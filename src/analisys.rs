use syntax::hir::{
    Hir, HirKind, Literal, ClassBytes, ClassBytesRange,
    Class, Visitor
};
use syntax::hir;
use utf8_ranges::Utf8Sequences;

/// True if the given expression is one-pass
pub fn is_one_pass(expr: &Hir) -> bool {
    struct IsOnePassVisitor(bool);
    impl Visitor for IsOnePassVisitor {
        type Output = bool;
        type Err = ();

        fn finish(self) -> Result<bool, ()> {
            Ok(self.0)
        }

        fn visit_pre(&mut self, hir: &Hir) -> Result<(), ()> {
            match hir.kind() {
                &HirKind::Concat(ref es) => self.check_concat(&es),
                &HirKind::Alternation(ref es) => self.check_alternation(&es),
                &HirKind::Repetition(ref rep) => {
                    if fset_of(&*rep.hir).is_empty() {
                        self.0 = false;
                    }

                    // If a repetition starts with an emptylook,
                    // the onepass DFA struggles with it because
                    // it does no know how to check a zero width
                    // assertion right before a transition.
                    //
                    // /(?m)(?:^a)+/ on "aaa\naaa\naaa"
                    //
                    // should demonstrate the problem. It does
                    // not seem impossible to lift this restriction
                    // on the face of it, but I struggled to come
                    // up with a clean solution.
                    if starts_with_emptylook(&*rep.hir) {
                        self.0 = false;
                    }
                }
                &HirKind::Class(ref cls) => self.check_cls(cls),
                _ => ()
            }

            Ok(())
        }
    }
    impl IsOnePassVisitor {
        fn new() -> Self {
            IsOnePassVisitor(true)
        }

        fn check_concat(&mut self, es: &[Hir]) {
            let mut rep_inners = vec![];
            for e in es {
                let e_rep_inners = IsOnePassVisitor::rep_inners_of(e);
                if e_rep_inners.len() > 0 {
                    // There are some inner expressions of a repetition
                    // to accumulate. e is of the form /e*/ or /e+/ or
                    // something.
                    rep_inners.extend(e_rep_inners);
                } else {
                    // We just reached the end of a list of repetitions.
                    rep_inners.push(e);
                    self.0 = self.0 && !fsets_clash(&rep_inners);
                    rep_inners.clear();
                }
            }

            // TODO: test to make sure we do the right thing for
            //       cases like (a|)a (not onepass)

            if rep_inners.len() > 0 {
                self.0 = self.0 && !fsets_clash(&rep_inners);
            }
        }

        fn rep_inners_of<'a>(e: &'a Hir) -> Vec<&Hir> {
            match e.kind() {
                &HirKind::Repetition(ref rep) => vec![&*rep.hir],
                &HirKind::Group(ref group) =>
                    IsOnePassVisitor::rep_inners_of(&*group.hir),

                // If all of the expressions are repetitions, we
                // need to return the inners, otherwise this concat
                // will be handled by a different visitor visit.
                //
                // Technically this is overly conservative.
                &HirKind::Concat(ref es) =>
                    es.iter()
                        .map(IsOnePassVisitor::rep_inners_of)
                        .fold(vec![], |mut v, s| { v.extend(s); v }),

                _ => vec![],
            }
        }

        fn check_alternation(&mut self, es: &[Hir]) {
            self.0 = self.0 && !fsets_clash(&es.iter().collect::<Vec<_>>());
        }

        // Unicode classes are really big alternatives from the byte
        // oriented point of view.
        //
        // This is function translates a unicode class into the 
        // byte space and checks for intersecting first sets.
        fn check_cls(&mut self, cls: &Class) {
            match cls {
                &Class::Unicode(ref ucls) => {
                    let mut seen_char: [bool; 256] = [false; 256];

                    for cr in ucls.iter() {
                        for br in Utf8Sequences::new(cr.start(), cr.end()) {
                            let first = br.as_slice()[0];
                            for b in first.start..(first.end+1) {
                                if seen_char[b as usize] {
                                    self.0 = false;
                                    return;
                                }
                                seen_char[b as usize] = true;
                            }
                        }
                    }
                }
                _ => {} // FALLTHROUGH
            }
        }
    }

    // check if a list of first sets is incompatable.
    fn fsets_clash(es: &[&Hir]) -> bool {
        for (i, e1) in es.iter().enumerate() {
            for (j, e2) in es.iter().enumerate() {
                if i != j {
                    let mut fset = fset_of(e1);
                    let fset2 = fset_of(e2);

                    // For the regex /a|()+/, we don't have a way to
                    // differentiate the branches, so we are not onepass.
                    //
                    // We might be able to loosen this restriction by
                    // considering the expression after the alternative
                    // if there is one.
                    if fset.is_empty() || fset2.is_empty() {
                        return true;
                    }

                    fset.intersect(&fset2);
                    if ! fset.is_empty() {
                        return true;
                    }
                }
            }
        }
        false
    }

    hir::visit(expr, IsOnePassVisitor::new()).unwrap()
}

fn starts_with_emptylook(expr: &Hir) -> bool {
    match expr.kind() {
        &HirKind::Anchor(_) | &HirKind::WordBoundary(_) => true,
        &HirKind::Group(ref e) => starts_with_emptylook(&e.hir),
        &HirKind::Repetition(ref rep) => starts_with_emptylook(&*rep.hir),
        &HirKind::Alternation(ref es) =>
            es.iter().any(|e| starts_with_emptylook(e)),
        &HirKind::Concat(ref es) => {
            for e in es {
                match e.kind() {
                    &HirKind::Anchor(_) | &HirKind::WordBoundary(_) =>
                        return true,
                    &HirKind::Repetition(ref rep) => {
                        if starts_with_emptylook(&*rep.hir) {
                            return true;
                        }
                    }
                    // This is the (n+1)th expression
                    _ => {
                        return starts_with_emptylook(&e);
                    }
                }
            }

            return false;
        }
        _ => return false,
    }
}

/// Compute the first set of a given regular expression.
///
/// The first set of a regular expression is the set of all characters
/// which might begin it. This is a less general version of the
/// notion of a regular expression preview (the first set can be
/// thought of as the 1-preview of a regular expression).
///
/// Note that first sets are byte-oriented because the DFA is
/// byte oriented. This means an expression like /Δ|δ/ is actually not
/// one-pass, even though there is clearly no non-determinism inherent
/// to the regex at a unicode code point level (big delta and little
/// delta start with the same byte).
fn fset_of(expr: &Hir) -> ClassBytes {
    fn singleton(b: u8) -> ClassBytes {
        let mut c = ClassBytes::empty();
        c.push(ClassBytesRange::new(b, b));
        c
    }

    fn anychar() -> ClassBytes {
        let mut c = ClassBytes::empty();
        c.push(ClassBytesRange::new(b'\0', b'\xFF'));
        c
    }

    match expr.kind() {
        &HirKind::Empty => ClassBytes::empty(),
        &HirKind::Literal(ref lit) => {
            match lit {
                &Literal::Unicode(c) => singleton(first_byte(c)),
                &Literal::Byte(b) => singleton(b),
            }
        }
        &HirKind::Class(ref class) => {
            match class {
                &Class::Unicode(ref c) => {
                    // Get all the bytes which might begin this unicode
                    // class.
                    let mut cb = ClassBytes::empty();
                    for cr in c.iter() {
                        for br in Utf8Sequences::new(cr.start(), cr.end()) {
                            let first = br.as_slice()[0];
                            cb.push(ClassBytesRange::new(first.start, first.end));
                        }
                    }
                    cb
                }
                &Class::Bytes(ref b) => ClassBytes::new(b.iter().map(|x| *x)),
            }
        }

        // When an empty look (Anchor or WordBoundary) is at the start of
        // a concatenation, we conservatively assume that the assertion
        // will pass, so we just drop it. Then we can only get to this
        // point if we are dealing with some sort of naked empty look.
        // For now we just do the most conservative thing and say
        // that such an emptylook could potentially match on any character.
        &HirKind::Anchor(_) | &HirKind::WordBoundary(_) => anychar(),

        &HirKind::Repetition(ref rep) => fset_of(&*rep.hir),
        &HirKind::Group(ref group) => fset_of(&group.hir),

        // The most involved case. We need to strip leading empty-looks
        // as well as take the union of the first sets of the first n+1
        // expressions where n is the number of leading repetitions.
        &HirKind::Concat(ref es) => {
            let mut fset = ClassBytes::empty();
            for e in es {
                match e.kind() {
                    &HirKind::Anchor(_) | &HirKind::WordBoundary(_) => (),
                    &HirKind::Repetition(ref rep) => {
                        fset.union(&fset_of(&*rep.hir));
                    }
                    // This is the (n+1)th expression
                    _ => {
                        fset.union(&fset_of(e));
                        break;
                    }
                }
            }
            fset
        }
        &HirKind::Alternation(ref es) => {
            let mut fset = ClassBytes::empty();
            for e in es {
                fset.union(&fset_of(e));
            }
            fset
        }
    }
}

fn first_byte(c: char) -> u8 {
    let mut b: [u8; 4] = [0; 4];
    c.encode_utf8(&mut b);
    b[0]
}

#[cfg(test)]
mod tests {
    use syntax::Parser;
    use syntax::hir::Hir;
    use super::{fset_of, is_one_pass};

    fn is_intersecting_fset(e1: &Hir, e2: &Hir) -> bool {
        let mut fset = fset_of(e1);
        fset.intersect(&fset_of(e2));
        ! fset.is_empty()
    }

    //
    // First set intersection smoke tests
    //

    #[test]
    fn fset_lit() {
        let e1 = Parser::new().parse("a").unwrap();
        let e2 = Parser::new().parse("a").unwrap();
        let e3 = Parser::new().parse("b").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_class() {
        let e1 = Parser::new().parse("[a]").unwrap();
        let e2 = Parser::new().parse("[a]").unwrap();
        let e3 = Parser::new().parse("[b]").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_class_n() {
        let e1 = Parser::new().parse("[xamn]").unwrap();
        let e2 = Parser::new().parse("[rlwa]").unwrap();
        let e3 = Parser::new().parse("[bcq]").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_alt() {
        let e1 = Parser::new().parse("ab|bc|ad").unwrap();
        let e2 = Parser::new().parse("yyyy|am|zz").unwrap();
        let e3 = Parser::new().parse("cc|ww").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_group() {
        let e1 = Parser::new().parse("(?:ab)").unwrap();
        let e2 = Parser::new().parse("(?:aq)").unwrap();
        let e3 = Parser::new().parse("(?:m)").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_concat() {
        let e1 = Parser::new().parse("aa(?:nb)").unwrap();
        let e2 = Parser::new().parse("aa(?:rq)").unwrap();
        let e3 = Parser::new().parse("bb(?:m)").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_word_boundary_dropped() {
        let e1 = Parser::new().parse(r"aa").unwrap();
        let e2 = Parser::new().parse(r"\baa").unwrap();
        let e3 = Parser::new().parse(r"\bbb").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_word_boundary_all() {
        let e1 = Parser::new().parse(r"aa").unwrap();
        let e2 = Parser::new().parse(r"\b").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
    }

    #[test]
    fn fset_not_word_boundary_dropped() {
        let e1 = Parser::new().parse(r"aa").unwrap();
        let e2 = Parser::new().parse(r"\Baa").unwrap();
        let e3 = Parser::new().parse(r"\Bbb").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    #[test]
    fn fset_not_word_boundary_all() {
        let e1 = Parser::new().parse(r"aa").unwrap();
        let e2 = Parser::new().parse(r"\B").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
    }

    #[test]
    fn fset_start_anchor_dropped() {
        let e1 = Parser::new().parse(r"aa").unwrap();
        let e2 = Parser::new().parse(r"^aa").unwrap();
        let e3 = Parser::new().parse(r"^bb").unwrap();

        assert!(is_intersecting_fset(&e1, &e2));
        assert!(!is_intersecting_fset(&e1, &e3));
    }

    //
    // One pass tests
    //

    #[test]
    fn is_one_pass_smoke_test1() {
        let e1 = Parser::new().parse(r"([^x]*)x(.*)").unwrap();
        let e2 = Parser::new().parse(r"(.*)x(.*)").unwrap();

        assert!(is_one_pass(&e1));
        assert!(! is_one_pass(&e2));
    }

    //
    // Note that Russ Cox's other example of a onepass regex
    // (r"(\d+)-(\d+)") is actually not onepass for us because
    // there is byte-level nondeterminism in the \d charicter
    // class, and we care about things in the byte space rather
    // than the charicter space. If you do a onepass engine at
    // the charicter level this should not be an issue.
    //
}
