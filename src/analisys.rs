use syntax::hir::{
    Hir, HirKind, Literal, ClassUnicodeRange, Interval, IntervalSet,
    Class, Visitor
};
use syntax::hir;

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
                    rep_inners.extend(e_rep_inners);
                } else {
                    rep_inners.push(e);
                    self.0 = self.0 && !fsets_intersect(&rep_inners);
                    rep_inners.clear();
                }
            }

            if rep_inners.len() > 0 {
                self.0 = self.0 && !fsets_intersect(&rep_inners);
            }
        }

        fn rep_inners_of<'a>(e: &'a Hir) -> Vec<&Hir> {
            match e.kind() {
                &HirKind::Repetition(ref rep) => vec![&*rep.hir],
                &HirKind::Group(ref group) =>
                    IsOnePassVisitor::rep_inners_of(&*group.hir),

                // If all of the expressions are repetitions, we
                // need to return the inners, otherwise this concat
                // will be handed by a different visitor visit.
                &HirKind::Concat(ref es) =>
                    es.iter()
                        .map(IsOnePassVisitor::rep_inners_of)
                        .fold(vec![], |mut v, s| { v.extend(s); v }),

                _ => vec![],
            }
        }

        fn check_alternation(&mut self, es: &[Hir]) {
            self.0 = self.0 && !fsets_intersect(&es.iter().collect::<Vec<_>>());
        }
    }

    fn fsets_intersect(es: &[&Hir]) -> bool {
        for (i, e1) in es.iter().enumerate() {
            for (j, e2) in es.iter().enumerate() {
                if i != j {
                    let mut fset = fset_of(e1);
                    let fset2 = fset_of(e2);

                    // For the regex /a|()+/, we don't have a way to
                    // differentiate the branches, so we are not onepass.
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

/// Compute the first set of a given regular expression.
///
/// The first set of a regular expression is the set of all characters
/// which might begin it. This is a less general version of the
/// notion of a regular expression preview (the first set can be
/// thought of as the 1-preview of a regular expression).
fn fset_of(expr: &Hir) -> IntervalSet<ClassUnicodeRange> {
    fn singleton(c: char) -> IntervalSet<ClassUnicodeRange> {
        IntervalSet::singleton(ClassUnicodeRange::create(c, c))
    }

    fn anychar() -> IntervalSet<ClassUnicodeRange> {
        IntervalSet::singleton(ClassUnicodeRange::new('\0', '\u{10FFFF}'))
    }

    match expr.kind() {
        &HirKind::Empty => IntervalSet::new(vec![]),
        &HirKind::Literal(ref lit) => {
            match lit {
                &Literal::Unicode(c) => singleton(c),
                &Literal::Byte(b) => singleton(b as char),
            }
        }
        &HirKind::Class(ref class) => {
            match class {
                &Class::Unicode(ref c) => IntervalSet::new(c.iter().map(|x| *x)),
                &Class::Bytes(ref b) =>
                    IntervalSet::new(
                        b.iter().map(|br|
                            ClassUnicodeRange::create(
                                br.lower() as char, br.upper() as char))),
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
            let mut fset = IntervalSet::new(vec![]);
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
            let mut fset = IntervalSet::new(vec![]);
            for e in es {
                fset.union(&fset_of(e));
            }
            fset
        }
    }
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
    // First set intersection tests
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

    #[test]
    fn is_one_pass_smoke_test2() {
        let e1 = Parser::new().parse(r"(\d+)-(\d+)").unwrap();
        let e2 = Parser::new().parse(r"(\d+).(\d+)").unwrap();

        assert!(is_one_pass(&e1));
        assert!(! is_one_pass(&e2));
    }
}
