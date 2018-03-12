use syntax::hir::{
    Hir, HirKind, Literal, ClassUnicodeRange, Interval, IntervalSet,
    Class
};

/// Compute the first set of a given regular expression.
///
/// The first set of a regular expression is the set of all characters
/// which might begin it. This is a less general version of the
/// notion of a regular expression preview (the first set can be
/// thought of as the 1-preview of a regular expression).
pub fn fset_of(expr: &Hir) -> IntervalSet<ClassUnicodeRange> {
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
    use super::fset_of;

    fn is_intersecting_fset(e1: &Hir, e2: &Hir) -> bool {
        let mut fset = fset_of(e1);
        fset.intersect(&fset_of(e2));
        ! fset.is_empty()
    }

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
}
