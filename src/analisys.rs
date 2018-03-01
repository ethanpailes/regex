
extern crate char_iter;

use syntax::{Expr};
use std::ascii::AsciiExt;

// Flip to true for debugging
const TRACE: bool = false;
macro_rules! trace {
    ($($tts:tt)*) => {
        if TRACE {
            println!($($tts)*);
        }
    }
}

/// Determines if a set of regular expressions have any intersecting
/// first sets between them.
pub fn branches_have_inter_fsets(branches: &[&Expr]) -> bool {
    for (i, e1) in branches.iter().enumerate() {
        for (j, e2) in branches.iter().enumerate() {
            if i != j && inter_fset(e1, e2) {
                return true;
            }
        }
    }

    false
}

// This macro is to be used when rhs is a terminal expression.
// If lhs is a terminal expression it will determine intersection.
// If not, it flips the operands in order to drill down on the
// terminal expression for the lhs.
macro_rules! term_intersects {
    ($lhs:expr, $rhs:expr, $c:expr, $casei:expr) => {
        match terminal_intersecting_char($lhs, $c, $casei) {
            Some(res) => res,
            None => inter_fset($rhs, $lhs),
        }
    }
}

/// Determines if the two regular expressions have an intersecting
/// first set.
pub fn inter_fset(lhs: &Expr, rhs: &Expr) -> bool {
    trace!("inter_fset: lhs={:?} rhs={:?}", lhs, rhs);

    match rhs {
        // base cases
        &Expr::Empty => false,
        &Expr::Literal { ref chars, casei } =>
            term_intersects!(lhs, rhs, chars[0], casei),
        &Expr::LiteralBytes { ref bytes, casei } =>
            term_intersects!(lhs, rhs, char::from(bytes[0]), casei),
        &Expr::AnyChar => *lhs != Expr::Empty,
        &Expr::AnyCharNoNL =>
            *lhs != Expr::Empty && term_intersects!(lhs, rhs, '\n', false),
        &Expr::AnyByte => *lhs != Expr::Empty,
        &Expr::AnyByteNoNL =>
            *lhs != Expr::Empty && term_intersects!(lhs, rhs, '\n', false),
        &Expr::Class(ref class) =>
            class.iter().any(|cr|
                char_iter::new(cr.start, cr.end).any(|c|
                    term_intersects!(lhs, rhs, c, false))),
        &Expr::ClassBytes(ref class) =>
            class.iter().any(|br|
                (br.start..br.end).any(|b|
                    term_intersects!(lhs, rhs, char::from(b), false))),


        // At the start of a concatination empty looks are dropped.
        //     - For {Start,End}{Line,Text} this is a conservative
        //        assumption that we could be starting the branch
        //        at any position. Really we could do better.
        //     - For (Not)WordBoundary(Ascii) this is a conservative
        //        assumption that the other branch didn't have any
        //        sort of assertion about the previous char.
        //
        // Naked empty looks are conservativly treated as anychar.
        // That is the case that we have to handle here.
        &Expr::StartLine => inter_fset(lhs, &Expr::AnyChar),
        &Expr::EndLine => inter_fset(lhs, &Expr::AnyChar),
        &Expr::StartText => inter_fset(lhs, &Expr::AnyChar),
        &Expr::EndText => inter_fset(lhs, &Expr::AnyChar),
        &Expr::WordBoundary => inter_fset(lhs, &Expr::AnyChar),
        &Expr::WordBoundaryAscii => inter_fset(lhs, &Expr::AnyChar),
        &Expr::NotWordBoundary => inter_fset(lhs, &Expr::AnyChar),
        &Expr::NotWordBoundaryAscii => inter_fset(lhs, &Expr::AnyChar),


        &Expr::Group { ref e, i: _, name: _ } =>
            inter_fset(lhs, &*e),
        &Expr::Concat(ref es) => {
            if es.len() > 1 && es[0].is_empty_look() {
                inter_fset(lhs, &es[1])
            } else {
                inter_fset(lhs, &es[0])
            }
        },
        &Expr::Repeat { ref e, r: _, greedy: _ }  =>
            inter_fset(lhs, &*e),
        &Expr::Alternate(ref es) =>
            es.iter().any(|e| inter_fset(lhs, e)),
    }
}

/// Determines if the expression is a terminal expression
/// (an expression that requires no further decomposition in
/// order to arrive at the first set). If it is, returns
/// a flag indicating if the given char matched.
fn terminal_intersecting_char(e: &Expr, c: char, casei: bool) -> Option<bool> {
    if casei {
        oor(terminal_its_char(e, AsciiExt::to_ascii_lowercase(&c)),
            terminal_its_char(e, AsciiExt::to_ascii_uppercase(&c)))
    } else {
        terminal_its_char(e, c)
    }
}

/// The main driver for `terminal_intersecting_char`
///
/// Some(true) if e is terminal and intersects with c
/// Some(false) if e is terminal and does not intersect with c
/// None if e is not terminal
fn terminal_its_char(e: &Expr, c: char) -> Option<bool> {
    let mut b = [0; 4];

    match e {
        &Expr::Literal { ref chars, casei } => {
            let intersects = if casei {
                AsciiExt::to_ascii_lowercase(&chars[0]) ==
                    AsciiExt::to_ascii_lowercase(&c)
            } else {
                chars[0] == c
            };

            Some(intersects)
        }
        &Expr::LiteralBytes { ref bytes, casei: _ } => {
            if c.encode_utf8(&mut b).len() == 1 {
                // TODO(ethan):casei
                Some(bytes[0] == b[0])
            } else {
                Some(false)
            }
        }
        &Expr::AnyChar => Some(true),
        &Expr::Empty => Some(false),
        &Expr::AnyCharNoNL => Some(c != '\n'),
        &Expr::AnyByte => Some(c.encode_utf8(&mut b).len() == 1),
        &Expr::AnyByteNoNL =>
            Some(c != '\n' && c.encode_utf8(&mut b).len() == 1),
        &Expr::Class(ref class) =>
            Some(class.iter().any(|cr| cr.start <= c && c <= cr.end)),
        &Expr::ClassBytes(ref class) => {
            if c.encode_utf8(&mut b).len() == 1 {
                Some(class.iter().any(|br| br.start <= b[0] && b[0] <= br.end))
            } else {
                Some(false)
            }
        }

        // Empty looks are treated as AnyChars here. See the comment
        // in inter_fset for why.
        &Expr::StartLine => Some(true),
        &Expr::EndLine => Some(true),
        &Expr::StartText => Some(true),
        &Expr::EndText => Some(true),
        &Expr::WordBoundary => Some(true),
        &Expr::WordBoundaryAscii => Some(true),
        &Expr::NotWordBoundary => Some(true),
        &Expr::NotWordBoundaryAscii => Some(true),

        // The rest require decomposition
        _ => None
    }
}

//
// Utils
//

fn oor(lhs: Option<bool>, rhs: Option<bool>) -> Option<bool> {
    lhs.and_then(|x| rhs.map(|y| x || y))
}

#[cfg(test)]
mod tests {
    use syntax::{ExprBuilder};
    use super::branches_have_inter_fsets;

    #[test]
    fn its_lit_1() {
        let e1 = ExprBuilder::new().parse("a").unwrap();
        let e2 = ExprBuilder::new().parse("a").unwrap();
        let e3 = ExprBuilder::new().parse("b").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_class_1() {
        let e1 = ExprBuilder::new().parse("[a]").unwrap();
        let e2 = ExprBuilder::new().parse("[a]").unwrap();
        let e3 = ExprBuilder::new().parse("[b]").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_class_n() {
        let e1 = ExprBuilder::new().parse("[xamn]").unwrap();
        let e2 = ExprBuilder::new().parse("[rlwa]").unwrap();
        let e3 = ExprBuilder::new().parse("[bcq]").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_alt() {
        let e1 = ExprBuilder::new().parse("ab|bc|ad").unwrap();
        let e2 = ExprBuilder::new().parse("yyyy|am|zz").unwrap();
        let e3 = ExprBuilder::new().parse("cc|ww").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_group() {
        let e1 = ExprBuilder::new().parse("(?:ab)").unwrap();
        let e2 = ExprBuilder::new().parse("(?:aq)").unwrap();
        let e3 = ExprBuilder::new().parse("(?:m)").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_concat() {
        let e1 = ExprBuilder::new().parse("aa(?:nb)").unwrap();
        let e2 = ExprBuilder::new().parse("aa(?:rq)").unwrap();
        let e3 = ExprBuilder::new().parse("bb(?:m)").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_word_boundary_dropped() {
        let e1 = ExprBuilder::new().parse(r"aa").unwrap();
        let e2 = ExprBuilder::new().parse(r"\baa").unwrap();
        let e3 = ExprBuilder::new().parse(r"\bbb").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_word_boundary_all() {
        let e1 = ExprBuilder::new().parse(r"aa").unwrap();
        let e2 = ExprBuilder::new().parse(r"\b").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
    }

    #[test]
    fn its_not_word_boundary_dropped() {
        let e1 = ExprBuilder::new().parse(r"aa").unwrap();
        let e2 = ExprBuilder::new().parse(r"\Baa").unwrap();
        let e3 = ExprBuilder::new().parse(r"\Bbb").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }

    #[test]
    fn its_not_word_boundary_all() {
        let e1 = ExprBuilder::new().parse(r"aa").unwrap();
        let e2 = ExprBuilder::new().parse(r"\B").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
    }

    #[test]
    fn its_start_anchor_dropped() {
        let e1 = ExprBuilder::new().parse(r"aa").unwrap();
        let e2 = ExprBuilder::new().parse(r"^aa").unwrap();
        let e3 = ExprBuilder::new().parse(r"^bb").unwrap();

        assert!(branches_have_inter_fsets(&[&e1, &e2]));
        assert!(!branches_have_inter_fsets(&[&e1, &e3]));
    }
}
