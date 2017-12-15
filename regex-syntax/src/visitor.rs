
use std::marker::Sized;

use Expr::*;
use {
    Expr, Repeater, CharClass, ClassRange, ByteClass, ByteRange
};

/// A `SyntaxVisitor` can be used to perform analysis and transformations
/// on an `Expr`.
pub trait SyntaxVisitor: Sized {
    fn visit_expr(&self, expr: &Expr) {
        expr.visit_children(self)
    }

    fn visit_repeater(&self, repeater: &Repeater) {
        repeater.visit_children(self)
    }

    fn visit_char_class(&self, char_class: &CharClass) {
        char_class.visit_children(self)
    }

    fn visit_class_range(&self, class_range: &ClassRange) {
        class_range.visit_children(self)
    }

    fn visit_byte_class(&self, byte_class: &ByteClass) {
        byte_class.visit_children(self)
    }

    fn visit_byte_range(&self, class_range: &ByteRange) {
        class_range.visit_children(self)
    }

    //
    // Mutable methods
    //

    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        expr.visit_children_mut(self)
    }

    fn visit_repeater_mut(&mut self, repeater: &mut Repeater) {
        repeater.visit_children_mut(self)
    }

    fn visit_char_class_mut(&mut self, char_class: &mut CharClass) {
        char_class.visit_children_mut(self)
    }

    fn visit_class_range_mut(&mut self, class_range: &mut ClassRange) {
        class_range.visit_children_mut(self)
    }

    fn visit_byte_class_mut(&mut self, byte_class: &mut ByteClass) {
        byte_class.visit_children_mut(self)
    }

    fn visit_byte_range_mut(&mut self, class_range: &mut ByteRange) {
        class_range.visit_children_mut(self)
    }
}

/// A type which can be visited by a `SyntaxVisitor`.
pub trait SyntaxVisitable {
    /// Just visit the current node with the right visit method of
    /// the given visitor.
    ///
    /// This method is not strictly required for the visitor
    /// mechanics to work, but it is a nice convenience method.
    fn visit_node<V>(&self, visitor: &V)
        where V: SyntaxVisitor;

    /// Recursively visit each of the `SyntaxVisitable` nodes
    /// which are direct children of the current node.
    fn visit_children<V>(&self, visitor: &V)
        where V: SyntaxVisitor;

    //
    // Mutable methods
    //

    /// Just visit the current node with the right visit method of
    /// the given visitor.
    ///
    /// This method is not strictly required for the visitor
    /// mechanics to work, but it is a nice convenience method.
    fn visit_node_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor;

    /// Recursively visit each of the `SyntaxVisitable` nodes
    /// which are direct children of the current node.
    fn visit_children_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor;
}

impl SyntaxVisitable for Expr {
    fn visit_node<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        visitor.visit_expr(self)
    }

    fn visit_children<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        match self {
            &Class(ref cc) => visitor.visit_char_class(cc),
            &ClassBytes(ref bc) => visitor.visit_byte_class(bc),
            &Group { ref e, i: _, name: _ } =>
                visitor.visit_expr(&*e),
            &Repeat { ref e, ref r, greedy: _ } => {
                visitor.visit_expr(e);
                visitor.visit_repeater(r);
            }
            &Concat(ref es) => {
                for e in es {
                    visitor.visit_expr(e);
                }
            }
            &Alternate(ref es) => {
                for e in es {
                    visitor.visit_expr(e);
                }
            }
            // nothing else contains a SyntaxVisitable element
            _ => ()
        }
    }

    fn visit_node_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        visitor.visit_expr_mut(self)
    }

    fn visit_children_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        match self {
            &mut Class(ref mut cc) => visitor.visit_char_class_mut(cc),
            &mut ClassBytes(ref mut bc) => visitor.visit_byte_class_mut(bc),
            &mut Group { ref mut e, i: _, name: _ } =>
                visitor.visit_expr_mut(&mut *e),
            &mut Repeat { ref mut e, ref mut r, greedy: _ } => {
                visitor.visit_expr_mut(e);
                visitor.visit_repeater_mut(r);
            }
            &mut Concat(ref mut es) => {
                for e in es {
                    visitor.visit_expr_mut(e);
                }
            }
            &mut Alternate(ref mut es) => {
                for e in es {
                    visitor.visit_expr_mut(e);
                }
            }
            // nothing else contains a SyntaxVisitable element
            _ => ()
        }
    }
}

impl SyntaxVisitable for Repeater {
    fn visit_node<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        visitor.visit_repeater(self)
    }

    fn visit_children<V>(&self, _visitor: &V)
        where V: SyntaxVisitor
    {
        // no-op
    }



    fn visit_node_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        visitor.visit_repeater_mut(self)
    }

    fn visit_children_mut<V>(&mut self, _visitor: &mut V)
        where V: SyntaxVisitor
    {
        // no-op
    }
}

impl SyntaxVisitable for CharClass {
    fn visit_node<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        visitor.visit_char_class(self)
    }

    fn visit_children<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        for cr in &self.ranges {
            visitor.visit_class_range(cr);
        }
    }


    fn visit_node_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        visitor.visit_char_class_mut(self)
    }

    fn visit_children_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        for cr in &mut self.ranges {
            visitor.visit_class_range_mut(cr);
        }
    }
}

impl SyntaxVisitable for ClassRange {
    fn visit_node<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        visitor.visit_class_range(self)
    }

    fn visit_children<V>(&self, _visitor: &V)
        where V: SyntaxVisitor
    {
        // no-op
    }



    fn visit_node_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        visitor.visit_class_range_mut(self)
    }

    fn visit_children_mut<V>(&mut self, _visitor: &mut V)
        where V: SyntaxVisitor
    {
        // no-op
    }
}

impl SyntaxVisitable for ByteClass {
    fn visit_node<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        visitor.visit_byte_class(self)
    }

    fn visit_children<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        for br in &self.ranges {
            visitor.visit_byte_range(br);
        }
    }


    fn visit_node_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        visitor.visit_byte_class_mut(self)
    }

    fn visit_children_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        for br in &mut self.ranges {
            visitor.visit_byte_range_mut(br);
        }
    }
}

impl SyntaxVisitable for ByteRange {
    fn visit_node<V>(&self, visitor: &V)
        where V: SyntaxVisitor
    {
        visitor.visit_byte_range(self)
    }

    fn visit_children<V>(&self, _visitor: &V)
        where V: SyntaxVisitor
    {
        // no-op
    }
    

    fn visit_node_mut<V>(&mut self, visitor: &mut V)
        where V: SyntaxVisitor
    {
        visitor.visit_byte_range_mut(self)
    }

    fn visit_children_mut<V>(&mut self, _visitor: &mut V)
        where V: SyntaxVisitor
    {
        // no-op
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn e(re: &str) -> Expr { Expr::parse(re).unwrap() }
    
    struct IdVisitor {}
    impl SyntaxVisitor for IdVisitor {}

    #[test]
    fn visit_smoke_test() {
        let mut expr = e(r"some(regex).*(:?abc|xyz)\w");
        let mut idv = IdVisitor {};
        let expr_snapshot = expr.clone();
        expr.visit_node_mut(&mut idv);
        assert_eq!(expr_snapshot, expr);
    }
}
