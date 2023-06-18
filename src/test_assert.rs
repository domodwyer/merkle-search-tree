//! A helper macro to validate the structure of a tree, and snapshot a DOT
//! representation.

/// Assert the ordering invariants of a tree, and validating the structure
/// against a DOT-formatted snapshot.
#[macro_export]
macro_rules! assert_tree {
    // Validate a page, not a tree.
    (page = $page:expr) => {{
        let page = $page;

        let v = $crate::visitor::dot::DotVisitor::default();
        let mut v = $crate::visitor::assert_order::InvariantAssertOrder::new(v);
        page.pre_order_traversal(&mut v, false);

        insta::assert_snapshot!(v.into_inner().finalise());
    }};
    // Validate a tree.
    ($tree:expr) => {{
        let tree = $tree;

        let mut v = $crate::visitor::dot::DotVisitor::default();
        tree.pre_order_traversal(&mut v);
        let dot = v.finalise();
        println!("{}", dot.clone());

        let mut v = $crate::visitor::assert_order::InvariantAssertOrder::new(
            $crate::visitor::nop::NopVisitor,
        );
        tree.pre_order_traversal(&mut v);

        insta::assert_snapshot!(dot);
    }};
}
