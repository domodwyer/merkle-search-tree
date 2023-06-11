use crate::{node::Node, page::Page};

/// An observer of [`Page`] and the [`Node`] instances within them during tree
/// traversal.
pub trait Visitor<const N: usize> {
    /// Called before a a call to [`Visitor::visit_node()`] with the same
    /// [`Node`].
    ///
    /// By default this is a no-op unless implemented.
    fn pre_visit_node(&mut self, node: &Node<N>) -> bool {
        let _ = node;
        true
    }

    /// Visit the given [`Node`].
    fn visit_node(&mut self, node: &Node<N>) -> bool;

    /// Called after [`Visitor::visit_node()`] with the same [`Node`].
    ///
    /// By default this is a no-op unless implemented.
    fn post_visit_node(&mut self, node: &Node<N>) -> bool {
        let _ = node;
        true
    }

    /// Visit the given [`Page`], which was referenced via a high-page link if
    /// `high_page` is true.
    ///
    /// By default this is a no-op unless implemented.
    fn visit_page(&mut self, page: &Page<N>, high_page: bool) -> bool {
        let _ = page;
        let _ = high_page;
        true
    }

    /// Called after [`Visitor::visit_page()`] with the same [`Page`].
    ///
    /// By default this is a no-op unless implemented.
    fn post_visit_page(&mut self, page: &Page<N>) -> bool {
        let _ = page;
        true
    }
}
