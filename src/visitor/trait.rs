use crate::{node::Node, page::Page};

/// An observer of [`Page`] and the [`Node`] instances within them during tree
/// traversal.
pub trait Visitor<'a, const N: usize, K> {
    /// Called before a a call to [`Visitor::visit_node()`] with the same
    /// [`Node`].
    ///
    /// By default this is a no-op unless implemented.
    fn pre_visit_node(&mut self, node: &'a Node<N, K>) -> bool {
        let _ = node;
        true
    }

    /// Visit the given [`Node`].
    fn visit_node(&mut self, node: &'a Node<N, K>) -> bool;

    /// Called after [`Visitor::visit_node()`] with the same [`Node`].
    ///
    /// By default this is a no-op unless implemented.
    fn post_visit_node(&mut self, node: &'a Node<N, K>) -> bool {
        let _ = node;
        true
    }

    /// Visit the given [`Page`], which was referenced via a high-page link if
    /// `high_page` is true.
    ///
    /// By default this is a no-op unless implemented.
    fn visit_page(&mut self, page: &'a Page<N, K>, high_page: bool) -> bool {
        let _ = page;
        let _ = high_page;
        true
    }

    /// Called after [`Visitor::visit_page()`] with the same [`Page`].
    ///
    /// By default this is a no-op unless implemented.
    fn post_visit_page(&mut self, page: &'a Page<N, K>) -> bool {
        let _ = page;
        true
    }
}
