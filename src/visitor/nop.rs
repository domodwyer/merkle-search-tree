use crate::{node::Node, page::Page};

use super::Visitor;

/// A no-op [`Visitor`] implementation - it does nothing!
#[derive(Debug, Default)]
pub(crate) struct NopVisitor;

impl<'a, const N: usize, K> Visitor<'a, N, K> for NopVisitor {
    fn post_visit_node(&mut self, _node: &'a Node<N, K>) -> bool {
        true
    }

    fn visit_page(&mut self, _page: &'a Page<N, K>, _high_page: bool) -> bool {
        true
    }

    fn post_visit_page(&mut self, _page: &'a Page<N, K>) -> bool {
        true
    }

    fn pre_visit_node(&mut self, _node: &'a Node<N, K>) -> bool {
        true
    }

    fn visit_node(&mut self, _node: &'a Node<N, K>) -> bool {
        true
    }
}
