use crate::{node::Node, page::Page};

use super::Visitor;

/// A no-op [`Visitor`] implementation - it does nothing!
#[derive(Debug, Default)]
pub(crate) struct NopVisitor;

impl<const N: usize> Visitor<N> for NopVisitor {
    fn post_visit_node(&mut self, _node: &Node<N>) -> bool {
        true
    }

    fn visit_page(&mut self, _page: &Page<N>, _high_page: bool) -> bool {
        true
    }

    fn post_visit_page(&mut self, _page: &Page<N>) -> bool {
        true
    }

    fn pre_visit_node(&mut self, _node: &Node<N>) -> bool {
        true
    }

    fn visit_node(&mut self, _node: &Node<N>) -> bool {
        true
    }
}
