use super::Visitor;
use crate::{node::Node, page::Page};

/// Internal visitor used to count and assert the number of key/value pairs in a
/// tree during traversal.
#[derive(Debug)]
pub(crate) struct InvariantAssertCount<T> {
    inner: T,
    count: usize,
}

impl<T> InvariantAssertCount<T> {
    /// Wrap `T` in this decorator.
    pub(crate) fn new(inner: T) -> Self {
        Self { inner, count: 0 }
    }

    /// Remove this decorator, asserting it has observed exactly `expect` number
    /// of key/value pairs.
    ///
    /// # Panics
    ///
    /// Panics if `expect` does not match the observed key/value count.
    pub(crate) fn unwrap_count(self, expect: usize) -> T {
        let got = self.count;
        assert_eq!(got, expect, "got {got}, want {expect}");
        self.inner
    }
}

impl<'a, const N: usize, T, K> Visitor<'a, N, K> for InvariantAssertCount<T>
where
    T: Visitor<'a, N, K>,
{
    #[track_caller]
    fn visit_node(&mut self, node: &'a Node<N, K>) -> bool {
        self.count += 1;
        self.inner.visit_node(node)
    }

    fn pre_visit_node(&mut self, node: &'a Node<N, K>) -> bool {
        self.inner.pre_visit_node(node)
    }

    fn post_visit_node(&mut self, node: &'a Node<N, K>) -> bool {
        self.inner.post_visit_node(node)
    }

    fn visit_page(&mut self, page: &'a Page<N, K>, high_page: bool) -> bool {
        self.inner.visit_page(page, high_page)
    }

    fn post_visit_page(&mut self, page: &'a Page<N, K>) -> bool {
        self.inner.post_visit_page(page)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{visitor::nop::NopVisitor, MerkleSearchTree};

    #[test]
    fn test_count() {
        let mut t = MerkleSearchTree::default();

        t.upsert("I", &"bananas");
        t.upsert("K", &"bananas");
        t.upsert("A", &"bananas");
        t.upsert("E", &"bananas");
        t.upsert("J", &"bananas");
        t.upsert("B", &"bananas");
        t.upsert("C", &"bananas");
        t.upsert("D", &"bananas");
        t.upsert("F", &"bananas");
        t.upsert("G", &"bananas");
        t.upsert("H", &"bananas");

        let mut counter = InvariantAssertCount::new(NopVisitor::default());
        t.in_order_traversal(&mut counter);

        counter.unwrap_count(11);
    }
}
