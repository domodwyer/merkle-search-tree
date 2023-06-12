use std::fmt::Debug;

use crate::{node::Node, page::Page};

use super::Visitor;

/// An internal visitor used to assert ordering invariants during depth-first
/// tree traversal.
///
/// Validates:
///
///   * Key traversal order (strictly increasing keys)
///   * Page levels (decrease when traversing down, increasing up)
///   * High pages are never empty
///
#[derive(Debug)]
pub(crate) struct InvariantAssertOrder<const N: usize, T, K> {
    inner: T,
    last: Option<K>,

    level_stack: Vec<u8>,
}

impl<const N: usize, T, K> InvariantAssertOrder<N, T, K> {
    /// Wrap `T` in this decorator.
    pub(crate) fn new(inner: T) -> Self {
        Self {
            inner,
            last: None,
            level_stack: Default::default(),
        }
    }

    /// Unwrap this decorator, yielding the underlying `T`.
    pub(crate) fn into_inner(self) -> T {
        self.inner
    }
}

impl<const N: usize, T, K> Visitor<N, K> for InvariantAssertOrder<N, T, K>
where
    K: PartialOrd + Debug + Clone,
    T: Visitor<N, K>,
{
    fn pre_visit_node(&mut self, node: &Node<N, K>) -> bool {
        self.inner.pre_visit_node(node)
    }

    fn visit_node(&mut self, node: &Node<N, K>) -> bool {
        if let Some(v) = &self.last {
            assert!(
                v < node.key(),
                "visited key {:?} before key {:?}",
                v,
                node.key()
            )
        }

        self.last = Some(node.key().clone());

        self.inner.visit_node(node)
    }

    fn post_visit_node(&mut self, node: &Node<N, K>) -> bool {
        self.inner.post_visit_node(node)
    }

    fn visit_page(&mut self, page: &Page<N, K>, high_page: bool) -> bool {
        // Page levels always increase as the visitor travels up the tree (for a
        // depth first search)
        assert!(self
            .level_stack
            .last()
            .map(|&v| v > page.level())
            .unwrap_or(true));

        // High pages are never empty (but normal pages can be, because of the
        // root page).
        if high_page {
            assert!(!page.nodes().is_empty());
        }

        self.level_stack.push(page.level());
        self.inner.visit_page(page, high_page)
    }

    fn post_visit_page(&mut self, page: &Page<N, K>) -> bool {
        self.level_stack.pop();
        self.inner.post_visit_page(page)
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        assert_tree,
        digest::mock::{LevelKey, MockHasher},
        MerkleSearchTree,
    };

    #[test]
    fn test_preorder() {
        let mut t = MerkleSearchTree::new_with_hasher(MockHasher::default());

        t.upsert(&LevelKey::new("I", 2), &"bananas");
        t.upsert(&LevelKey::new("K", 2), &"bananas");
        t.upsert(&LevelKey::new("A", 1), &"bananas");
        t.upsert(&LevelKey::new("E", 1), &"bananas");
        t.upsert(&LevelKey::new("J", 1), &"bananas");
        t.upsert(&LevelKey::new("B", 0), &"bananas");
        t.upsert(&LevelKey::new("C", 0), &"bananas");
        t.upsert(&LevelKey::new("D", 0), &"bananas");
        t.upsert(&LevelKey::new("F", 0), &"bananas");
        t.upsert(&LevelKey::new("G", 0), &"bananas");
        t.upsert(&LevelKey::new("H", 0), &"bananas");

        assert_tree!(t);
    }
}
