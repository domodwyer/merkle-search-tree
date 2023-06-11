use crate::{
    digest::{KeyDigest, ValueDigest},
    page::Page,
    visitor::Visitor,
};

/// Storage of a single key/value pair.
///
/// Keys are stored immutably in the [`Node`], alongside the hash of a value
/// (and not the value itself).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Node<const N: usize> {
    key_hash: KeyDigest<N>,
    value_hash: ValueDigest<N>,

    /// A pointer to a page with a strictly lower tree level, and containing
    /// strictly smaller/less-than keys when compared to "key".
    lt_pointer: Option<Box<Page<N>>>,
}

impl<const N: usize> Node<N> {
    pub(crate) const fn new(
        key: KeyDigest<N>,
        value: ValueDigest<N>,
        lt_pointer: Option<Box<Page<N>>>,
    ) -> Self {
        Self {
            key_hash: key,
            value_hash: value,
            lt_pointer,
        }
    }

    pub(crate) fn depth_first<T>(&self, visitor: &mut T) -> bool
    where
        T: Visitor<N>,
    {
        if !visitor.pre_visit_node(self) {
            return false;
        }

        if let Some(p) = &self.lt_pointer {
            if !p.pre_order_traversal(visitor, false) {
                return false;
            }
        }

        if !visitor.visit_node(self) {
            return false;
        }

        if !visitor.post_visit_node(self) {
            return false;
        }

        true
    }

    /// Return the hash of the key for this node.
    pub fn key_hash(&self) -> &KeyDigest<N> {
        &self.key_hash
    }

    /// Return the hash of the value for this node.
    pub fn value_hash(&self) -> &ValueDigest<N> {
        &self.value_hash
    }

    pub(crate) fn update_hash(&mut self, hash: ValueDigest<N>) {
        self.value_hash = hash;
    }

    pub(crate) fn lt_pointer_mut(&mut self) -> &mut Option<Box<Page<N>>> {
        &mut self.lt_pointer
    }
}
