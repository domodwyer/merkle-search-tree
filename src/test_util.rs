use std::{collections::BTreeMap, fmt::Display, ops::RangeInclusive};

use crate::{diff::PageRange, MerkleSearchTree};

/// An wrapper over integers, implementing `AsRef<[u8]>` with deterministic
/// output across platforms with differing endian-ness.
#[derive(PartialOrd, Ord, PartialEq, Eq, Clone, Hash)]
pub struct IntKey(u64, [u8; 8]);

impl std::fmt::Debug for IntKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("IntKey").field(&self.0).finish()
    }
}
impl IntKey {
    pub fn new(v: u64) -> Self {
        Self(v, v.to_be_bytes())
    }
    pub fn unwrap(&self) -> u64 {
        self.0
    }
}
impl AsRef<[u8]> for IntKey {
    fn as_ref(&self) -> &[u8] {
        &self.1
    }
}
impl Display for IntKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.0, f)
    }
}

/// A mock peer, storing `(key, value)` tuples and maintaining a
/// [`MerkleSearchTree`] of the store contents.
#[derive(Default, Clone)]
pub struct Node(BTreeMap<IntKey, u64>, MerkleSearchTree<IntKey, u64>);

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        // Invariant: root hash hash equality must match the control btree
        // equality.
        if let Some((a, b)) = self.1.root_hash_cached().zip(other.1.root_hash_cached()) {
            assert_eq!((self.0 == other.0), (a == b));
        }
        self.0 == other.0
    }
}

impl std::ops::DerefMut for Node {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.1
    }
}

impl std::ops::Deref for Node {
    type Target = MerkleSearchTree<IntKey, u64>;

    fn deref(&self) -> &Self::Target {
        &self.1
    }
}

impl std::fmt::Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut w = f.debug_map();
        for (k, v) in &self.0 {
            w.entry(&k.unwrap(), &v);
        }
        w.finish()
    }
}

impl Node {
    /// Store the given `key` & `value` in the node, replacing the previous
    /// value of `key`, if any.
    pub fn upsert(&mut self, key: IntKey, value: u64) {
        self.1.upsert(&key, &value);
        self.0.insert(key, value);
    }

    /// Return a serialised representation of the [`MerkleSearchTree`] pages for
    /// diff computations.
    pub fn page_ranges(&mut self) -> Vec<PageRange<'_, IntKey>> {
        self.1.root_hash();
        self.1.serialise_page_ranges().unwrap()
    }

    /// Return an iterator over the specified inclusive range of keys.
    pub fn key_range_iter(
        &self,
        key_range: RangeInclusive<&'_ IntKey>,
    ) -> impl Iterator<Item = (&IntKey, &u64)> {
        self.0.range(key_range)
    }

    pub fn key_count(&self) -> usize {
        self.0.len()
    }
}
