use std::{
    fmt::{Debug, Display},
    marker::PhantomData,
};

use siphasher::sip128::SipHasher24;

use crate::{
    diff::PageRange,
    digest::{self, siphash::SipHasher, Hasher, RootHash, ValueDigest},
    node::Node,
    page::{insert_intermediate_page, Page},
    visitor::{page_range_hash::PageRangeHashVisitor, Visitor},
};

/// An alias for the default hash implementation.
type DefaultHasher = SipHasher;

/// An implementation of the Merkle Search Tree as described in [Merkle Search
/// Trees: Efficient State-Based CRDTs in Open Networks][paper].
///
/// This implementation stores only keys directly in the tree - hashes of values
/// are retained instead of the actual value. This allows greatest flexibility,
/// as the user can choose the most appropriate key/value storage data
/// structure, while using the MST strictly for anti-entropy / Merkle proofs.
///
/// # Merkle Search Trees
///
/// In addition to the normal hash & consistency properties of a regular
/// Merkle/hash tree, a MST is a searchable balanced B-tree with variable,
/// probabilistically bounded page sizes and a deterministic representation
/// irrespective of insert order - these properties make a MST a useful data
/// structure for efficient state-based CRDT replication and anti-entropy.
///
/// Keys are stored in sort order (from min to max) in an MST. If monotonic keys
/// are inserted, a minimal amount of hash re-computation needs to be performed
/// as the nodes & pages for most of the older keys remain unchanged; this
/// reduces the overhead of anti-entropy as fewer intermediate hashes need
/// recomputing and exchanging during reconciliation.
///
/// # Portability & Compatibility
///
/// For two [`MerkleSearchTree`] to be useful, both instances must produce
/// identical hash digests for a given input. To do so, they must be using the
/// same [`Hasher`] implementation, and in turn it must output a deterministic
/// hash across all peers interacting with the [`MerkleSearchTree`].
///
/// For ease of use, this library uses the standard library [`Hash`] trait by
/// default to hash key and value types. The documentation for the trait warns
/// it is not guaranteed to produce identical hashes for the same data across
/// different compilation platforms and Rust compiler versions.
///
/// If you intend to interact with peers across multiple platforms and/or Rust
/// versions, you should consider implementing a fully-deterministic [`Hasher`]
/// specialised to your key/value types that does not make use of the [`Hash`]
/// trait for correctness.
///
/// Any change to the underlying hash construction algorithm implemented in this
/// crate that would cause existing hashes to no longer match will not occur
/// without a breaking change major semver version bump once this crate reaches
/// stability (>1.0.0).
///
/// # Lazy Tree Hash Generation
///
/// Each page within the tree maintains a cache of the pre-computed hash of
/// itself, and the sub-tree rooted from it (all pages & nodes below it).
/// Successive root hash queries will re-use this cached value to avoid hashing
/// the full tree each time.
///
/// Upserting elements into the tree invalidates the cached hashes of the pages
/// along the path to the leaf, and the leaf page itself. To amortise the cost
/// of regenerating these hashes, the affected pages are marked as "dirty",
/// causing them to be rehashed next time the root hash is requested. This
/// allows hash regeneration to be occur once per batch of upsert operations.
///
/// # Example
///
/// ```
/// use merkle_search_tree::MerkleSearchTree;
///
/// let mut t = MerkleSearchTree::default();
/// t.upsert(&"bananas", &"great");
/// t.upsert(&"plátano", &"muy bien");
///
/// // Obtain a root hash / merkle proof covering all the tree data
/// let hash_1 = t.root_hash().to_owned();
/// println!("{:?}", hash_1.as_ref());
///
/// // Modify the MST, reflecting the new value of an existing key
/// t.upsert(&"bananas", &"amazing");
///
/// // Obtain an updated root hash
/// let hash_2 = t.root_hash().to_owned();
/// println!("{:?}", hash_2);
///
/// // The root hash changes to reflect the changed state
/// assert_ne!(hash_1.as_ref(), hash_2.as_ref());
/// ```
///
/// [paper]: https://inria.hal.science/hal-02303490
#[derive(Debug, Clone)]
pub struct MerkleSearchTree<K, V, H = DefaultHasher, const N: usize = 16> {
    /// User-provided hasher implementation used for key/value digests.
    hasher: H,

    /// Internal hasher used to produce page/root digests.
    tree_hasher: SipHasher24,

    root: Page<N, K>,
    root_hash: Option<RootHash>,

    _value_type: PhantomData<V>,
}

impl<K, V> Default for MerkleSearchTree<K, V> {
    fn default() -> Self {
        Self {
            hasher: SipHasher::default(),
            tree_hasher: SipHasher24::default(),
            root: Page::new(0, vec![]),
            root_hash: None,
            _value_type: Default::default(),
        }
    }
}

impl<K, V, H, const N: usize> MerkleSearchTree<K, V, H, N>
where
    K: Clone,
{
    /// Initialise a new [`MerkleSearchTree`] using the provided [`Hasher`] of
    /// keys & values.
    pub fn new_with_hasher(hasher: H) -> Self {
        Self {
            hasher,
            tree_hasher: SipHasher24::default(),
            root: Page::new(0, vec![]),
            root_hash: None,
            _value_type: PhantomData,
        }
    }
}

impl<K, V, H, const N: usize> MerkleSearchTree<K, V, H, N> {
    /// Return the precomputed root hash, if any.
    ///
    /// This method never performs any hashing - if there's no precomputed hash
    /// available, this immediately returns [`None`]. This operation is `O(1)`.
    ///
    /// If this returns [`None`], call [`MerkleSearchTree::root_hash()`] to
    /// regenerate the root hash.
    #[inline]
    pub fn root_hash_cached(&self) -> Option<&RootHash> {
        self.root_hash.as_ref()
    }
}

impl<K, V, H, const N: usize> MerkleSearchTree<K, V, H, N>
where
    K: AsRef<[u8]>,
{
    /// Generate the root hash if necessary, returning the result.
    ///
    /// If there's a precomputed root hash, it is immediately returned.
    ///
    /// If no cached root hash is available all tree pages with modified child
    /// nodes are rehashed and the resulting new root hash is returned.
    #[inline]
    pub fn root_hash(&mut self) -> &RootHash {
        self.root.maybe_generate_hash(&self.tree_hasher);
        self.root_hash = self.root.hash().cloned().map(RootHash::new);

        #[cfg(feature = "digest_base64")] // Required for display impl
        debug!(
            root_hash=%self.root_hash.as_ref().unwrap(),
            "regenerated root hash"
        );

        self.root_hash.as_ref().unwrap()
    }

    /// Serialise the key intervals covered by each [`Page`] within this tree.
    ///
    /// Performs a pre-order traversal of all pages within this tree and emits a
    /// [`PageRange`] per page that covers the min/max key of the subtree at the
    /// given page.
    ///
    /// The first page is the tree root, and as such has a key min/max that
    /// equals the min/max of the keys stored within this tree.
    pub fn serialise_page_ranges(&self) -> Option<Vec<PageRange<'_, K>>>
    where
        K: PartialOrd,
    {
        // The tree hash must be up-to-date.
        self.root_hash_cached()?;
        let mut v = PageRangeHashVisitor::default();
        self.root.in_order_traversal(&mut v, false);
        Some(v.finalise())
    }
}

impl<K, V, H, const N: usize> MerkleSearchTree<K, V, H, N>
where
    K: PartialOrd + Clone,
    H: Hasher<N, K> + Hasher<N, V>,
{
    /// Add or update the value for `key`.
    ///
    /// This method invalidates the cached, precomputed root hash value, if any
    /// (even if the value is not modified).
    #[inline]
    pub fn upsert(&mut self, key: &'_ K, value: &'_ V) {
        let value_hash = ValueDigest::new(self.hasher.hash(value));
        let level = digest::level(&self.hasher.hash(key));

        // Invalidate the root hash - it always changes when a key is upserted.
        self.root_hash = None;

        if !self.root.upsert(key, level, value_hash.clone()) {
            // As an optimisation and simplification, if the current root is
            // empty, simply replace it with the new root.
            if self.root.nodes().is_empty() {
                let node = Node::new(key.clone(), value_hash, None);
                self.root = Page::new(level, vec![node]);
                return;
            }

            insert_intermediate_page(&mut &mut self.root, key.clone(), level, value_hash);
        }
    }
}

impl<K, V, H, const N: usize> MerkleSearchTree<K, V, H, N>
where
    K: PartialOrd + Display,
{
    /// Perform a depth-first, in-order traversal, yielding each [`Page`] and
    /// [`Node`] to `visitor`.
    ///
    /// An in-order traversal yields nodes in key order, from min to max.
    pub fn in_order_traversal<'a, T>(&'a self, visitor: &mut T)
    where
        T: Visitor<'a, N, K>,
    {
        self.root.in_order_traversal(visitor, false);
    }
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, hash::Hasher as _};

    use proptest::prelude::*;
    use siphasher::sip128::Hasher128;

    use crate::{
        assert_tree,
        digest::{
            mock::{LevelKey, MockHasher},
            Digest,
        },
        visitor::{
            assert_count::InvariantAssertCount, assert_order::InvariantAssertOrder, nop::NopVisitor,
        },
    };

    use super::*;

    /// A hash implementation that does not rely on the stdlib Hash trait, and
    /// therefore produces stable hashes across rust version changes /
    /// platforms.
    #[derive(Debug, Default)]
    struct FixtureHasher;
    impl Hasher<16, IntKey> for FixtureHasher {
        fn hash(&self, value: &IntKey) -> Digest<16> {
            self.hash(&value.0)
        }
    }
    impl Hasher<16, u64> for FixtureHasher {
        fn hash(&self, value: &u64) -> Digest<16> {
            let mut h = SipHasher24::default();
            h.write_u64(*value);
            Digest::new(h.finish128().as_bytes())
        }
    }

    /// An wrapper over integers, implementing `AsRef<[u8]>` with deterministic
    /// output across platforms with differing endian-ness.
    #[derive(Debug, PartialOrd, PartialEq, Clone, Hash)]
    struct IntKey(u64, [u8; 8]);
    impl IntKey {
        fn new(v: u64) -> Self {
            Self(v, v.to_be_bytes())
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

    #[test]
    fn test_hash_fixture() {
        let mut t = MerkleSearchTree::new_with_hasher(FixtureHasher::default());

        for i in 0..1000 {
            t.upsert(&IntKey::new(i), &i);
        }

        // This hash ensures that any changes to this construction do not result
        // in existing hashes being invalidated / unequal for the same data.
        let fixture_hash = [
            57, 77, 199, 66, 89, 217, 207, 166, 136, 181, 45, 80, 108, 80, 94, 3,
        ];

        assert_eq!(t.root_hash().as_ref(), &fixture_hash);
    }

    #[test]
    fn test_level_generation() {
        let h = Digest::new([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(digest::level(&h), 32);

        let h = Digest::new([1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(digest::level(&h), 0);

        let h = Digest::new([0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(digest::level(&h), 1);

        let h = Digest::new([0, 0x10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert_eq!(digest::level(&h), 3);
    }

    macro_rules! test_insert {
        (
			$name:ident,
			values = [$(($key:expr, $value:expr)),*]
		) => {
            paste::paste! {
                #[test]
                fn [<test_ $name>]() {
                    let mut t = MerkleSearchTree::new_with_hasher(MockHasher::default());

					$(
						t.upsert(&$key, $value);
					)*

                    assert_tree!(t)
                }
            }
        };
    }

    test_insert!(one, values = [(LevelKey::new("key", 0), &"bananas")]);

    test_insert!(
        one_non_zero_level,
        values = [(LevelKey::new("key", 4), &"bananas")]
    );

    // Assert the tree is ordered by key.
    test_insert!(
        two_in_order,
        values = [
            (LevelKey::new("A", 0), &"bananas"),
            (LevelKey::new("B", 0), &"bananas")
        ]
    );

    // Assert the tree becomes ordered by key.
    test_insert!(
        two_unordered,
        values = [
            (LevelKey::new("B", 0), &"bananas"),
            (LevelKey::new("A", 0), &"bananas")
        ]
    );

    // Insert two values
    //
    // Level 0 [ A ]
    //
    // Then insert B, which is destined for level 1, and greater than A;
    // therefore B is placed in level 1 as the new root, and A/level 0 is
    // attached to the lt_pointer of B.
    test_insert!(
        root_split_page_gt,
        values = [
            (LevelKey::new("A", 0), &"bananas"),
            (LevelKey::new("B", 1), &"bananas")
        ]
    );

    // Insert two values
    //
    // Level 0 [ B ]
    //
    // Then insert A, which is destined for level 1, and less than B;
    // therefore A is placed in level 1 as the new root, and B/level 0 is
    // attached to the high page of level 1 because A < B.
    test_insert!(
        root_split_page_lt,
        values = [
            (LevelKey::new("B", 0), &"bananas"),
            (LevelKey::new("A", 1), &"bananas")
        ]
    );

    // Insert two values, the second with a level higher than the first, causing
    // the root page to be split, both with differing (non-consecutive) levels.
    test_insert!(
        root_split_non_zero_step_gt,
        values = [
            (LevelKey::new("A", 3), &"bananas"),
            (LevelKey::new("B", 9), &"bananas")
        ]
    );

    // Insert two values, the second with a level higher than the first, causing
    // the root page to be split, both with differing (non-consecutive) levels.
    test_insert!(
        root_split_non_zero_step_lt,
        values = [
            (LevelKey::new("B", 3), &"bananas"),
            (LevelKey::new("A", 9), &"bananas")
        ]
    );

    // Insert elements that cause the root to split, and then the child page to
    // split. Each successive element causes a new page to be created and added
    // to the previous level's high page.
    test_insert!(
        non_root_page_split_gt,
        values = [
            (LevelKey::new("A", 6), &"bananas"),
            (LevelKey::new("B", 4), &"bananas"),
            (LevelKey::new("C", 2), &"bananas")
        ]
    );

    test_insert!(
        non_root_page_split_lt,
        values = [
            (LevelKey::new("C", 6), &"bananas"),
            (LevelKey::new("B", 4), &"bananas"),
            (LevelKey::new("A", 2), &"bananas")
        ]
    );

    // Upsert for an existing key does not create more nodes.
    test_insert!(
        update,
        values = [
            (LevelKey::new("A", 6), &"bananas"),
            (LevelKey::new("A", 6), &"platanos")
        ]
    );

    // Upsert for an existing key does not create more nodes.
    test_insert!(
        split_child_into_two_empty_gte_page,
        values = [
            (LevelKey::new("A", 5), &"platanos"),
            (LevelKey::new("B", 0), &"platanos"),
            (LevelKey::new("C", 0), &"platanos"),
            (LevelKey::new("D", 1), &"platanos")
        ]
    );

    // Upsert for an existing key does not create more nodes.
    test_insert!(
        split_child_into_two_with_gte_page,
        values = [
            (LevelKey::new("A", 5), &"platanos"),
            (LevelKey::new("B", 0), &"platanos"),
            (LevelKey::new("C", 0), &"platanos"),
            (LevelKey::new("E", 0), &"platanos"),
            (LevelKey::new("D", 1), &"platanos")
        ]
    );

    // Ensure that when inserting a node greater than all existing nodes in a
    // page, the high page is split if necessary
    test_insert!(
        greatest_key_splits_high_page,
        values = [
            (LevelKey::new(11, 1), &"bananas"),
            (LevelKey::new(10, 2), &"bananas"),
            (LevelKey::new(12, 2), &"bananas")
        ]
    );

    // When inserting an intermediate page, ensure the high-page of the
    // less-than split is processed.
    test_insert!(
        intermediate_page_move_all_nodes_and_high_page,
        values = [
            (LevelKey::new(1, 1), &"bananas"),
            (LevelKey::new(2, 1), &"bananas"),
            (LevelKey::new(4, 0), &"bananas"),
            (LevelKey::new(3, 2), &"bananas")
        ]
    );

    test_insert!(
        intermediate_page_move_all_nodes_and_high_page_subset,
        values = [
            (LevelKey::new(1, 1), &"bananas"),
            (LevelKey::new(2, 1), &"bananas"),
            (LevelKey::new(3, 0), &"bananas"),
            (LevelKey::new(5, 0), &"bananas"),
            (LevelKey::new(4, 2), &"bananas")
        ]
    );

    test_insert!(
        child_page_split_add_intermediate,
        values = [
            (LevelKey::new("K", 2), &"bananas"),
            (LevelKey::new("D", 0), &"bananas"),
            (LevelKey::new("E", 1), &"bananas")
        ]
    );

    test_insert!(
        equal_page_move_all_nodes_and_high_page,
        values = [
            (LevelKey::new(2_usize, 64), &"bananas"),
            (LevelKey::new(5_usize, 20), &"bananas"),
            (LevelKey::new(3_usize, 52), &"bananas"),
            (LevelKey::new(4_usize, 64), &"bananas")
        ]
    );

    test_insert!(
        equal_page_move_all_nodes_and_high_page_subset,
        values = [
            (LevelKey::new(2_usize, 64), &"bananas"),
            (LevelKey::new(6_usize, 20), &"bananas"),
            (LevelKey::new(4_usize, 20), &"bananas"),
            (LevelKey::new(3_usize, 52), &"bananas"),
            (LevelKey::new(5_usize, 64), &"bananas")
        ]
    );

    test_insert!(
        split_page_all_gte_nodes_with_lt_pointer,
        values = [
            (LevelKey::new(1, 0), &"bananas"),
            (LevelKey::new(0, 1), &"bananas")
        ]
    );

    test_insert!(
        split_page_all_lt_nodes_with_high_page,
        values = [
            (LevelKey::new(0, 0), &"bananas"),
            (LevelKey::new(1, 1), &"bananas")
        ]
    );

    test_insert!(
        insert_intermediate_recursive_lt_pointer,
        values = [
            (LevelKey::new(1_usize, 1), &""),
            (LevelKey::new(2_usize, 0), &""),
            (LevelKey::new(4_usize, 1), &""),
            (LevelKey::new(3_usize, 2), &"")
        ]
    );

    test_insert!(
        split_page_move_gte_lt_pointer_to_high_page,
        values = [
            (LevelKey::new(1_usize, 1), &""),
            (LevelKey::new(2_usize, 0), &""),
            (LevelKey::new(4_usize, 1), &""),
            (LevelKey::new(3_usize, 2), &"")
        ]
    );

    test_insert!(
        split_page_move_input_high_page_to_gte_page,
        values = [
            (LevelKey::new(6, 0), &"bananas"),
            (LevelKey::new(3, 21), &"bananas"),
            (LevelKey::new(0, 21), &"bananas"),
            (LevelKey::new(1, 22), &"bananas")
        ]
    );

    proptest! {
        // Invariant 1: the tree structure is deterministic for a given set of
        // inputs (regardless of insert order)
        #[test]
        fn prop_deterministic_construction(keys in proptest::collection::vec(any::<u64>(), 0..64)) {
            // keys is a HashSet of (keys, level), which will iterate in random
            // order.
            //
            // Collect the items into a vector and sort it, producing a
            // different insert ordering from the HashSet iter.
            let mut b_values = keys.to_vec();
            b_values.sort();
            b_values.dedup();

            let a_values = keys;

            let mut a = MerkleSearchTree::default();
            let mut b = MerkleSearchTree::default();

            let want_len = b_values.len();

            let mut unique = HashSet::new();
            for key in a_values {
                if unique.insert(key) {
                    a.upsert(&IntKey::new(key), &"bananas");
                }
            }
            for key in b_values {
                b.upsert(&IntKey::new(key), &"bananas");
            }

            assert_eq!(a.root_hash(), b.root_hash());
            assert_eq!(a.root, b.root);

            let mut asserter = InvariantAssertCount::new(InvariantAssertOrder::new(NopVisitor::default()));
            a.in_order_traversal(&mut asserter);
            asserter.unwrap_count(want_len);

            let mut asserter = InvariantAssertCount::new(InvariantAssertOrder::new(NopVisitor::default()));
            b.in_order_traversal(&mut asserter);
            asserter.unwrap_count(want_len);
        }

        // Invariant 2: values in the tree are stored in key order.
        #[test]
        fn prop_in_order_traversal_key_order(keys in proptest::collection::vec(any::<u64>(), 0..64)) {
            let mut t = MerkleSearchTree::default();

            let mut unique = HashSet::new();
            let mut want_len = 0;

            for key in keys {
                if unique.insert(key) {
                    want_len += 1;
                    t.upsert(&IntKey::new(key), &"bananas");
                }
            }

            let mut asserter = InvariantAssertCount::new(InvariantAssertOrder::new(NopVisitor::default()));
            t.in_order_traversal(&mut asserter);
            asserter.unwrap_count(want_len);
        }

        // Invariant 3: two independent trees contain the same data iff their
        // root hashes are identical
        #[test]
        fn prop_root_hash_data_equality(keys in proptest::collection::vec(any::<u64>(), 0..64)) {
            let mut a = MerkleSearchTree::default();
            let mut b = MerkleSearchTree::default();

            // They are equal when empty.
            assert_eq!(a.root_hash(), b.root_hash());

            let mut unique = HashSet::new();
            let last_entry = keys.first().cloned();
            for key in keys {
                if !unique.insert(key) {
                    // Root hashes may compute to the same value if the same
                    // (key, value) pair is inserted twice, causing the
                    // divergence assert below to spuriously trigger.
                    continue;
                }

                a.upsert(&IntKey::new(key), &"bananas");
                assert_eq!(a.root_hash_cached(), None);

                // The trees diverge
                assert_ne!(a.root_hash(), b.root_hash());

                b.upsert(&IntKey::new(key), &"bananas");
                assert_eq!(b.root_hash_cached(), None);

                // And then converge
                assert_eq!(a.root_hash(), b.root_hash());
            }

            // Update a value for an existing key
            if let Some(key) = last_entry {
                 b.upsert(&IntKey::new(key), &"platanos");
                 assert_eq!(b.root_hash_cached(), None);

                 // The trees diverge
                 assert_ne!(a.root_hash(), b.root_hash());

                 // And converge once again
                 b.upsert(&IntKey::new(key), &"platanos");
                 assert_eq!(b.root_hash_cached(), None);

                 assert_ne!(a.root_hash(), b.root_hash());
            }

            let mut asserter = InvariantAssertCount::new(InvariantAssertOrder::new(NopVisitor::default()));
            a.in_order_traversal(&mut asserter);
            asserter.unwrap_count(unique.len());

            let mut asserter = InvariantAssertCount::new(InvariantAssertOrder::new(NopVisitor::default()));
            b.in_order_traversal(&mut asserter);
            asserter.unwrap_count(unique.len());
        }
    }
}
