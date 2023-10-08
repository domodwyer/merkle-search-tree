#![no_main]

use std::{collections::BTreeMap, ops::RangeInclusive};

use libfuzzer_sys::{arbitrary::Arbitrary, fuzz_target};
use merkle_search_tree::{
    diff::{diff, PageRange},
    MerkleSearchTree,
};

// An owned PageRange payload, from which a PageRange instance will be
// projected.
#[derive(Debug)]
struct Input {
    key: String,
    value: u16,
}

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(
        u: &mut libfuzzer_sys::arbitrary::Unstructured<'a>,
    ) -> libfuzzer_sys::arbitrary::Result<Self> {
        Ok(Self {
            key: u.arbitrary()?,
            value: u.arbitrary()?,
        })
    }
}

// Feed the diff() algorithm with random PageRange lists.
fuzz_target!(|data: (Vec<Input>, Vec<Input>)| {
    let mut a = Node::default();
    let mut b = Node::default();

    for input in data.0 {
        a.upsert(input.key, input.value);
    }
    for input in data.1 {
        b.upsert(input.key, input.value);
    }

    // Drive them to convergence, recording sync statistics.
    while a.1.root_hash() != b.1.root_hash() {
        sync_round(&mut a, &mut b);
        sync_round(&mut b, &mut a);
    }
});

/// Perform a single sync round, pulling differences from a into b.
fn sync_round(from: &mut Node, to: &mut Node) {
    // First sync b from a, applying the "a is always right" merge rule.
    let a2 = from.clone();
    let a_tree = from.page_ranges();

    let mut to2 = to.clone();
    let want = diff(to2.page_ranges(), a_tree);

    for range in want {
        for (k, v) in a2.key_range_iter(range.start().to_owned()..=range.end().to_owned()) {
            to.upsert(k.clone(), *v);
        }
    }
}

/// A mock peer, storing `(key, value)` tuples and maintaining a
/// [`MerkleSearchTree`] of the store contents.
#[derive(Default, Clone)]
pub struct Node(BTreeMap<String, u16>, MerkleSearchTree<String, u16>);

impl Node {
    /// Store the given `key` & `value` in the node, replacing the previous
    /// value of `key`, if any.
    pub fn upsert(&mut self, key: String, value: u16) {
        self.1.upsert(key.clone(), &value);
        self.0.insert(key, value);
    }

    /// Return a serialised representation of the [`MerkleSearchTree`] pages for
    /// diff computations.
    pub fn page_ranges(&mut self) -> Vec<PageRange<'_, String>> {
        self.1.root_hash();
        self.1.serialise_page_ranges().unwrap()
    }

    /// Return an iterator over the specified inclusive range of keys.
    pub fn key_range_iter(
        &self,
        key_range: RangeInclusive<String>,
    ) -> impl Iterator<Item = (&String, &u16)> {
        self.0.range(key_range)
    }
}
