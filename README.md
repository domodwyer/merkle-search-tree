[![crates.io](https://img.shields.io/crates/v/merkle-search-tree.svg)](https://crates.io/crates/merkle-search-tree)
[![docs.rs](https://docs.rs/merkle-search-tree/badge.svg)](https://docs.rs/merkle-search-tree)

# Merkle Search Tree

This crate implements a Merkle Search Tree as described in the 2019 paper
[Merkle Search Trees: Efficient State-Based CRDTs in Open Networks][paper] by
Alex Auvolat & François Taïani.[^cite]

When paired with CRDT-based value types, a Merkle Search Tree can act as an
efficient anti-entropy primitive, allowing independent replicas to concurrently
modify data within the tree with deterministic and eventual convergence across
all peers.

## Use It

```rust
use merkle_search_tree::{MerkleSearchTree, diff::diff};

// Initialise a tree using the default configuration, appropriate for most uses.
let mut node_a = MerkleSearchTree::default();

// Upsert values into the tree.
//
// For the MST construct to be a CRDT itself, the values stored into the tree 
// must also be CRDTs (or at least, have deterministic conflict resolution). 
// Here the MST is used as an add-only set (a trivial CRDT) by using () as the 
// key values.
node_a.upsert(&"bananas", &());
node_a.upsert(&"plátanos", &());

// Another node has differing keys.
let mut node_b = MerkleSearchTree::default();
node_b.upsert(&"donkey", &());

// The MST root hash can be used as an efficient consistency check (comparison 
// is O(1) in space and time).
//
// In this case, both trees are inconsistent w.r.t each other, which is 
// indicated by their differing root hashes.
assert_ne!(node_a.root_hash(), node_b.root_hash());

// The trees can be converged by pulling key ranges from peers - a differential 
// range identification implementation is included in this library:
let diff_range = diff(
    node_b.serialise_page_ranges().unwrap().into_iter(), 
    node_a.serialise_page_ranges().unwrap().into_iter()
);

// In this case, node B can obtain the missing/differing keys in node A by 
// requesting keys within the computed diff range (inclusive):
assert_matches::assert_matches!(diff_range.as_slice(), [range] => {
    assert_eq!(range.start(), &"bananas");
    assert_eq!(range.end(), &"plátanos");
});
```

[paper]: https://inria.hal.science/hal-02303490
[^cite]: Alex Auvolat, François Taïani. Merkle Search Trees: Efficient
    State-Based CRDTs in Open Networks. SRDS 2019 - 38th IEEE International
    Symposium on Reliable Distributed Systems, Oct 2019, Lyon, France. pp.1-10,
    ⟨10.1109/SRDS.2019.00032⟩. ⟨hal-02303490⟩