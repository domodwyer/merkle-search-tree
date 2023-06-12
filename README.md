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

[paper]: https://inria.hal.science/hal-02303490
[^cite]: Alex Auvolat, François Taïani. Merkle Search Trees: Efficient
    State-Based CRDTs in Open Networks. SRDS 2019 - 38th IEEE International
    Symposium on Reliable Distributed Systems, Oct 2019, Lyon, France. pp.1-10,
    ⟨10.1109/SRDS.2019.00032⟩. ⟨hal-02303490⟩