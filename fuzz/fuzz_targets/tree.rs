#![no_main]

use std::collections::HashMap;

use libfuzzer_sys::fuzz_target;
use merkle_search_tree::*;

fuzz_target!(|data: Vec<(Vec<u8>, Vec<u8>)>| {
    // Record the last (key, value) pair inserted into t1.
    let mut inserted: HashMap<&Vec<u8>, &Vec<u8>> = HashMap::default();

    // Write the fuzz key value pairs to a MST instance
    let mut t1 = MerkleSearchTree::default();
    for (k, v) in &data {
        inserted.insert(k, v);
        t1.upsert(k, &v);
    }

    // Insert the same key value pairs into another instance, relying on the
    // randomised order of the hashmap iteration to shuffle the key order.
    //
    // Note that because the update order for a given key does matter, this
    // dedupes the values for a given key, inserting only the last value
    // inserted into t1 for a given key.
    let mut t2 = MerkleSearchTree::default();
    for (k, v) in inserted {
        t2.upsert(k, v);
    }

    // Invariant: merkle search trees should be deterministic for a given set of
    // inputs regardless of order.
    let root_t1 = t1.root_hash();
    let root_t2 = t2.root_hash();
    assert_eq!(root_t1, root_t2);

    // Invariant: Serialised pages must be identical for identical root hashes
    let pages_t1 = t1.serialise_page_ranges().expect("root hash was generated");
    let pages_t2 = t2.serialise_page_ranges().expect("root hash was generated");
    assert_eq!(pages_t1, pages_t2);
});
