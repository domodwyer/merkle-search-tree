use std::{
    collections::BTreeMap,
    fmt::{Display, Write},
    ops::RangeInclusive,
};

use merkle_search_tree::{
    diff::{diff, PageRange},
    MerkleSearchTree,
};

const N_VALUES: usize = 5_000;

#[derive(Debug, Default)]
struct SyncStats {
    /// Number of sync "rounds" required to converge the trees, where a "round"
    /// is a two way diff + key fetch.
    rounds: usize,

    keys_a_to_b: DirectionStats,
    keys_b_to_a: DirectionStats,
}

#[derive(Debug)]
struct DirectionStats {
    /// Minimum number of keys synced in a single round.
    min: usize,
    /// Maximum number of keys synced in a single round.
    max: usize,
    /// Total number of keys synced in one direction, across all syncs.
    total: usize,

    /// Number of rounds that sync'd 0 keys.
    zero_rounds: usize,
}

impl Default for DirectionStats {
    fn default() -> Self {
        Self {
            min: usize::MAX,
            max: usize::MIN,
            total: Default::default(),
            zero_rounds: Default::default(),
        }
    }
}

impl Display for DirectionStats {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:>10} keys total\tmin {:>10}\tmax {:>10}\t{} zero rounds",
            self.total, self.min, self.max, self.zero_rounds
        )
    }
}

/// A test that drives convergence between two randomly generated reference
/// trees (random key/value pairs are deterministic across runs), and records
/// statistics describing the keys/rounds required to reach convergence.
///
/// MST/diff changes can change the efficiency of syncs, and this test surfaces
/// those changes.
#[test]
fn test_sync_rounds() {
    let mut out = String::new();
    let mut total_rounds = 0;
    let mut total_keys = 0;
    let mut n_rounds = 0;
    for i in 1..=30 {
        let v = do_sync(Lfsr(i));

        writeln!(
            &mut out,
            "[*] sync with seed {i} - total sync rounds: {}",
            v.rounds
        )
        .unwrap();
        writeln!(
            &mut out,
            "\ta->b: {}\tavg: {:<5} keys per round",
            v.keys_a_to_b,
            v.keys_a_to_b
                .total
                .checked_div(v.rounds)
                .unwrap_or_default(),
        )
        .unwrap();
        writeln!(
            &mut out,
            "\tb->a: {}\tavg: {:<5} keys per round",
            v.keys_b_to_a,
            v.keys_b_to_a
                .total
                .checked_div(v.rounds)
                .unwrap_or_default(),
        )
        .unwrap();
        writeln!(&mut out).unwrap();

        total_rounds += v.rounds;
        n_rounds += 1;
        total_keys += v.keys_a_to_b.total;
        total_keys += v.keys_b_to_a.total;
    }

    writeln!(&mut out).unwrap();
    writeln!(
        &mut out,
        "{total_rounds} total sync rounds needed to converge {n_rounds} tree \
		pairs (average {:.2} rounds, {} keys per pair)",
        total_rounds as f32 / n_rounds as f32,
        total_keys / n_rounds,
    )
    .unwrap();

    insta::assert_snapshot!(out);
}

fn do_sync(mut rand: Lfsr) -> SyncStats {
    let mut a = Node::default();
    let mut b = Node::default();

    // Populate the trees with disjoint keys
    for _ in 0..(N_VALUES / 2) {
        a.upsert(rand.next().to_string(), rand.next());
        b.upsert(rand.next().to_string(), rand.next());
    }

    // Populate the trees with identical key/value pairs
    for _ in 0..(N_VALUES / 2) {
        let key = rand.next().to_string();
        let value = rand.next();
        a.upsert(key.clone(), value);
        b.upsert(key.clone(), value);
    }

    let mut result = SyncStats::default();

    // Drive them to convergence, recording sync statistics.
    while a.1.root_hash() != b.1.root_hash() {
        result.rounds += 1;
        sync_round(&mut a, &mut b, &mut result.keys_a_to_b);
        sync_round(&mut b, &mut a, &mut result.keys_b_to_a);
    }

    result
}

/// Perform a single sync round, pulling differences from a into b.
fn sync_round(from: &mut Node, to: &mut Node, stats: &mut DirectionStats) {
    // First sync b from a, applying the "a is always right" merge rule.
    let a2 = from.clone();
    let a_tree = from.page_ranges();

    let mut to2 = to.clone();
    let want = diff(to2.page_ranges(), a_tree);

    let mut count = 0; // Number of keys upserted
    for range in want {
        for (k, v) in a2.key_range_iter(range.start().to_owned()..=range.end().to_owned()) {
            to.upsert(k.clone(), *v);
            count += 1;
        }
    }

    stats.min = stats.min.min(count);
    stats.max = stats.max.max(count);
    stats.total += count;

    if count == 0 {
        stats.zero_rounds += 1;
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

/// Linear-feedback shift register based PRNG.
///
/// Generates 65,535 unique values before cycling.
#[derive(Debug)]
pub struct Lfsr(u16);

impl Default for Lfsr {
    fn default() -> Self {
        Self(42)
    }
}

impl Lfsr {
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> u16 {
        let lsb = self.0 & 1;
        self.0 >>= 1;
        if lsb == 1 {
            self.0 ^= 0xD008;
        }
        self.0
    }
}
