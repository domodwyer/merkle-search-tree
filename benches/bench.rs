use std::hash::Hash;

use criterion::{
    criterion_group, criterion_main, measurement::WallTime, BenchmarkGroup, BenchmarkId, Criterion,
    Throughput,
};
use merkle_search_tree::MerkleSearchTree;

fn bench(c: &mut Criterion) {
    {
        let mut g = c.benchmark_group("insert");

        // U64 values
        insert_param(&mut g, "u64", 1, |rand| rand as u64);
        insert_param(&mut g, "u64", 100, |rand| rand as u64);
        insert_param(&mut g, "u64", 1_000, |rand| rand as u64);
        insert_param(&mut g, "u64", 10_000, |rand| rand as u64);

        // 36 byte strings (same as UUIDs)
        insert_param(&mut g, "string_36", 1, |rand| format!("{rand:0>36}"));
        insert_param(&mut g, "string_36", 100, |rand| format!("{rand:0>36}"));
        insert_param(&mut g, "string_36", 1_000, |rand| format!("{rand:0>36}"));
        insert_param(&mut g, "string_36", 10_000, |rand| format!("{rand:0>36}"));
    }

    let mut g = c.benchmark_group("generate_root_hash");
    generate_root(&mut g, "string_36", 10_000, |rand| format!("{rand:0>36}"));
}

fn insert_param<F, T>(
    g: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    n_values: usize,
    make_value: F,
) where
    F: Fn(u16) -> T,
    T: PartialOrd + Eq + Clone + Hash,
{
    // Generate benchmark data using a pseudo random sequence with the same seed
    // for reproducible runs.
    let mut rand = Lfsr::default();
    let values = (0..n_values)
        .map(|_| make_value(rand.next()))
        .collect::<Vec<_>>();

    g.throughput(Throughput::Elements(n_values as _));
    g.bench_with_input(BenchmarkId::new(name, n_values), &values, |b, values| {
        b.iter(|| {
            let mut t = MerkleSearchTree::default();
            for v in values {
                t.upsert(&v, &42);
            }
        });
    });
}

fn generate_root<F, T>(
    g: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    n_values: usize,
    make_value: F,
) where
    F: Fn(u16) -> T,
    T: PartialOrd + Eq + Clone + Hash + AsRef<[u8]>,
{
    // Generate benchmark data using a pseudo random sequence with the same seed
    // for reproducible runs.
    let mut rand = Lfsr::default();
    let values = (0..n_values)
        .map(|_| make_value(rand.next()))
        .collect::<Vec<_>>();

    g.throughput(Throughput::Elements(n_values as _));
    g.bench_with_input(BenchmarkId::new(name, n_values), &values, |b, values| {
        let mut t = MerkleSearchTree::default();
        for v in values {
            t.upsert(v, &42);
        }
        b.iter_batched(
            || t.clone(),
            |mut t| {
                let _v = t.root_hash();
            },
            criterion::BatchSize::NumIterations(1),
        );
    });

    // Benchmark the performance of rebuilding the tree after changing the value
    // of a single node.
    g.bench_with_input(
        BenchmarkId::new(format!("{}_minimal_rebuild", name), n_values),
        &values,
        |b, values| {
            // Populate the tree
            let mut t = MerkleSearchTree::default();
            for v in values {
                t.upsert(v, &42);
            }

            // Generate full tree hash
            let _ = t.root_hash();

            // Invalidate that hash
            t.upsert(values.last().as_ref().unwrap(), &424242);

            // Measure rebuilding the root hash
            b.iter_batched(
                || t.clone(),
                |mut t| {
                    let _v = t.root_hash();
                },
                criterion::BatchSize::NumIterations(1),
            );
        },
    );

    // Benchmark the performance of rebuilding the tree after changing the value
    // of half the nodes.
    g.bench_with_input(
        BenchmarkId::new(format!("{}_partial_rebuild", name), n_values),
        &values,
        |b, values| {
            // Populate the tree
            let mut t = MerkleSearchTree::default();
            for v in values {
                t.upsert(v, &42);
            }

            // Generate full tree hash
            let _ = t.root_hash();

            // Invalidate the hash of N/2 nodes
            for v in values.iter().take(n_values / 2) {
                t.upsert(v, &42424242);
            }

            // Measure rebuilding the root hash
            b.iter_batched(
                || t.clone(),
                |mut t| {
                    let _v = t.root_hash();
                },
                criterion::BatchSize::NumIterations(1),
            );
        },
    );
}

criterion_group!(benches, bench);
criterion_main!(benches);

/// Linear-feedback shift register based PRNG.
///
/// Generates 65,535 unique values before cycling.
#[derive(Debug)]
struct Lfsr(u16);

impl Default for Lfsr {
    fn default() -> Self {
        Self(42)
    }
}

impl Lfsr {
    fn next(&mut self) -> u16 {
        let lsb = self.0 & 1;
        self.0 >>= 1;
        if lsb == 1 {
            self.0 ^= 0xD008;
        }
        self.0
    }
}
