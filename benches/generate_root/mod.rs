use std::fmt::Display;

use criterion::{measurement::WallTime, BenchmarkGroup, BenchmarkId, Criterion, Throughput};
use merkle_search_tree::MerkleSearchTree;

use crate::{Lfsr, ROW_COUNTS};

#[derive(Debug, Clone, Copy)]
struct BenchParams {
    values_inserted: usize,
}

impl Display for BenchParams {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_keys", self.values_inserted)
    }
}

pub(super) fn bench_generate_root(c: &mut Criterion) {
    let mut g = c.benchmark_group("regenerate_root_hash");

    for &n_values in ROW_COUNTS {
        bench_param(&mut g, n_values);
    }
}

fn bench_param(g: &mut BenchmarkGroup<'_, WallTime>, n_values: usize) {
    // Generate benchmark data using a pseudo random sequence with the same seed
    // for reproducible runs.
    let mut rand = Lfsr::default();
    let values = (0..n_values)
        .map(|_| format!("{:0>36}", rand.next()))
        .collect::<Vec<_>>();

    let bench_params = BenchParams {
        values_inserted: n_values,
    };

    // Hash generation for a tree for the first time touches every page.
    {
        g.throughput(Throughput::Elements(n_values as _));
        g.bench_with_input(
            BenchmarkId::new("complete_rehash", bench_params),
            &values,
            |b, values| {
                b.iter(|| {
                    let mut t = MerkleSearchTree::default();
                    for v in values {
                        t.upsert(&v, &42);
                    }
                });
            },
        );
    }

    // A minimal rebuild involves updating a single page and rebuilding the path
    // to the root.
    {
        g.throughput(Throughput::Elements(n_values as _));
        g.bench_with_input(
            BenchmarkId::new("minimal_rebuild", bench_params),
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
    }

    // A partial rebuild invalidates half the tree keys, and rebuilds the
    // modified page hashes and their paths to the root.
    {
        g.throughput(Throughput::Elements(n_values as _));
        g.bench_with_input(
            BenchmarkId::new("partial_rebuild", bench_params),
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
}
