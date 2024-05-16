use std::hint::black_box;

use criterion::{measurement::WallTime, BenchmarkGroup, BenchmarkId, Criterion, Throughput};
use merkle_search_tree::MerkleSearchTree;

use crate::{Lfsr, ROW_COUNTS};

struct BenchName {
    name: &'static str,
    values_inserted: usize,
}

impl From<BenchName> for BenchmarkId {
    fn from(v: BenchName) -> Self {
        Self::new(v.name, format!("{}_keys", v.values_inserted))
    }
}

pub(super) fn bench_node_iter(c: &mut Criterion) {
    let mut g = c.benchmark_group("node_iter");

    // Collecting U64 values
    for &n_values in ROW_COUNTS {
        iter_param(&mut g, n_values, "collect", |t| {
            black_box(t.node_iter().collect::<Vec<_>>());
        });
    }

    // Visiting u64 values
    for &n_values in ROW_COUNTS {
        iter_param(&mut g, n_values, "visit", |t| {
            t.node_iter().for_each(|v| {
                black_box(v);
            });
        });
    }
}

fn iter_param<F, T>(g: &mut BenchmarkGroup<'_, WallTime>, n_values: usize, name: &'static str, f: F)
where
    F: Fn(&MerkleSearchTree<u64, u64>) -> T,
{
    // Generate benchmark data using a pseudo random sequence with the same seed
    // for reproducible runs.
    let mut rand = Lfsr::default();

    let mut t = MerkleSearchTree::default();

    (0..n_values)
        .map(|_| rand.next() as u64)
        .for_each(|v| t.upsert(v, &v));

    let bench_name = BenchName {
        name,
        values_inserted: n_values,
    };

    g.throughput(Throughput::Elements(n_values as _));
    g.bench_with_input(BenchmarkId::from(bench_name), &t, |b, t| {
        b.iter(|| f(t));
    });
}
