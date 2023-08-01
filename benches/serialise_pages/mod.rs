use std::fmt::Display;

use criterion::{measurement::WallTime, BenchmarkGroup, Criterion, Throughput};
use merkle_search_tree::MerkleSearchTree;

use crate::{Lfsr, ROW_COUNTS};

#[derive(Debug, Clone, Copy)]
struct BenchName {
    n_values: usize,
    n_pages: usize,
}

impl Display for BenchName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}_keys/{}_pages", self.n_values, self.n_pages)
    }
}

pub(super) fn bench_serialise_pages(c: &mut Criterion) {
    let mut g = c.benchmark_group("serialise_pages");

    for &n_values in ROW_COUNTS {
        bench_param(&mut g, n_values)
    }
}

fn bench_param(g: &mut BenchmarkGroup<'_, WallTime>, n_values: usize) {
    // Generate the tree.
    let mut rand = Lfsr::default();
    let mut t = MerkleSearchTree::default();
    for _i in 0..n_values {
        t.upsert(rand.next().to_string(), &42_usize);
    }

    let _ = t.root_hash();
    let n_pages = t.serialise_page_ranges().unwrap().len();

    let bench_name = BenchName { n_values, n_pages };

    g.throughput(Throughput::Elements(n_values as _)); // Keys per second
    g.bench_function(bench_name.to_string(), |b| {
        b.iter(|| t.serialise_page_ranges());
    });
}
