use criterion::{measurement::WallTime, BenchmarkGroup, BenchmarkId, Criterion, Throughput};
use merkle_search_tree::{diff::diff, MerkleSearchTree};

use crate::{Lfsr, ROW_COUNTS};

#[derive(Debug, Clone, Copy)]
struct BenchName {
    n_values: usize,
    n_pages: usize,
    pcnt_values_inconsistent: f64,
}

impl From<BenchName> for BenchmarkId {
    fn from(v: BenchName) -> Self {
        Self::new(
            format!(
                "{}%_inconsistent_values",
                (v.pcnt_values_inconsistent * 100.0).floor()
            ),
            format!(
                "{keys}_keys/{pages}_pages",
                keys = v.n_values,
                pages = v.n_pages,
            ),
        )
    }
}

pub(super) fn bench_diff(c: &mut Criterion) {
    let mut g = c.benchmark_group("diff");

    for pcnt_values_consistent in [0.0_f64, 0.25, 0.5, 0.75, 1.0] {
        for &n_values in ROW_COUNTS {
            bench_param(&mut g, n_values, pcnt_values_consistent)
        }
    }
}

fn bench_param(
    g: &mut BenchmarkGroup<'_, WallTime>,
    n_values: usize,
    pcnt_values_inconsistent: f64,
) {
    assert!(pcnt_values_inconsistent <= 1.0);

    // Generate the tree.
    let mut rand = Lfsr::default();
    let mut t = MerkleSearchTree::default();
    for _i in 0..n_values {
        t.upsert(rand.next().to_string(), &42_usize);
    }

    // Record the serialised pages
    let _ = t.root_hash();
    let original_pages = t.serialise_page_ranges().expect("must generate page list");

    // Copy the tree and update some random keys to cause inconsistencies.
    let mut rand = Lfsr::default();
    let n_inconsistent = (pcnt_values_inconsistent * (n_values as f64)) as usize;
    let mut t = t.clone();
    for _i in 0..n_inconsistent {
        t.upsert(rand.next().to_string(), &4242);
    }

    // Record the inconsistent/updated pages
    let _ = t.root_hash();
    let updated_pages = t.serialise_page_ranges().expect("must generate page list");

    let bench_name = BenchName {
        n_values,
        n_pages: original_pages.len(),
        pcnt_values_inconsistent,
    };

    g.throughput(Throughput::Elements(n_values as _)); // Keys per second
    g.bench_function(BenchmarkId::from(bench_name), |b| {
        b.iter_batched(
            || original_pages.clone(),
            |a| diff(a, updated_pages.clone()),
            criterion::BatchSize::PerIteration,
        );
    });
}
