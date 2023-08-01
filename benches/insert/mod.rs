use std::hash::Hash;

use criterion::{
    measurement::WallTime, BatchSize, BenchmarkGroup, BenchmarkId, Criterion, Throughput,
};
use merkle_search_tree::MerkleSearchTree;

use crate::{Lfsr, ROW_COUNTS};

struct BenchName {
    input_type_desc: &'static str,
    values_inserted: usize,
}

impl From<BenchName> for BenchmarkId {
    fn from(v: BenchName) -> Self {
        Self::new(v.input_type_desc, format!("{}_keys", v.values_inserted))
    }
}

pub(super) fn bench_insert(c: &mut Criterion) {
    let mut g = c.benchmark_group("insert");

    // U64 values
    for &n_values in ROW_COUNTS {
        insert_param(&mut g, "u64", n_values, |rand| rand as u64);
    }

    // 36 byte strings (same as UUIDs)
    for &n_values in ROW_COUNTS {
        insert_param(&mut g, "uuid_string", n_values, |rand| {
            format!("{rand:0>36}")
        });
    }
}

fn insert_param<F, T>(
    g: &mut BenchmarkGroup<'_, WallTime>,
    name: &'static str,
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

    let bench_name = BenchName {
        input_type_desc: name,
        values_inserted: n_values,
    };

    g.throughput(Throughput::Elements(n_values as _));
    g.bench_with_input(BenchmarkId::from(bench_name), &values, |b, values| {
        b.iter_batched(
            || (*values).clone(),
            |values| {
                let mut t = MerkleSearchTree::default();
                for v in values {
                    t.upsert(v, &42);
                }
            },
            BatchSize::PerIteration,
        );
    });
}
