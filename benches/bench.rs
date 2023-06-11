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
    generate_root(&mut g, "u64", 10_000, |rand| rand as u64);
    generate_root(&mut g, "string_36", 10_000, |rand| format!("{rand:0>36}"));
}

fn insert_param<F, T>(
    g: &mut BenchmarkGroup<'_, WallTime>,
    name: &str,
    n_values: usize,
    make_value: F,
) where
    F: Fn(u16) -> T,
    T: PartialOrd + Eq + Clone + Hash + 'static,
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
                t.upsert(v.clone(), &42);
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
    T: PartialOrd + Eq + Clone + Hash + 'static,
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
