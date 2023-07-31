mod diff;
mod generate_root;
mod insert;
mod node_iter;
mod serialise_pages;

use criterion::{criterion_group, criterion_main};
use diff::bench_diff;
use generate_root::bench_generate_root;
use insert::bench_insert;
use node_iter::bench_node_iter;
use serialise_pages::bench_serialise_pages;

const ROW_COUNTS: &[usize] = &[1, 100, 1_000, 10_000, 100_000];

criterion_main!(benches);
criterion_group!(
    benches,
    bench_insert,
    bench_generate_root,
    bench_diff,
    bench_serialise_pages,
    bench_node_iter,
);

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
