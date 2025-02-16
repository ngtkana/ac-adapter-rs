mod eratosthenes;
mod modulo_six;

use criterion::{criterion_group, criterion_main, Criterion};
use std::hint::black_box;

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("eratosthenes::build_sieve(1_000_000)", |b| {
        b.iter(|| eratosthenes::build_sieve(black_box(1_000_000)))
    });
    c.bench_function("modulo_six::build_sieve(1_000_000)", |b| {
        b.iter(|| modulo_six::build_sieve(black_box(1_000_000)))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
