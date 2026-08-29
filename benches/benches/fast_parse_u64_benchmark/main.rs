use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use parse_int::fast_parse_u64;

// テストケース: 10桁と20桁（短い・長い数字の代表）
const TEST_CASES: &[(&str, &str)] = &[
    ("10_digits", "1234567890"),
    ("20_digits", "12345678901234567890"),
];

fn benchmark_fast_parse_u64(c: &mut Criterion) {
    let mut group = c.benchmark_group("fast_parse_u64");

    for (label, value) in TEST_CASES {
        group.bench_with_input(
            BenchmarkId::from_parameter(label),
            value,
            |b, &value| {
                b.iter(|| {
                    for _ in 0..10_000 {
                        black_box(fast_parse_u64(black_box(value.as_bytes())));
                    }
                });
            },
        );
    }
    group.finish();
}

fn benchmark_std_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("std_parse_u64");

    for (label, value) in TEST_CASES {
        group.bench_with_input(
            BenchmarkId::from_parameter(label),
            value,
            |b, &value| {
                b.iter(|| {
                    for _ in 0..10_000 {
                        black_box(value.parse::<u64>().unwrap());
                    }
                });
            },
        );
    }
    group.finish();
}

criterion_group!(benches, benchmark_fast_parse_u64, benchmark_std_parse);
criterion_main!(benches);
