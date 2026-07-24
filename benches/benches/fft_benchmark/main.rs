use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fp::fpu;
use fp_fft::fft;

const P: u64 = 998_244_353;

fn fft_bench_2_23(c: &mut Criterion) {
    c.bench_function("fft_1^23", |b| {
        let data: Vec<_> = (0..1 << 23).map(fpu::<P>).collect();

        b.iter(|| {
            let mut work = black_box(data.clone());
            fft(&mut work);
        });
    });
}

criterion_group!(benches, fft_bench_2_23);
criterion_main!(benches);
