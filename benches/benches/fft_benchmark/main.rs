use criterion::black_box;
use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use fp::fpu;
use fp_fft::build_twiddle_factors_forward;
use fp_fft::fft;
use fp_fft::fft_with_twiddle_factors;

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

fn fft_with_twiddle_factors_bench_2_23(c: &mut Criterion) {
    c.bench_function("fft_with_twiddle_factors_1^23", |b| {
        let data: Vec<_> = (0..1 << 23).map(fpu::<P>).collect();

        let twiddle_factors = build_twiddle_factors_forward(1 << 23);
        b.iter(|| {
            let mut work = black_box(data.clone());
            fft_with_twiddle_factors(&mut work, &twiddle_factors);
        });
    });
}

fn build_twiddle_factors_bench_2_23(c: &mut Criterion) {
    c.bench_function("build_twiddle_factors_1^23", |b| {
        b.iter(|| {
            let work = black_box(1 << 23);
            let _ = build_twiddle_factors_forward::<P>(work);
        });
    });
}

criterion_group!(
    benches,
    fft_bench_2_23,
    fft_with_twiddle_factors_bench_2_23,
    build_twiddle_factors_bench_2_23,
);
criterion_main!(benches);
