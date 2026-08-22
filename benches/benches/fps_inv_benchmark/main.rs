use criterion::black_box;
use criterion::criterion_group;
use criterion::criterion_main;
use criterion::Criterion;
use fp::fp_new;
use fp::Fp;
use fp_fps::fps_inv;

const P: u64 = 998_244_353;

fn fps_inv_bench_2_20(c: &mut Criterion) {
    c.bench_function("fps_inv_2^20", |b| {
        let mut f: Vec<Fp<P>> = (0..1 << 20).map(|i| fp_new((i + 1) as u64)).collect();
        f[0] = fp_new(1);
        let precision = 1 << 20;

        b.iter(|| fps_inv(black_box(&f), precision));
    });
}

criterion_group!(benches, fps_inv_bench_2_20);
criterion_main!(benches);
