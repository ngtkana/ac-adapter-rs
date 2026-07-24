use fp::{Fp, fp};
use fp_fps::{poly_mul, fps_inv};
use rand::{Rng, SeedableRng, prelude::Distribution, rngs::StdRng};

const P: u64 = 998_244_353;

struct FpHomogeneous;
impl Distribution<Fp<P>> for FpHomogeneous {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Fp<P> {
        fp(rng.gen_range(0..P))
    }
}

fn naive_fps_inv(f: &[Fp<P>], precision: usize) -> Vec<Fp<P>> {
    let mut g = vec![fp(0); precision];
    g[0] = f[0].inv();
    for i in 1..precision {
        let mut sum = fp(0);
        for j in 1..=i.min(f.len() - 1) {
            sum += f[j] * g[i - j];
        }
        g[i] = -sum * f[0].inv();
    }
    g
}

fn naive_poly_mul(f: &[Fp<P>], g: &[Fp<P>]) -> Vec<Fp<P>> {
    if f.is_empty() {
        return g.to_vec();
    }
    if g.is_empty() {
        return f.to_vec();
    }
    let mut h = vec![fp(0); f.len() + g.len() - 1];
    for (i, f) in f.iter().enumerate() {
        for (j, g) in g.iter().enumerate() {
            h[i + j] += *f * *g;
        }
    }
    h
}

#[allow(dead_code)]
fn naive_poly_div_rem(mut a: Vec<Fp<P>>, b: &[Fp<P>]) -> (Vec<Fp<P>>, Vec<Fp<P>>) {
    assert_ne!(*b.last().unwrap(), fp(0));
    if a.len() < b.len() {
        return (vec![], a);
    }
    let blinv = b.last().unwrap().inv();
    let mut q = vec![fp(0); a.len() - b.len() + 1];
    for i in (0..=a.len() - b.len()).rev() {
        q[i] = a[i + b.len() - 1] * blinv;
        for (a, b) in a[i..].iter_mut().zip(b) {
            *a -= *b * q[i];
        }
        assert_eq!(a[i + b.len() - 1], fp(0));
    }
    while a.pop_if(|a| *a == fp(0)).is_some() {}
    (q, a)
}

#[allow(dead_code)]
fn naive_multipoint_evaluation<const P: u64>(f: &[Fp<P>], points: &[Fp<P>]) -> Vec<Fp<P>> {
    points
        .iter()
        .map(|&x| {
            let mut state = fp(1);
            let mut result = fp(0);
            for &f in f {
                result += f * state;
                state *= x;
            }
            result
        })
        .collect()
}

#[test]
fn test_poly_mul_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..100 {
        let a_len = rng.gen_range(1..=6);
        let b_len = rng.gen_range(1..=6);
        let a: Vec<_> = (&mut rng)
            .sample_iter(FpHomogeneous)
            .take(a_len)
            .collect();
        let b: Vec<_> = (&mut rng)
            .sample_iter(FpHomogeneous)
            .take(b_len)
            .collect();

        let result = poly_mul(a.clone(), b.clone());
        let expected = naive_poly_mul(&a, &b);
        assert_eq!(result, expected, "a = {a:?}, b = {b:?}");
    }
}

#[test]
fn test_poly_mul_power_of_two_sizes() {
    let mut rng = StdRng::seed_from_u64(42);
    for lg_a in 0..=5 {
        for lg_b in 0..=5 {
            let a: Vec<_> = (&mut rng)
                .sample_iter(FpHomogeneous)
                .take(1 << lg_a)
                .collect();
            let b: Vec<_> = (&mut rng)
                .sample_iter(FpHomogeneous)
                .take(1 << lg_b)
                .collect();

            let result = poly_mul(a.clone(), b.clone());
            let expected = naive_poly_mul(&a, &b);
            assert_eq!(result, expected, "2^{lg_a} * 2^{lg_b}");
        }
    }
}

#[test]
fn test_fps_inv_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..100 {
        let f_len = 1 << rng.gen_range(0..=4);
        let mut f: Vec<_> = (&mut rng)
            .sample_iter(FpHomogeneous)
            .take(f_len)
            .collect();

        f[0] = fp(rng.gen_range(1..P));
        let precision = rng.gen_range(1..=8);

        let result = fps_inv(&f, precision);
        let expected = naive_fps_inv(&f, precision);
        assert_eq!(result, expected, "f[0] = {}, precision = {}", f[0], precision);
    }
}

#[test]
fn test_fps_inv_inverse_property() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..50 {
        let mut f: Vec<_> = (&mut rng)
            .sample_iter(FpHomogeneous)
            .take(1 << 4)
            .collect();
        f[0] = fp(rng.gen_range(1..P));

        let precision = 1 << 4;
        let inv = fps_inv(&f, precision);

        let product = poly_mul(f[..precision].to_vec(), inv);

        for (i, &val) in product.iter().enumerate() {
            if i == 0 {
                assert_eq!(val, fp(1), "Product[0] should be 1, f[0] = {}", f[0]);
            } else if i < precision {
                assert_eq!(val, fp(0), "Product[{i}] should be 0");
            }
        }
    }
}
