use fp::Fp;
use fp::fp_new;
use fp_precalc::Precalc;
use rand::Rng;
use rand::SeedableRng;
use rand::rngs::StdRng;

const P: u64 = 998_244_353;

fn fact_naive(n: usize) -> Fp<P> {
    (1..=n).fold(fp_new(1), |acc, i| acc * fp_new(i as u64))
}

fn inv_fact_naive(n: usize) -> Fp<P> {
    fact_naive(n).inv()
}

fn binom_naive(n: usize, k: usize) -> Fp<P> {
    if k > n {
        return fp_new(0);
    }
    fact_naive(n) * inv_fact_naive(k) * inv_fact_naive(n - k)
}

#[test]
fn test_fact_compare_with_naive() {
    let size = 500;
    let precalc = Precalc::<P>::new(size).build_fact();

    for n in 0..size {
        let result = precalc.fact(n);
        let expected = fact_naive(n);
        assert_eq!(result, expected, "fact({n})");
    }
}

#[test]
fn test_finv_compare_with_naive() {
    let size = 500;
    let precalc = Precalc::<P>::new(size).build_fact().build_finv_using_fact();

    for n in 0..size {
        let result = precalc.finv(n);
        let expected = inv_fact_naive(n);
        assert_eq!(result, expected, "finv({n})");
    }
}

#[test]
fn test_binom_compare_with_naive() {
    let size = 20;
    let precalc = Precalc::<P>::new(size).build_fact().build_finv_using_fact();

    for n in 0..size {
        for k in 0..=n {
            let result = precalc.binom(n, k);
            let expected = binom_naive(n, k);
            assert_eq!(result, expected, "binom({n}, {k})");
        }
    }
}

#[test]
fn test_binom_random_samples() {
    let mut rng = StdRng::seed_from_u64(42);
    let size = 500;
    let precalc = Precalc::<P>::new(size).build_fact().build_finv_using_fact();

    for _ in 0..200 {
        let n = rng.gen_range(0..size);
        let k = rng.gen_range(0..=n);

        let result = precalc.binom(n, k);
        let expected = binom_naive(n, k);
        assert_eq!(result, expected, "random: binom({n}, {k})");
    }
}

#[test]
fn test_inv_compare_with_naive() {
    let size = 500;
    let precalc = Precalc::<P>::new(size).build_inv();

    for n in 1..size {
        let result = precalc.inv(n);
        let expected = fp_new(n as u64).inv();
        assert_eq!(result, expected, "inv({n})");
    }
}

#[test]
fn test_finv_using_inv() {
    let size = 500;
    let precalc_fact = Precalc::<P>::new(size)
        .build_fact()
        .build_inv()
        .build_finv_using_inv();

    for n in 0..size {
        let result = precalc_fact.finv(n);
        let expected = inv_fact_naive(n);
        assert_eq!(result, expected, "finv_using_inv({n})");
    }
}
