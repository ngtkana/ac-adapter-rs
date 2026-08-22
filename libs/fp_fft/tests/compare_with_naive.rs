use fp::Fp;
use fp::fp_new;
use fp::fpu;
use fp_fft::fft;
use fp_fft::ifft;
use rand::Rng;
use rand::SeedableRng;
use rand::prelude::Distribution;
use rand::rngs::StdRng;

const P: u64 = 998_244_353; // 2^23 * 7 * 17 + 1

struct FpHomogeneous;
impl Distribution<Fp<P>> for FpHomogeneous {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Fp<P> {
        fp_new(rng.gen_range(0..P))
    }
}

#[allow(clippy::unreadable_literal)]
const EXPECTED_DIADIC_ROOTS: [Fp<P>; 24] = [
    fp_new(1),         // 2^0-th root
    fp_new(998244352), // 2^1-th root
    fp_new(911660635), // 2^2-th root
    fp_new(372528824), // 2^3-th root
    fp_new(929031873), // 2^4-th root
    fp_new(452798380), // 2^5-th root
    fp_new(922799308), // 2^6-th root
    fp_new(781712469), // 2^7-th root
    fp_new(476477967), // 2^8-th root
    fp_new(166035806), // 2^9-th root
    fp_new(258648936), // 2^10-th root
    fp_new(584193783), // 2^11-th root
    fp_new(63912897),  // 2^12-th root
    fp_new(350007156), // 2^13-th root
    fp_new(666702199), // 2^14-th root
    fp_new(968855178), // 2^15-th root
    fp_new(629671588), // 2^16-th root
    fp_new(24514907),  // 2^17-th root
    fp_new(996173970), // 2^18-th root
    fp_new(363395222), // 2^19-th root
    fp_new(565042129), // 2^20-th root
    fp_new(733596141), // 2^21-th root
    fp_new(267099868), // 2^22-th root
    fp_new(15311432),  // 2^23-th root
];

fn ntt_naive(f: &[Fp<P>]) -> Vec<Fp<P>> {
    let n = f.len();
    assert!(n.is_power_of_two());
    if n == 1 {
        return f.to_vec();
    }
    let w = EXPECTED_DIADIC_ROOTS[n.trailing_zeros() as usize];
    (0..n)
        .map(|i| {
            let i = i.reverse_bits() >> (n.leading_zeros() + 1);
            (0..n).map(|j| f[j] * w.pow((i * j % n) as u64)).sum()
        })
        .collect()
}

fn iftt_naive(f: &[Fp<P>]) -> Vec<Fp<P>> {
    let n = f.len();
    assert!(n.is_power_of_two());
    if n == 1 {
        return f.to_vec();
    }
    let w = EXPECTED_DIADIC_ROOTS[n.trailing_zeros() as usize].inv();
    let n_inv = fpu(n).inv();
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    let j_rev = j.reverse_bits() >> (n.leading_zeros() + 1);
                    f[j_rev] * w.pow((i * j % n) as u64)
                })
                .sum::<Fp<_>>()
                * n_inv
        })
        .collect()
}

#[test]
fn test_fft_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        let lg = rng.gen_range(0..=6);
        let n = 1 << lg;
        let f = (&mut rng)
            .sample_iter(FpHomogeneous)
            .take(n)
            .collect::<Vec<_>>();

        let mut result = f.clone();
        fft(&mut result);
        let expected = ntt_naive(&f);
        assert_eq!(&result, &expected, "f = {f:?}");
    }
}

#[test]
fn test_ifft_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        let lg = rng.gen_range(0..=6);
        let n = 1 << lg;
        let f = (&mut rng)
            .sample_iter(FpHomogeneous)
            .take(n)
            .collect::<Vec<_>>();

        let mut result = f.clone();
        ifft(&mut result);
        let expected = iftt_naive(&f);
        assert_eq!(&result, &expected, "f = {f:?}");
    }
}
