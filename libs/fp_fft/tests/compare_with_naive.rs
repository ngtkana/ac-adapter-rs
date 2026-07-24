use fp::{Fp, fp, fpu};
use fp_fft::{fft, ifft};
use rand::{Rng, SeedableRng, rngs::StdRng};

const P: u64 = 998_244_353; // 2^23 * 7 * 17 + 1

#[allow(clippy::unreadable_literal)]
const DYADIC_ROOTS: [Fp<P>; 24] = [
    fp(1),         // 2^0-th root
    fp(998244352), // 2^1-th root
    fp(911660635), // 2^2-th root
    fp(372528824), // 2^3-th root
    fp(929031873), // 2^4-th root
    fp(452798380), // 2^5-th root
    fp(922799308), // 2^6-th root
    fp(781712469), // 2^7-th root
    fp(476477967), // 2^8-th root
    fp(166035806), // 2^9-th root
    fp(258648936), // 2^10-th root
    fp(584193783), // 2^11-th root
    fp(63912897),  // 2^12-th root
    fp(350007156), // 2^13-th root
    fp(666702199), // 2^14-th root
    fp(968855178), // 2^15-th root
    fp(629671588), // 2^16-th root
    fp(24514907),  // 2^17-th root
    fp(996173970), // 2^18-th root
    fp(363395222), // 2^19-th root
    fp(565042129), // 2^20-th root
    fp(733596141), // 2^21-th root
    fp(267099868), // 2^22-th root
    fp(15311432),  // 2^23-th root
];

fn ntt_naive(f: &[Fp<P>]) -> Vec<Fp<P>> {
    let n = f.len();
    assert!(n.is_power_of_two());
    if n == 1 {
        return f.to_vec();
    }
    let w = DYADIC_ROOTS[n.trailing_zeros() as usize];
    (0..n)
        .map(|i| {
            let i = i.reverse_bits() >> (n.leading_zeros() + 1);
            (0..n).map(|j| f[j] * w.pow((i * j % n) as u64)).sum()
        })
        .collect()
}

fn intt_naive(f: &[Fp<P>]) -> Vec<Fp<P>> {
    let n = f.len();
    assert!(n.is_power_of_two());
    if n == 1 {
        return f.to_vec();
    }
    let w = DYADIC_ROOTS[n.trailing_zeros() as usize].inv();
    let coeff = fpu(n).inv();
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    let j_rev = j.reverse_bits() >> (n.leading_zeros() + 1);
                    f[j_rev] * w.pow((i * j % n) as u64)
                })
                .sum::<Fp<_>>()
                * coeff
        })
        .collect()
}

#[test]
fn test_fft_len_1() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let x = fp::<P>(rng.gen_range(0..P));
        let mut f = [x];
        fft(&mut f);
        assert_eq!(f.as_slice(), &[x]);
    }
}

#[test]
fn test_ifft_len_1() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let x = fp::<P>(rng.gen_range(0..P));
        let mut f = [x];
        ifft(&mut f);
        assert_eq!(f.as_slice(), &[x]);
    }
}

#[test]
fn test_fft_len_2() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let x = fp::<P>(rng.gen_range(0..P));
        let y = fp(rng.gen_range(0..P));
        let mut f = [x, y];
        fft(&mut f);
        assert_eq!(f.as_slice(), &[x + y, x - y]);
    }
}

#[test]
fn test_ifft_len_2() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let x = fp::<P>(rng.gen_range(0..P));
        let y = fp(rng.gen_range(0..P));
        let mut f = [x, y];
        ifft(&mut f);
        assert_eq!(f.as_slice(), &[(x + y) / fp(2), (x - y) / fp(2)]);
    }
}

#[test]
fn test_fft_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        let lg = rng.gen_range(0..=6);
        let n = 1 << lg;
        let f = (0..n).map(|_| fp(rng.gen_range(0..P))).collect::<Vec<_>>();

        let mut result = f.clone();
        fft(&mut result);
        let expected = ntt_naive(&f);
        assert_eq!(&result, &expected, "f = {f:?}");

        let sum = f.iter().sum::<Fp<_>>();
        assert_eq!(result[0], sum);
        if 2 <= n {
            let alternative_sum = (0..n).map(|i| if i % 2 == 0 { f[i] } else { -f[i] }).sum();
            assert_eq!(result[1], alternative_sum);
        }
    }
}

#[test]
fn test_ifft_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        let lg = rng.gen_range(0..=6);
        let n = 1 << lg;
        let f = (0..n)
            .map(|_| fp(rng.gen_range(0..4) * 16))
            .collect::<Vec<_>>();

        let mut result = f.clone();
        ifft(&mut result);
        let expected = intt_naive(&f);
        assert_eq!(&result, &expected, "f = {f:?}");

        let sum = f.iter().sum::<Fp<_>>() / fpu(n);
        assert_eq!(result[0], sum);
        if 2 <= n {
            let (former, latter) = f.split_at(n / 2);
            let alternative_sum = former.iter().sum::<Fp<_>>() - latter.iter().sum::<Fp<_>>();
            assert_eq!(result[n / 2], alternative_sum / fpu(n));
        }
    }
}
