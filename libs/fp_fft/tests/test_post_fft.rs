use fp::{Fp, fp};
use fp_fft::{fft, ifft, split_fft};
use rand::{Rng, SeedableRng, prelude::Distribution, rngs::StdRng};

const P: u64 = 998_244_353;

struct FpHomogeneous;
impl Distribution<Fp<P>> for FpHomogeneous {
    fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Fp<P> {
        fp(rng.gen_range(0..P))
    }
}

fn naive_split_fft(f: &mut [Fp<P>]) {
    let len = f.len();
    assert!(len.is_power_of_two());
    ifft(f);
    fft(&mut f[..len / 2]);
    fft(&mut f[len / 2..]);
}

#[test]
fn test_mask_lower_part_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        let lg = rng.gen_range(1..=6);
        let n = 1 << lg;
        let data: Vec<_> = (&mut rng).sample_iter(FpHomogeneous).take(n).collect();

        let mut expected = data.clone();
        let mut result = data.clone();

        naive_split_fft(&mut expected);
        split_fft(&mut result);

        assert_eq!(result, expected, "size: {n}, data: {data:?}");
    }
}
