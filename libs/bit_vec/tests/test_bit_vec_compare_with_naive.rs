use bit_vec::BitVec;
use rand::{rngs::StdRng, Rng, SeedableRng};

fn or_shift_convolution_with_zero_naive(items: &mut [bool], shift: &[usize]) {
    for i in (0..items.len()).rev() {
        let value = items[i];
        for shift in shift {
            if i + shift < items.len() {
                items[i + shift] |= value;
            }
        }
    }
}

#[test]
fn test_or_shift_convolution_with_zero() {
    let mut rng = StdRng::seed_from_u64(42);

    for _ in 0..200 {
        let n = rng.gen_range(0..=200);
        let shift_count = 1;
        let shift = (0..shift_count)
            .map(|_| rng.gen_range(1..200))
            .collect::<Vec<_>>();

        let items = (0..n).map(|_| rng.gen_ratio(1, 2)).collect::<Vec<_>>();

        let mut bit_vec: BitVec = items.iter().copied().collect();

        let mut result = items.clone();
        or_shift_convolution_with_zero_naive(&mut result, &shift);

        bit_vec.or_shift_convolution_with_zero(&shift);
        let expected = bit_vec.collect_vec();

        assert_eq!(result, expected, "items = {items:?}, shift = {shift:?}");
    }
}
