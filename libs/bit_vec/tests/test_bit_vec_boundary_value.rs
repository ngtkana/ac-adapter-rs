use bit_vec::BitVec;
use rand::{rngs::StdRng, Rng, SeedableRng};
use rand_range::RngRange;

const BOUNDARY_VALUES: [usize; 11] = [0, 1, 63, 64, 65, 127, 128, 129, 191, 192, 193];

fn gen_bit_vec_range(mut rng: impl Rng) -> (Vec<bool>, BitVec, usize, usize) {
    let [start, end, n] = rng.gen_range_many(0..BOUNDARY_VALUES.len());
    let start = BOUNDARY_VALUES[start];
    let end = BOUNDARY_VALUES[end];
    let n = BOUNDARY_VALUES[n];
    let a = (0..n).map(|_| rng.gen_bool(0.5)).collect::<Vec<_>>();
    let bv = a.iter().copied().collect::<BitVec>();
    (a, bv, start, end)
}

#[test]
fn test_count_ones() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..1000 {
        let (vec, bv, start, end) = gen_bit_vec_range(&mut rng);

        let result = vec[start..end].iter().filter(|&&b| b).count();
        let expected = bv.range(start..end).count_ones();

        assert_eq!(result, expected, "a = {bv}[{start}..{end}]");
    }
}

#[test]
fn test_flip() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..1000 {
        let (mut vec, mut bv, start, end) = gen_bit_vec_range(&mut rng);

        for b in &mut vec[start..end] {
            *b ^= true;
        }
        bv.range_mut(start..end).flip();

        assert_eq!(vec, bv.collect_vec(), "a = {bv}[{start}..{end}]");
    }
}

#[test]
fn test_or_assign() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..1000 {
        let (mut a_vec, mut a_bv, a_start, a_end) = gen_bit_vec_range(&mut rng);
        let (b_vec, b_bv, b_start, b_end) = gen_bit_vec_range(&mut rng);

        for (a, &b) in a_vec[a_start..a_end].iter_mut().zip(&b_vec[b_start..b_end]) {
            *a |= b;
        }

        a_bv.range_mut(a_start..a_end)
            .or_assign(b_bv.range(b_start..b_end));

        let result = a_vec;
        let expected = a_bv.collect_vec();

        assert_eq!(
            result, expected,
            "a = {a_bv}[{a_start}..{a_end}], b = {b_bv}[{b_start}..{b_end}]"
        );
    }
}

#[test]
fn test_xor_assign() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..1000 {
        let (mut a_vec, mut a_bv, a_start, a_end) = gen_bit_vec_range(&mut rng);
        let (b_vec, b_bv, b_start, b_end) = gen_bit_vec_range(&mut rng);

        for (a, &b) in a_vec[a_start..a_end].iter_mut().zip(&b_vec[b_start..b_end]) {
            *a ^= b;
        }

        a_bv.range_mut(a_start..a_end)
            .xor_assign(b_bv.range(b_start..b_end));

        let result = a_vec;
        let expected = a_bv.collect_vec();

        assert_eq!(
            result, expected,
            "a = {a_bv}[{a_start}..{a_end}], b = {b_bv}[{b_start}..{b_end}]"
        );
    }
}
