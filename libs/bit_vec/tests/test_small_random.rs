use bit_vec::BitVec;
use rand::{rngs::StdRng, Rng, SeedableRng};
use rand_range::RngRange;

// A probability distribution where the values
// 64q±1 appear with high frequency.
fn gen_range_many(rng: &mut impl Rng, max_len: usize) -> [usize; 3] {
    let mut weight = vec![1; max_len + 1];
    for i in [0, 1]
        .into_iter()
        .chain((1..).flat_map(|q| [q * 64 - 1, q * 64, q * 64 + 1]))
        .take_while(|&i| i <= max_len)
    {
        weight[i] = 20;
    }
    for i in 1..=max_len {
        weight[i] += weight[i - 1];
    }
    let [start, end, len] = rng.gen_range_many(0..weight[max_len]);
    [
        weight.iter().position(|&w| start < w).unwrap(),
        weight.iter().position(|&w| end < w).unwrap(),
        weight.iter().position(|&w| len < w).unwrap(),
    ]
}

#[test]
fn test_xor_assign_small_random() {
    let mut rng = StdRng::seed_from_u64(42);
    let testcase_number = 2_000;
    for testcase_id in 1..=testcase_number {
        let [a_start, a_end, a_len] = gen_range_many(&mut rng, 200);
        let [b_start, b_end, b_len] = gen_range_many(&mut rng, 200);

        let a = (0..a_len).map(|_| rng.gen_bool(0.5)).collect::<Vec<_>>();
        let b = (0..b_len).map(|_| rng.gen_bool(0.5)).collect::<Vec<_>>();

        let mut a_changed = a.clone();
        for (x, &y) in a_changed[a_start..a_end].iter_mut().zip(&b[b_start..b_end]) {
            *x ^= y;
        }

        let mut a_bv = a.iter().copied().collect::<BitVec>();
        let b_bv = b.iter().copied().collect::<BitVec>();

        let mut a_range = a_bv.range_mut(a_start..a_end);
        let b_range = b_bv.range(b_start..b_end);

        eprint!(
            "Testcase {testcase_id}/{testcase_number}:\n\
            a[0..{a_len}][{a_start}..{a_end}]: {a},\n\
            b[0..{b_len}][{b_start}..{b_end}]: {b},\n\
            ",
            a = format_range(&a, a_start, a_end),
            b = format_range(&b, b_start, b_end),
        );

        a_range.xor_assign(b_range);

        eprint!(
            "\
            result  : {a_changed_result}\n\
            expected: {a_changed_expected}\n\
            ",
            a_changed_result = format_range(&a_changed, a_start, a_end),
            a_changed_expected = format_range(&a_bv.iter().collect::<Vec<_>>(), a_start, a_end),
        );

        for i in 0..a.len() {
            let result = a_bv.get(i);
            let expected = a_changed[i];
            assert_eq!(result, expected, "{i}-th bit differs");
        }
        eprintln!();
    }
}

#[test]
fn test_or_assign_small_random() {
    let mut rng = StdRng::seed_from_u64(42);
    let testcase_number = 2_000;
    for testcase_id in 1..=testcase_number {
        let [a_start, a_end, a_len] = gen_range_many(&mut rng, 200);
        let [b_start, b_end, b_len] = gen_range_many(&mut rng, 200);

        let a = (0..a_len).map(|_| rng.gen_bool(0.5)).collect::<Vec<_>>();
        let b = (0..b_len).map(|_| rng.gen_bool(0.5)).collect::<Vec<_>>();

        let mut a_changed = a.clone();
        for (x, &y) in a_changed[a_start..a_end].iter_mut().zip(&b[b_start..b_end]) {
            *x |= y;
        }

        let mut a_bv = a.iter().copied().collect::<BitVec>();
        let b_bv = b.iter().copied().collect::<BitVec>();

        let mut a_range = a_bv.range_mut(a_start..a_end);
        let b_range = b_bv.range(b_start..b_end);

        eprint!(
            "Testcase {testcase_id}/{testcase_number}:\n\
            a[0..{a_len}][{a_start}..{a_end}]: {a},\n\
            b[0..{b_len}][{b_start}..{b_end}]: {b},\n\
            ",
            a = format_range(&a, a_start, a_end),
            b = format_range(&b, b_start, b_end),
        );

        a_range.or_assign(b_range);

        eprint!(
            "\
            result  : {a_changed_result}\n\
            expected: {a_changed_expected}\n\
            ",
            a_changed_result = format_range(&a_changed, a_start, a_end),
            a_changed_expected = format_range(&a_bv.iter().collect::<Vec<_>>(), a_start, a_end),
        );

        for i in 0..a.len() {
            let result = a_bv.get(i);
            let expected = a_changed[i];
            assert_eq!(result, expected, "{i}-th bit differs");
        }
        eprintln!();
    }
}

fn format_range(a: &[bool], start: usize, end: usize) -> String {
    format!(
        "{}<{}>{}",
        iter_to_string(a[..start].iter().copied()),
        iter_to_string(a[start..end].iter().copied()),
        iter_to_string(a[end..].iter().copied()),
    )
}

fn iter_to_string(iter: impl Iterator<Item = bool>) -> String {
    let mut result = String::new();
    for b in iter {
        result.push(if b { '1' } else { '0' });
    }
    result
}
