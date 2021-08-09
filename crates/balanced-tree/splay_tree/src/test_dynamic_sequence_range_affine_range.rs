use {
    super::{LazyOps, SplayTree},
    itertools::Itertools,
    rand::{prelude::StdRng, Rng, SeedableRng},
    std::{iter::repeat_with, mem::swap},
};

const P: i64 = 998_244_353;

enum Affine {}
impl LazyOps for Affine {
    type Value = i64;
    type Acc = (i64, usize);
    type Lazy = [i64; 2];
    fn proj(&value: &Self::Value) -> Self::Acc {
        (value, 1)
    }
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc {
        ((lhs.0 + rhs.0) % P, lhs.1 + rhs.1)
    }
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value) {
        *value = (lazy[0] * *value + lazy[1]) % P;
    }
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc) {
        acc.0 = (lazy[0] * acc.0 + lazy[1] * acc.1 as i64) % P;
    }
    fn compose(upper: &Self::Lazy, lower: &mut Self::Lazy) {
        *lower = [
            (upper[0] * lower[0]) % P,
            (upper[0] * lower[1] + upper[1]) % P,
        ];
    }
}

#[test]
fn test_dynamic_sequence_range_affine_range() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let n = rng.gen_range(2..10);
        let mut brute = repeat_with(|| rng.gen_range(0..P)).take(n).collect_vec();
        let mut splay = brute.iter().copied().collect::<SplayTree<Affine>>();
        for _ in 0..200 {
            match rng.gen_range(0..5) {
                0 => {
                    let i = rng.gen_range(0..=brute.len());
                    let value = rng.gen_range(0..P);
                    brute.insert(i, value);
                    splay.insert(i, value);
                }
                1 => {
                    if brute.is_empty() {
                        continue;
                    }
                    let i = rng.gen_range(0..brute.len());
                    brute.remove(i);
                    splay.delete(i);
                }
                2 => {
                    if brute.len() < 2 {
                        continue;
                    }
                    let mut start = rng.gen_range(0..brute.len());
                    let mut end = rng.gen_range(0..brute.len() - 1);
                    if start >= end {
                        swap(&mut start, &mut end);
                        end += 1;
                    }
                    brute[start..end].reverse();
                    splay.reverse(start..end);
                }
                3 => {
                    if brute.len() < 2 {
                        continue;
                    }
                    let mut start = rng.gen_range(0..brute.len());
                    let mut end = rng.gen_range(0..brute.len() - 1);
                    if start >= end {
                        swap(&mut start, &mut end);
                        end += 1;
                    }
                    let b = rng.gen_range(0..P);
                    let c = rng.gen_range(0..P);
                    brute[start..end]
                        .iter_mut()
                        .for_each(|x| *x = ((b * *x) + c) % P);
                    splay.act(start..end, [b, c]);
                }
                4 => {
                    if brute.len() < 2 {
                        continue;
                    }
                    let mut start = rng.gen_range(0..brute.len());
                    let mut end = rng.gen_range(0..brute.len() - 1);
                    if start >= end {
                        swap(&mut start, &mut end);
                        end += 1;
                    }
                    let expected = brute[start..end].iter().fold(0, |acc, &x| (acc + x) % P);
                    let result = splay.fold(start..end).unwrap().0;
                    assert_eq!(expected, result);
                }
                _ => unreachable!(),
            }
        }
    }
}
