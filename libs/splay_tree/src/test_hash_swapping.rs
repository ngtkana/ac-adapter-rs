use super::NoLazy;
use super::Ops;
use super::SplayTree;
use itertools::Itertools;
use rand::prelude::StdRng;
use rand::Rng;
use rand::SeedableRng;
use std::iter::repeat_with;
use std::mem::swap;

const P: u64 = 998_244_353;

enum StrHash {}
impl Ops for StrHash {
    type Acc = [u64; 2];
    type Value = u64;

    fn proj(&value: &Self::Value) -> Self::Acc { [value, 1_000_000] }

    fn op(&lhs: &Self::Acc, &rhs: &Self::Acc) -> Self::Acc {
        [(lhs[0] + lhs[1] * rhs[0]) % P, lhs[1] * rhs[1] % P]
    }
}

#[test]
fn test_hash_swapping() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let n = rng.gen_range(2..10);
        let m = rng.gen_range(2..10);
        let mut brute = repeat_with(|| repeat_with(|| rng.gen_range(0..26)).take(n).collect_vec())
            .take(m)
            .collect_vec();
        let mut splay = brute
            .iter()
            .map(|row| row.iter().copied().collect::<SplayTree<NoLazy<StrHash>>>())
            .collect_vec();
        for _ in 0..200 {
            match rng.gen_range(0..2) {
                0 => {
                    let i = rng.gen_range(0..m);
                    let mut j = rng.gen_range(0..m - 1);
                    if i <= j {
                        j += 1;
                    }
                    let mut start = rng.gen_range(0..n);
                    let mut end = rng.gen_range(0..n - 1);
                    if start >= end {
                        swap(&mut start, &mut end);
                        end += 1;
                    }

                    let ir = splay[i].split_off(end);
                    let ic = splay[i].split_off(start);
                    let jr = splay[j].split_off(end);
                    let jc = splay[j].split_off(start);
                    splay[i].append(&jc);
                    splay[i].append(&ir);
                    splay[j].append(&ic);
                    splay[j].append(&jr);

                    let mut ir = brute[i].split_off(end);
                    let mut ic = brute[i].split_off(start);
                    let mut jr = brute[j].split_off(end);
                    let mut jc = brute[j].split_off(start);
                    brute[i].append(&mut jc);
                    brute[i].append(&mut ir);
                    brute[j].append(&mut ic);
                    brute[j].append(&mut jr);
                }
                1 => {
                    let i = rng.gen_range(0..m);
                    let mut start = rng.gen_range(0..n);
                    let mut end = rng.gen_range(0..n - 1);
                    if start >= end {
                        swap(&mut start, &mut end);
                        end += 1;
                    }

                    let result = splay[i].fold(start..end).unwrap()[0];
                    let expected = brute[i][start..end]
                        .iter()
                        .rev()
                        .fold(0, |acc, &x| (acc * 1_000_000 + x) % P);
                    assert_eq!(result, expected);
                }
                _ => unreachable!(),
            }
        }
    }
}
