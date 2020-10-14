#![allow(clippy::many_single_char_names)]
use crate::LazySegtree;
use alg_traits::{arith::Add, Action, Assoc, Identity};

const PROBLEM_DIR: &str = "../../../library-checker-problems/datastructure/range_affine_range_sum";

type Fp = fp2::F998244353;

#[derive(Debug, Clone, PartialEq, Copy, Eq)]
struct A {}
impl Assoc for A {
    type Value = (Fp, Fp);
    fn op((a, b): (Fp, Fp), (c, d): (Fp, Fp)) -> (Fp, Fp) {
        (a * c, a * d + b)
    }
}
impl Identity for A {
    fn identity() -> (Fp, Fp) {
        (Fp::new(1), Fp::new(0))
    }
}
impl Action for A {
    type Point = (Fp, usize);
    fn act((a, b): (Fp, Fp), (x, len): (Fp, usize)) -> (Fp, usize) {
        (a * x + b * Fp::new(len as i64), len)
    }
}

fn main(in_str: &str, out_str: &mut String) {
    let mut buf = ngtio::with_str(in_str);
    let n = buf.usize();
    let q = buf.usize();
    let a = std::iter::repeat_with(|| (Fp::new(buf.i64()), 1))
        .take(n)
        .collect::<Vec<_>>();
    let mut seg = LazySegtree::<A, (Add<Fp>, Add<usize>)>::from_slice(&a);
    for _ in 0..q {
        let command = buf.usize();
        match command {
            0 => {
                let l = buf.usize();
                let r = buf.usize();
                let b = Fp::new(buf.i64());
                let c = Fp::new(buf.i64());
                seg.apply(l..r, (b, c));
            }
            1 => {
                let l = buf.usize();
                let r = buf.usize();
                let ans: Fp = seg.fold(l..r).0;
                out_str.push_str(&format!("{}\n", ans));
            }
            _ => panic!(),
        }
    }
}

#[test]
#[ignore]
fn range_affine_range_sum() {
    yosupo::run_all(&PROBLEM_DIR, main);
}
