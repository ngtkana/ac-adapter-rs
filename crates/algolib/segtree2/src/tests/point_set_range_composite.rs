use crate::Segtree;
use alg_traits::{Assoc, Identity};

type Fp = fp2::F998244353;

#[derive(Debug, Clone, PartialEq)]
struct X {}
impl Assoc for X {
    type Value = (Fp, Fp);
    fn op((a0, b0): Self::Value, (a1, b1): Self::Value) -> Self::Value {
        (a1 * a0, a1 * b0 + b1)
    }
}
impl Identity for X {
    fn identity() -> (Fp, Fp) {
        (Fp::new(1), Fp::new(0))
    }
}

const PROBLEM_DIR: &'static str =
    "../../../library-checker-problems/datastructure/point_set_range_composite";

fn main(in_str: &str, out_str: &mut String) {
    let mut buf = ngtio::with_str(in_str);
    let n = buf.usize();
    let q = buf.usize();
    let mut seg = Segtree::<X>::from_slice(
        &std::iter::repeat_with(|| (Fp::new(buf.i64()), Fp::new(buf.i64())))
            .take(n)
            .collect::<Vec<_>>(),
    );
    for _ in 0..q {
        let command = buf.usize();
        match command {
            0 => {
                let i = buf.usize();
                let f = (Fp::new(buf.i64()), Fp::new(buf.i64()));
                seg.set(i, f);
            }
            1 => {
                let l = buf.usize();
                let r = buf.usize();
                let x = Fp::new(buf.i64());
                let (a, b) = seg.fold(l..r);
                let ans = a * x + b;
                out_str.push_str(&format!("{}\n", ans));
            }
            _ => panic!(),
        }
    }
}

#[test]
#[ignore]
fn point_set_range_composite() {
    yosupo::run_all(&PROBLEM_DIR, main);
}
