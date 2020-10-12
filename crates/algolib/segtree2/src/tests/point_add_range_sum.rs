use crate::Segtree;
use alg_traits::arith::Add;

const PROBLEM_DIR: &'static str =
    "../../../library-checker-problems/datastructure/point_add_range_sum";

fn main(in_str: &str, out_str: &mut String) {
    let mut buf = ngtio::with_str(in_str);
    let n = buf.usize();
    let q = buf.usize();
    let a = buf.vec::<u64>(n);
    let mut seg = Segtree::<Add<_>>::from_slice(&a);
    for _ in 0..q {
        let command = buf.usize();
        match command {
            0 => {
                let i = buf.usize();
                let x = buf.u64();
                let x = x + seg.fold(i..i + 1);
                seg.set(i, x);
            }
            1 => {
                let l = buf.usize();
                let r = buf.usize();
                let ans = seg.fold(l..r);
                out_str.push_str(&format!("{}\n", ans));
            }
            _ => panic!(),
        }
    }
}

#[test]
#[ignore]
fn point_add_range_sum() {
    yosupo::run_all(&PROBLEM_DIR, main);
}
