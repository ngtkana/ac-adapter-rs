use cht::{BTreeCht, Concave, ConvexOrConcave, Convex, Quadratic, VecCht, X};
use rand::{rngs::StdRng, Rng, SeedableRng};

fn brute_max(brute: &[Quadratic], x: i64) -> i64 {
    brute.iter().map(|&q| q.eval(x)).max().unwrap()
}
fn brute_min(brute: &[Quadratic], x: i64) -> i64 {
    brute.iter().map(|&q| q.eval(x)).min().unwrap()
}

// Boundary-cursor regression test: zero coefficients so evaluation itself
// never overflows, letting us safely probe i64::MIN / i64::MAX.
#[test]
fn boundary_cursor_vec_cht() {
    let mut cht = VecCht::<Convex>::new();
    cht.add(Quadratic::from(0));
    cht.add(Quadratic::from(1));
    cht.add(Quadratic::from(-1));
    for &x in &[i64::MIN, i64::MIN + 1, 0, i64::MAX - 1, i64::MAX] {
        assert_eq!(cht.eval(x), 1, "x={x}");
    }
}

#[test]
fn boundary_cursor_btree_cht() {
    let mut cht = BTreeCht::<Convex>::new();
    cht.add(Quadratic::from(0));
    cht.add(Quadratic::from(1));
    cht.add(Quadratic::from(-1));
    for &x in &[i64::MIN, i64::MIN + 1, 0, i64::MAX - 1, i64::MAX] {
        assert_eq!(cht.eval(x), 1, "x={x}");
    }
}

#[test]
fn fuzz_vec_cht_random_order_queries_convex() {
    let mut rng = StdRng::seed_from_u64(999);
    for im in [1_i64, 2, 3, 5, 8, 13, 20, 50, 100, 1000] {
        let mut cht = VecCht::<Convex>::new();
        let mut brute = Vec::new();
        let second = rng.gen_range(-im..=im);
        // VecCht requires insertion sorted by slope (first-degree coeff).
        let mut qs: Vec<Quadratic> = (0..40)
            .map(|_| {
                Quadratic::from(rng.gen_range(-im..=im))
                    + rng.gen_range(-im..=im) * X
                    + second * (X * X)
            })
            .collect();
        qs.sort_by_key(|q| q.eval(1) - q.eval(0));
        for q in qs {
            cht.add(q);
            brute.push(q);

            // random-order (non-monotonic) queries
            let xs: Vec<i64> = (0..30).map(|_| rng.gen_range(-im * 5..=im * 5)).collect();
            for &x in &xs {
                let got = cht.eval(x);
                let want = brute_max(&brute, x);
                assert_eq!(got, want, "x={x}, im={im}");
            }
        }
    }
}

#[test]
fn fuzz_vec_cht_random_order_queries_concave() {
    let mut rng = StdRng::seed_from_u64(1000);
    for im in [1_i64, 2, 3, 5, 8, 13, 20, 50, 100, 1000] {
        let mut cht = VecCht::<Concave>::new();
        let mut brute = Vec::new();
        let second = rng.gen_range(-im..=im);
        let mut qs: Vec<Quadratic> = (0..40)
            .map(|_| {
                Quadratic::from(rng.gen_range(-im..=im))
                    + rng.gen_range(-im..=im) * X
                    + second * (X * X)
            })
            .collect();
        qs.sort_by_key(|q| Concave::negate_if_concave(q.eval(1) - q.eval(0)));
        for q in qs {
            cht.add(q);
            brute.push(q);

            let xs: Vec<i64> = (0..30).map(|_| rng.gen_range(-im * 5..=im * 5)).collect();
            for &x in &xs {
                let got = cht.eval(x);
                let want = brute_min(&brute, x);
                assert_eq!(got, want, "x={x}, im={im}");
            }
        }
    }
}

#[test]
fn fuzz_btree_cht_random_order_queries() {
    let mut rng = StdRng::seed_from_u64(1001);
    for im in [1_i64, 2, 3, 5, 8, 13, 20, 50, 100, 1000] {
        let mut cht = BTreeCht::<Convex>::new();
        let mut brute = Vec::new();
        let second = rng.gen_range(-im..=im);
        for _ in 0..40 {
            let q = Quadratic::from(rng.gen_range(-im..=im))
                + rng.gen_range(-im..=im) * X
                + second * (X * X);
            cht.add(q);
            brute.push(q);

            let xs: Vec<i64> = (0..30).map(|_| rng.gen_range(-im * 5..=im * 5)).collect();
            for &x in &xs {
                let got = cht.eval(x);
                let want = brute_max(&brute, x);
                assert_eq!(got, want, "x={x}, im={im}");
            }
        }
    }
}
