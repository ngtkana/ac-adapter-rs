use fenwick::{Fenwick, Op, OpSub};
use rand::{Rng, SeedableRng, rngs::StdRng};

enum O {}
impl Op for O {
    type Value = usize;

    fn identity() -> Self::Value {
        0
    }

    fn add(a: &Self::Value, b: &Self::Value) -> Self::Value {
        a + b
    }
}
impl OpSub for O {
    fn sub(a: &Self::Value, b: &Self::Value) -> Self::Value {
        a - b
    }
}

#[derive(Debug)]
enum Query {
    Add { i: usize, x: usize },
    Sub { i: usize, x: usize },
    Sum { l: usize, r: usize },
}

#[test]
fn test_point_change_prefix_sum() {
    let mut rng = StdRng::seed_from_u64(42);

    for _ in 0..200 {
        let n = rng.gen_range(1..=10);
        let q = rng.gen_range(1..=10);
        let value_lim = usize::midpoint(n, q).max(1);

        let mut a = (0..n)
            .map(|_| rng.gen_range(0..value_lim))
            .collect::<Vec<_>>();
        let mut fen = Fenwick::<O>::new(n);
        for (i, &a) in a.iter().enumerate() {
            fen.add(i, &a);
        }

        for _ in 0..q {
            let query = match rng.gen_range(0..2) {
                0 => {
                    let i = rng.gen_range(0..n);
                    let x = rng.gen_range(0..=value_lim - a[i]);
                    Query::Add { i, x }
                }
                1 => {
                    let i = rng.gen_range(0..n);
                    let x = rng.gen_range(0..=a[i]);
                    Query::Sub { i, x }
                }
                2 => {
                    let mut l = rng.gen_range(0..=n + 1);
                    let mut r = rng.gen_range(0..=n);
                    if l > r {
                        std::mem::swap(&mut l, &mut r);
                    }
                    Query::Sum { l, r }
                }
                _ => unreachable!(),
            };
            eprintln!("a = {a:?}, {query:?}, fen = {fen:?}");

            match query {
                Query::Add { i, x } => {
                    a[i] += x;
                    fen.add(i, &x);
                }
                Query::Sub { i, x } => {
                    a[i] -= x;
                    fen.sub(i, &x);
                }
                Query::Sum { l, r } => {
                    let expected = a[l..r].iter().sum::<usize>();
                    let result = fen.fold(l..r);
                    assert_eq!(result, expected);
                }
            }
        }
    }
}
