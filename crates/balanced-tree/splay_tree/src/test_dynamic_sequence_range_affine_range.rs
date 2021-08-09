// Library-Checer Dynamic Sequence Range Affine Range Sum
//
// https://judge.yosupo.jp/problem/dynamic_sequence_range_affine_range_sum
use {
    super::{
        brute::{test_case, Spec},
        LazyOps,
    },
    rand::{prelude::StdRng, Rng, SeedableRng},
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

fn random_value(rng: &mut StdRng) -> i64 {
    rng.gen_range(0..10)
}

fn random_lazy(rng: &mut StdRng) -> [i64; 2] {
    [rng.gen_range(1..3), rng.gen_range(0..10)]
}

#[test]
fn test_affine_insert_delete() {
    let mut rng = StdRng::seed_from_u64(42);
    let mut spec = Spec::new();
    spec.add("insert", 1);
    spec.add("delete", 1);
    spec.add("reverse", 1);
    spec.add("act", 1);
    spec.add("fold", 1);
    for _ in 0..20 {
        test_case::<Affine, _, _>(&mut rng, random_value, random_lazy, &spec);
    }
}
