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
    type Acc = i64;
    type Lazy = [i64; 2];
    fn proj(&value: &Self::Value) -> Self::Acc {
        value
    }
    fn op(lhs: &Self::Value, rhs: &Self::Value) -> Self::Acc {
        (lhs + rhs) % P
    }
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value) {
        *value = (lazy[0] * *value + lazy[1]) % P;
    }
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc) {
        *acc = (lazy[0] * *acc + lazy[1]) % P;
    }
    fn lazy_propagate(upper: &Self::Lazy, lower: &mut Self::Lazy) {
        *lower = [
            (upper[0] * lower[0]) % P,
            (upper[0] * lower[1] + lower[0]) % P,
        ];
    }
}

#[test]
fn test_affine_only_get() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case::<Affine, _>(
            &mut rng,
            random_value,
            &Spec {
                get: 4,
                fold: 0,
                push_back: 0,
                push_front: 0,
                insert: 4,
                pop_back: 0,
                pop_front: 0,
                delete: 0,
            },
        );
    }
}

fn random_value(rng: &mut StdRng) -> i64 {
    rng.gen_range(0..10)
}

#[test]
fn test_affine_insert_delete() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case::<Affine, _>(
            &mut rng,
            random_value,
            &Spec {
                get: 4,
                fold: 2,
                insert: 1,
                delete: 2,
                ..Spec::default()
            },
        );
    }
}

#[test]
fn test_affine_push_pop() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case::<Affine, _>(
            &mut rng,
            random_value,
            &Spec {
                get: 4,
                fold: 2,
                push_back: 2,
                push_front: 2,
                pop_back: 1,
                pop_front: 1,
                ..Spec::default()
            },
        );
    }
}

#[test]
fn test_affine_typical_queries_many_push() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case::<Affine, _>(
            &mut rng,
            random_value,
            &Spec {
                get: 4,
                fold: 2,
                push_back: 2,
                push_front: 2,
                insert: 2,
                pop_back: 1,
                pop_front: 1,
                delete: 1,
            },
        );
    }
}
