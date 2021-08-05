use {
    super::{
        brute::{test_case, Spec},
        LazyOps,
    },
    rand::{distributions::Alphanumeric, prelude::StdRng, Rng, SeedableRng},
    std::iter::once,
};

enum Cat {}
impl LazyOps for Cat {
    type Value = String;
    type Acc = String;
    type Lazy = String;
    fn proj(c: &String) -> String {
        c.clone()
    }
    fn op(lhs: &String, rhs: &String) -> String {
        lhs.chars().chain(rhs.chars()).collect()
    }
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value) {
        *value = value.chars().chain(lazy.chars()).collect()
    }
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc) {
        *acc = acc.chars().chain(lazy.chars()).collect()
    }
    fn lazy_propagate(upper: &Self::Lazy, lower: &mut Self::Lazy) {
        *lower = lower.chars().chain(upper.chars()).collect();
    }
}

fn random_value(rng: &mut StdRng) -> String {
    once(rng.sample(Alphanumeric) as char).collect()
}

fn random_lazy(rng: &mut StdRng) -> String {
    once(rng.sample(Alphanumeric) as char).collect()
}

#[test]
fn test_cat_insert_delete() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case::<Cat, _, _>(
            &mut rng,
            random_value,
            random_lazy,
            &Spec {
                len: 1,
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
fn test_cat_push_pop() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case::<Cat, _, _>(
            &mut rng,
            random_value,
            random_lazy,
            &Spec {
                len: 1,
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
fn test_cat_act() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case::<Cat, _, _>(
            &mut rng,
            random_value,
            random_lazy,
            &Spec {
                fold: 2,
                act: 4,
                ..Spec::default()
            },
        );
    }
}
