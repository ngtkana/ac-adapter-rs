use {
    super::{brute::Brute, NoLazy, Ops, SplayTree},
    rand::{distributions::Alphanumeric, prelude::StdRng, Rng, SeedableRng},
    std::mem::swap,
};

enum Cat {}
impl Ops for Cat {
    type Value = char;
    type Acc = String;
    fn proj(c: &char) -> String {
        c.to_string()
    }
    fn op(lhs: &String, rhs: &String) -> String {
        lhs.chars().chain(rhs.chars()).collect()
    }
}

#[test]
fn test_cat_only_get() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case(
            &mut rng,
            &Spec {
                get: 4,
                fold: 4,
                push_back: 4,
                push_front: 4,
                insert: 1,
                pop_back: 4,
                pop_front: 4,
                delete: 4,
            },
        );
    }
}

#[test]
fn test_cat_typical_queries() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case(
            &mut rng,
            &Spec {
                get: 4,
                fold: 2,
                push_back: 1,
                push_front: 1,
                insert: 1,
                pop_back: 1,
                pop_front: 1,
                delete: 1,
            },
        );
    }
}

#[test]
fn test_cat_typical_queries_many_delete() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case(
            &mut rng,
            &Spec {
                get: 4,
                fold: 2,
                push_back: 1,
                push_front: 1,
                insert: 1,
                pop_back: 2,
                pop_front: 2,
                delete: 2,
            },
        );
    }
}

#[test]
fn test_cat_typical_queries_many_push() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        test_case(
            &mut rng,
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

struct Spec {
    get: usize,
    fold: usize,
    push_back: usize,
    push_front: usize,
    insert: usize,
    pop_back: usize,
    pop_front: usize,
    delete: usize,
}

fn test_case(rng: &mut StdRng, spec: &Spec) {
    println!("New test case");
    let mut splay = SplayTree::<NoLazy<Cat>>::new();
    let mut brute = Brute::new();
    let dice_max = spec.get
        + spec.fold
        + spec.push_back
        + spec.push_front
        + spec.insert
        + spec.pop_back
        + spec.pop_front;
    for _ in 0..200 {
        let mut dice = rng.gen_range(0..dice_max);

        // get
        if dice < spec.get {
            let i = rng.gen_range(0..=brute.len());
            let expected = brute.get(i);
            println!("get({}) = {:?}", i, &expected);
            let result = splay.get(i);
            assert_eq!(result, expected);
            continue;
        }
        dice -= spec.get;

        // fold
        if dice < spec.fold {
            let mut l = rng.gen_range(0..=brute.len() + 1);
            let mut r = rng.gen_range(0..=brute.len());
            if l > r {
                swap(&mut l, &mut r);
                r -= 1;
            }
            let expected = brute.fold(l..r);
            println!("fold({}..{}) = {:?}", l, r, &expected);
            let result = splay.fold(l..r);
            assert_eq!(expected, result);
            continue;
        }
        dice -= spec.fold;

        // push_back
        if dice < spec.push_back {
            let c = rng.sample(Alphanumeric) as char;
            brute.push_back(c);
            println!("push_back({}) -> {:?}", c, brute.fold_all_unwrap());
            splay.push_back(c);
            continue;
        }
        dice -= spec.push_back;

        // push_front
        if dice < spec.push_front {
            let c = rng.sample(Alphanumeric) as char;
            brute.push_front(c);
            splay.push_front(c);
            continue;
        }
        dice -= spec.push_front;

        // insert
        if dice < spec.insert {
            let i = rng.gen_range(0..=brute.len());
            let c = rng.sample(Alphanumeric) as char;
            brute.insert(i, c);
            println!("insert({}, {}) -> {:?}", i, c, brute.fold_all_unwrap());
            splay.insert(i, c);
            continue;
        }
        dice -= spec.insert;

        // pop_back
        if dice < spec.pop_back {
            let expected = brute.pop_back();
            println!(
                "pop_back() = {:?} -> {:?}",
                expected,
                brute.fold_all_unwrap()
            );
            let result = splay.pop_back();
            assert_eq!(expected, result);
            continue;
        }
        dice -= spec.pop_back;

        // pop_front
        if dice < spec.pop_front {
            let expected = brute.pop_front();
            println!(
                "pop_front() = {:?} -> {:?}",
                expected,
                brute.fold_all_unwrap()
            );
            let result = splay.pop_front();
            assert_eq!(expected, result);
            continue;
        }
        dice -= spec.pop_front;

        // delete
        if dice < spec.delete {
            let i = rng.gen_range(0..brute.len());
            if i < brute.len() {
                let expected = brute.delete(i);
                println!(
                    "delete({}) = {:?} -> {:?}",
                    i,
                    expected,
                    brute.fold_all_unwrap()
                );
                let result = splay.delete(i);
                assert_eq!(expected, result);
            }
            continue;
        }
        unreachable!();
    }
}
