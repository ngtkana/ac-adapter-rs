use rand::{Rng, SeedableRng, rngs::StdRng};
use w_ary_tree::*;

fn gen_instance(mut rng: impl Rng, p: f64) -> (usize, Vec<bool>, WAryTree) {
    let depth = rng.gen_range(0..=2);
    let n = rng.gen_range(1 << (depth * 6)..(1 << ((depth + 1) * 6)).min(1 << 13));
    let a = (0..n).map(|_| rng.gen_bool(p)).collect::<Vec<_>>();
    let tree = WAryTree::from_slice_of_bool(&a);
    (n, a, tree)
}

#[test]
fn test_w_ary_tree_contains() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let (n, a, tree) = gen_instance(&mut rng, 0.5);
        for _ in 0..200 {
            let x = rng.gen_range(0..n);
            let result = a[x];
            let expected = tree.contains(x);
            assert_eq!(result, expected, "x = {x}");
        }
    }
}

#[test]
fn test_w_ary_tree_insert_collect() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let (n, mut a, mut tree) = gen_instance(&mut rng, 0.5);
        for _ in 0..200 {
            let x = rng.gen_range(0..n);
            let result = !a[x];
            a[x] = true;
            let expected = tree.insert(x);
            assert_eq!(result, expected, "x = {x}");
        }
        let result = a;
        let expected = tree.iter().collect::<Vec<_>>();
        assert_eq!(result, expected);
    }
}

#[test]
fn test_w_ary_tree_remove_collect() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let (n, mut a, mut tree) = gen_instance(&mut rng, 0.5);
        for _ in 0..200 {
            let x = rng.gen_range(0..n);
            let result = a[x];
            a[x] = false;
            let expected = tree.remove(x);
            assert_eq!(result, expected, "x = {x}");
        }
        let result = a;
        let expected = tree.iter().collect::<Vec<_>>();
        assert_eq!(result, expected);
    }
}

#[test]
fn test_w_ary_tree_min() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        let p = 2f64.powf(rng.gen_range(-8f64..=-1f64));
        let (n, a, tree) = gen_instance(&mut rng, p);
        eprintln!(
            "n = {n}, a = {:?}",
            (0..n).filter(|&b| a[b]).collect::<Vec<_>>()
        );
        let result = a.iter().position(|&b| b);
        let expected = tree.min();
        assert_eq!(result, expected);
    }
}

#[test]
fn test_w_ary_tree_successor_excluding() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let p = 2f64.powf(rng.gen_range(-8f64..=-1f64));
        let (n, a, tree) = gen_instance(&mut rng, p);
        for _ in 0..200 {
            let x = rng.gen_range(0..n);
            let result = (x + 1..n).find(|&x| a[x]);
            let expected = tree.successor_excluding(x);
            assert_eq!(result, expected, "x = {x}");
        }
    }
}

#[test]
fn test_w_ary_tree_max() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        let p = 2f64.powf(rng.gen_range(-8f64..=-1f64));
        let (_n, a, tree) = gen_instance(&mut rng, p);
        let result = a.iter().rposition(|&b| b);
        let expected = tree.max();
        assert_eq!(result, expected);
    }
}

#[test]
fn test_w_ary_tree_predecessor_excluding() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..20 {
        let p = 2f64.powf(rng.gen_range(-8f64..=-1f64));
        let (n, a, tree) = gen_instance(&mut rng, p);
        for _ in 0..200 {
            let x = rng.gen_range(0..n);
            let result = (0..x).rfind(|&x| a[x]);
            let expected = tree.predecessor_excluding(x);
            assert_eq!(result, expected, "x = {x}");
        }
    }
}
