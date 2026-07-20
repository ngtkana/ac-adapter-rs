use intrusive_splay_tree::{Op, Tree};

struct Value {
    key: u32,
    size: usize,
}

enum O {}
impl Op for O {
    type Value = Value;

    fn update(center: &mut Self::Value, left: Option<&Self::Value>, right: Option<&Self::Value>) {
        center.size = 1;
        if let Some(left) = left {
            center.size += left.size;
        }
        if let Some(right) = right {
            center.size += right.size;
        }
    }
}

fn query_0_insert(tree: &mut Tree<O>, key: u32) {
    tree.remove_by_key(&key, |value| value.key);
    tree.insert_lower_bound_by_key(Value { key, size: 1 }, |value| value.key)
}

fn query_1_remove(tree: &mut Tree<O>, key: u32) {
    tree.remove_by_key(&key, |value| value.key);
}

fn query_2_nth(tree: &mut Tree<O>, index: usize) -> Option<u32> {
    tree.get_by_index(index, |value| value.size)
        .map(|value| value.key)
}

fn query_3_count_le(tree: &mut Tree<O>, key: u32) -> usize {
    tree.range_by_key(..=key, |n| n.key)
        .fold()
        .map_or(0, |e| e.size)
}

fn query_4_pred(tree: &mut Tree<O>, key: u32) -> Option<u32> {
    tree.range_by_key(..=key, |n| n.key).back().map(|e| e.key)
}

fn query_5_succ(tree: &mut Tree<O>, key: u32) -> Option<u32> {
    tree.range_by_key(key.., |n| n.key).front().map(|e| e.key)
}

mod random_tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};
    use std::collections::BTreeSet;

    #[test]
    fn test_library_checker_ordered_set() {
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..200 {
            let q = rng.gen_range(1..=200);
            let lim = (q / 2).max(1) as u32;

            let mut tree = Tree::<O>::new();
            let mut model: BTreeSet<u32> = BTreeSet::new();

            for _ in 0..q {
                match rng.gen_range(0..8) {
                    0 | 1 => {
                        let key = rng.gen_range(0..lim);
                        query_0_insert(&mut tree, key);
                        model.insert(key);
                    }
                    2 | 3 => {
                        let key = rng.gen_range(0..lim);
                        query_1_remove(&mut tree, key);
                        model.remove(&key);
                    }
                    4 => {
                        let index = rng.gen_range(0..=lim as usize);
                        let expected = model.iter().nth(index).copied();
                        let got = query_2_nth(&mut tree, index);
                        if got != expected {
                            eprintln!(
                                "nth({}) failed: got {:?}, expected {:?}",
                                index, got, expected
                            );
                            eprintln!(
                                "tree.fold().map(|v| v.size): {:?}",
                                tree.fold().map(|v| v.size)
                            );
                            eprintln!("tree.collect().len(): {}", tree.collect().len());
                            eprintln!(
                                "tree contents: {:?}",
                                tree.collect().iter().map(|v| v.key).collect::<Vec<_>>()
                            );
                        }
                        assert_eq!(got, expected);
                    }
                    5 => {
                        let key = rng.gen_range(0..=lim);
                        let expected = model.range(..=key).count();
                        let got = query_3_count_le(&mut tree, key);
                        assert_eq!(
                            got, expected,
                            "count_le({}) failed: got {}, expected {}",
                            key, got, expected
                        );
                    }
                    6 => {
                        let key = rng.gen_range(0..=lim);
                        let expected = model.range(..=key).next_back().copied();
                        let got = query_4_pred(&mut tree, key);
                        assert_eq!(
                            got, expected,
                            "pred({}) failed: got {:?}, expected {:?}",
                            key, got, expected
                        );
                    }
                    7 => {
                        let key = rng.gen_range(0..=lim);
                        let expected = model.range(key..).next().copied();
                        let got = query_5_succ(&mut tree, key);
                        if got != expected {
                            eprintln!(
                                "succ({}) failed: got {:?}, expected {:?}",
                                key, got, expected
                            );
                            eprintln!(
                                "tree contents: {:?}",
                                tree.collect().iter().map(|v| v.key).collect::<Vec<_>>()
                            );
                            eprintln!(
                                "model contents: {:?}",
                                model.iter().copied().collect::<Vec<_>>()
                            );
                        }
                        assert_eq!(
                            got, expected,
                            "succ({}) failed: got {:?}, expected {:?}",
                            key, got, expected
                        );
                    }
                    _ => unreachable!(),
                }

                // 集約値 (size) の整合性
                match tree.fold() {
                    Some(root) => assert_eq!(root.size, model.len()),
                    None => assert!(model.is_empty()),
                }

                // 全件一致
                let collected: Vec<u32> = tree.collect().iter().map(|v| v.key).collect();
                let expected: Vec<u32> = model.iter().copied().collect();
                assert_eq!(collected, expected);
            }
        }
    }
}
