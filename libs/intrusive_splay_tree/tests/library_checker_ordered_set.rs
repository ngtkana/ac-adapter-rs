use intrusive_splay_tree::{Navi3, Tree, Op};

struct Value {
    key: u32,
    size: usize,
}

enum U {}
impl Op for U {
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

fn query_0_insert(tree: &mut Tree<U>, key: u32) {
    tree.remove_by_key(&key, |value| value.key);
    tree.insert_lower_bound_by_key(Value { key, size: 1 }, |value| value.key)
}

fn query_1_remove(tree: &mut Tree<U>, key: u32) {
    tree.remove_by_key(&key, |value| value.key);
}

fn query_2_nth(tree: &mut Tree<U>, index: usize) -> Option<u32> {
    tree.get_at(index, |value| value.size)
        .map(|value| value.key)
}

fn query_3_count_le(tree: &mut Tree<U>, key: u32) -> usize {
    let mut tail = tree.split_off_upper_bound_by_key(&key, |value| value.key);
    let result = tree.fold_all().map_or(0, |root| root.size);
    tree.append(&mut tail);
    result
}

fn query_4_pred(tree: &mut Tree<U>, key: u32) -> Option<u32> {
    let mut tail = tree.split_off_upper_bound_by_key(&key, |value| value.key);
    let result = tree
        .get(|_, _, right| if right.is_some() { Navi3::GoDownRight } else { Navi3::Found })
        .map(|value| value.key);
    tree.append(&mut tail);
    result
}

fn query_5_succ(tree: &mut Tree<U>, key: u32) -> Option<u32> {
    let mut tail = tree.split_off_lower_bound_by_key(&key, |value| value.key);
    let result = tail
        .get(|_, left, _| if left.is_some() { Navi3::GoDownLeft } else { Navi3::Found })
        .map(|value| value.key);
    tree.append(&mut tail);
    result
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

            let mut tree = Tree::<U>::new();
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
                                "tree.fold_all().map(|v| v.size): {:?}",
                                tree.fold_all().map(|v| v.size)
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
                match tree.fold_all() {
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
