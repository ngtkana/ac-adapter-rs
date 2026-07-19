use order_statistic_tree::{Op, OrderStatisticMap};
use order_statistic_tree::map::Entry;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::collections::BTreeMap;

/// Simple sum operation for testing augmented API.
struct SumOp;

impl Op for SumOp {
    type Key = i32;
    type Value = i32;
    type SegValue = i64;

    fn identity() -> Self::SegValue {
        0
    }

    fn to_seg_value(key: &Self::Key, value: &Self::Value) -> Self::SegValue {
        (*key as i64) + (*value as i64)
    }

    fn mul(lhs: &Self::SegValue, rhs: &Self::SegValue) -> Self::SegValue {
        lhs + rhs
    }
}

mod basic {
    use super::*;

    #[test]
    fn test_simple_operations() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        assert_eq!(map.len(), 0);

        map.insert(2, 20);
        assert_eq!(map.len(), 1, "After insert 2");

        map.insert(1, 10);
        assert_eq!(map.len(), 2, "After insert 1");

        map.insert(3, 30);
        assert_eq!(map.len(), 3, "After insert 3");

        // Insert duplicate
        map.insert(2, 25);
        assert_eq!(map.len(), 3, "After duplicate insert");

        // Remove
        map.remove(&2);
        assert_eq!(map.len(), 2, "After remove");

        // Check iteration
        let collected: Vec<_> = map.iter().collect();
        assert_eq!(collected.len(), 2);
    }

    #[test]
    fn test_default_clear_from_extend() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::default();
        assert!(map.is_empty());

        let data = vec![(1, 10), (2, 20), (3, 30)];
        map.extend(data.clone());
        assert_eq!(map.len(), 3);

        map.clear();
        assert!(map.is_empty());

        let map2: OrderStatisticMap<i32, i32> = data.into_iter().collect();
        assert_eq!(map2.len(), 3);
    }

    #[test]
    fn test_get_mut() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        map.insert(1, 10);
        map.insert(2, 20);

        if let Some(mut v) = map.get_mut(&1) {
            *v = 100;
        }

        assert_eq!(map.get(&1), Some(&100));
        assert_eq!(map.get(&2), Some(&20));
    }

    #[test]
    fn test_keys_values() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);

        let keys: Vec<_> = map.keys().collect();
        assert_eq!(keys.len(), 3);

        let values: Vec<_> = map.values().collect();
        assert_eq!(values.len(), 3);
    }

    #[test]
    #[should_panic(expected = "strictly less")]
    fn test_concat_panic_on_overlap() {
        let mut map1: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
        map1.insert(1, "a");
        map1.insert(2, "b");

        let mut map2: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
        map2.insert(2, "c");
        map2.insert(3, "d");

        map1.concat(&mut map2);
    }
}

mod split_concat {
    use super::*;

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_split_off_concat_roundtrip() {
        const VALUE_LIM: i32 = 200;
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..200 {
            let n = rng.gen_range(1..=200);
            let q = rng.gen_range(0..=200);

            let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
            let mut vec: Vec<(i32, i32)> = Vec::new();

            for _ in 0..q {
                let key = rng.gen_range(0..n);
                let value = rng.gen_range(0..VALUE_LIM);
                map.insert(key, value);
                if let Some(pos) = vec.iter().position(|(k, _)| k == &key) {
                    vec[pos] = (key, value);
                } else {
                    let idx = vec.iter().position(|(k, _)| k > &key).unwrap_or(vec.len());
                    vec.insert(idx, (key, value));
                }
            }

            let split_key = rng.gen_range(0..=(n + 1));
            let hi_map = map.split_off_by_key(&split_key);

            let lo_collected: Vec<_> = map.iter().collect();
            let hi_collected: Vec<_> = hi_map.iter().collect();

            let split_pos = vec
                .iter()
                .position(|(k, _)| *k >= split_key)
                .unwrap_or(vec.len());
            let lo_expected: Vec<_> = vec[..split_pos]
                .iter()
                .map(|(k, v)| (k, v))
                .collect();
            let hi_expected: Vec<_> = vec[split_pos..]
                .iter()
                .map(|(k, v)| (k, v))
                .collect();

            assert_eq!(lo_collected, lo_expected, "split_off lo mismatch");
            assert_eq!(hi_collected, hi_expected, "split_off hi mismatch");

            let mut map = map;
            let mut hi_map = hi_map;
            map.concat(&mut hi_map);

            let final_collected: Vec<_> = map.iter().collect();
            let final_expected: Vec<_> = vec.iter().map(|(k, v)| (k, v)).collect();

            assert_eq!(final_collected, final_expected, "concat roundtrip mismatch");
            assert!(hi_map.is_empty(), "hi_map should be empty after concat");
        }
    }
}

mod random {
    use super::*;

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_insert_remove_nth_random() {
        const VALUE_LIM: i32 = 200;
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..200 {
            let n = rng.gen_range(1..=200);
            let q = rng.gen_range(0..=200);

            let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
            let mut vec: Vec<(i32, i32)> = Vec::new();

            for _ in 0..q {
                // Weighted: P(remove) = 0.7 when non-empty, else 1.0 (if we have insertions)
                // This aggressively removes existing elements, creating deep unbalanced trees
                // that expose the detach_root len-staleness bug.
                let should_remove = !vec.is_empty() && rng.gen_bool(0.7);

                if should_remove {
                    // Remove family (types 2, 3, 4)
                    let remove_type = rng.gen_range(0..3);
                    match remove_type {
                        0 => {
                            // remove_nth (always succeeds on non-empty set)
                            let idx = rng.gen_range(0..vec.len());
                            map.remove_nth(idx);
                            vec.remove(idx);
                        }
                        1 => {
                            // pop_first or pop_last
                            if rng.gen_bool(0.5) {
                                map.pop_first();
                                vec.remove(0);
                            } else {
                                map.pop_last();
                                vec.pop();
                            }
                        }
                        2 => {
                            // remove by key from existing elements
                            if !vec.is_empty() {
                                let idx = rng.gen_range(0..vec.len());
                                let key_to_remove = vec[idx].0;
                                map.remove(&key_to_remove);
                                vec.retain(|(k, _)| k != &key_to_remove);
                            }
                        }
                        _ => unreachable!(),
                    }
                } else {
                    // Insert (types 0, 1)
                    let key = rng.gen_range(0..n);
                    let value = rng.gen_range(0..VALUE_LIM);
                    map.insert(key, value);
                    if let Some(pos) = vec.iter().position(|(k, _)| k == &key) {
                        vec[pos] = (key, value);
                    } else {
                        let idx = vec.iter().position(|(k, _)| k > &key).unwrap_or(vec.len());
                        vec.insert(idx, (key, value));
                    }
                }

                // Verify invariants
                assert_eq!(map.len(), vec.len(), "Length mismatch");
                assert_eq!(map.is_empty(), vec.is_empty(), "Empty mismatch");

                if vec.is_empty() {
                    assert_eq!(map.first_key_value(), None);
                    assert_eq!(map.last_key_value(), None);
                } else {
                    assert_eq!(
                        map.first_key_value(),
                        Some((&vec[0].0, &vec[0].1)),
                        "First key-value mismatch"
                    );
                    assert_eq!(
                        map.last_key_value(),
                        Some((&vec[vec.len() - 1].0, &vec[vec.len() - 1].1)),
                        "Last key-value mismatch"
                    );
                }

                let collected: Vec<_> = map.iter().collect();
                let expected: Vec<_> = vec.iter().map(|(k, v)| (k, v)).collect();
                assert_eq!(collected, expected, "iter() mismatch");

                for (i, expected_kv) in vec.iter().enumerate() {
                    assert_eq!(map.nth(i), (&expected_kv.0, &expected_kv.1), "nth({i}) mismatch");
                }

                // Query: get, get_key_value, contains_key, binary_search, lower_bound, upper_bound
                for key in 0..n {
                    let expected_get = vec.iter().find(|(k, _)| k == &key).map(|(_, v)| v);
                    assert_eq!(map.get(&key), expected_get, "get({key}) mismatch");

                    let expected_get_key_value =
                        vec.iter().find(|(k, _)| k == &key).map(|(k, v)| (k, v));
                    assert_eq!(
                        map.get_key_value(&key),
                        expected_get_key_value,
                        "get_key_value({key}) mismatch"
                    );

                    let expected_contains = vec.iter().any(|(k, _)| k == &key);
                    assert_eq!(
                        map.contains_key(&key),
                        expected_contains,
                        "contains_key({key}) mismatch"
                    );

                    let expected_binary_search = vec
                        .iter()
                        .position(|(k, _)| k == &key)
                        .ok_or_else(|| vec.iter().position(|(k, _)| k > &key).unwrap_or(vec.len()));
                    assert_eq!(
                        map.binary_search(&key),
                        expected_binary_search,
                        "binary_search({key}) mismatch"
                    );

                    let expected_lower_bound =
                        vec.iter().position(|(k, _)| k >= &key).unwrap_or(vec.len());
                    assert_eq!(
                        map.lower_bound(&key),
                        expected_lower_bound,
                        "lower_bound({key}) mismatch"
                    );

                    let expected_upper_bound =
                        vec.iter().position(|(k, _)| k > &key).unwrap_or(vec.len());
                    assert_eq!(
                        map.upper_bound(&key),
                        expected_upper_bound,
                        "upper_bound({key}) mismatch"
                    );
                }
            }
        }
    }
}

mod fold {
    use super::*;

    #[test]
    fn test_fold_empty_map() {
        // Empty map should return identity
        let map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        assert_eq!(map.fold_all(), SumOp::identity());
    }

    #[test]
    fn test_fold_whole_map() {
        // Single element
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(5, 10);
        assert_eq!(map.fold_all(), 5 + 10);

        // Multiple elements
        map.insert(3, 20);
        map.insert(7, 15);
        let expected = (5 + 10) + (3 + 20) + (7 + 15);
        assert_eq!(map.fold_all(), expected);
    }

    #[test]
    fn test_fold_range_basic() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 1..=5 {
            map.insert(i, i * 10);
        }

        // Whole range
        let whole = (1 + 10) + (2 + 20) + (3 + 30) + (4 + 40) + (5 + 50);
        assert_eq!(map.fold_by_key(1..6), whole);

        // Partial range [2, 4)
        let partial = (2 + 20) + (3 + 30);
        assert_eq!(map.fold_by_key(2..4), partial);

        // Single element [3, 4)
        assert_eq!(map.fold_by_key(3..4), 3 + 30);
    }

    #[test]
    fn test_fold_range_empty() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(5, 50);

        // Empty range
        assert_eq!(map.fold_by_key(1..1), SumOp::identity());
        assert_eq!(map.fold_by_key(10..20), SumOp::identity());
    }

    #[test]
    fn test_fold_after_overwrite() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(5, 10);
        assert_eq!(map.fold_all(), 5 + 10);

        // Overwrite value
        map.insert(5, 20);
        assert_eq!(map.fold_all(), 5 + 20, "fold should reflect updated value");
    }

    #[test]
    fn test_noop_backward_compat() {
        // Type annotation omits O parameter, defaults to NoOp
        let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
        map.insert(3, "c");
        map.insert(1, "a");
        map.insert(2, "b");

        assert_eq!(map.nth(0), (&1, &"a"));
        assert_eq!(map.get(&2), Some(&"b"));
        assert_eq!(map.len(), 3);
    }

    #[test]
    fn test_fold_after_remove() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 1..=5 {
            map.insert(i, i * 10);
        }

        // Verify fold is correct before removal
        let expected_all = (1..=5).map(|i| (i as i64) + (i as i64 * 10)).sum::<i64>();
        assert_eq!(map.fold_all(), expected_all);

        // Remove an element and verify fold reflects the change
        let removed = map.remove(&3);
        assert_eq!(removed, Some(30));

        let expected_after = (1..=5)
            .filter(|i| *i != 3)
            .map(|i| (i as i64) + (i as i64 * 10))
            .sum::<i64>();
        assert_eq!(map.fold_all(), expected_after);
    }

    #[test]
    fn test_fold_remove_nth_random() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        let mut reference: BTreeMap<i32, i32> = BTreeMap::new();
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);

        // First, build a stable map with known content
        for i in 1..=10 {
            map.insert(i, i * 10);
            reference.insert(i, i * 10);
        }

        // Verify initial fold
        let expected: i64 = reference
            .iter()
            .map(|(&k, &v)| (k as i64) + (v as i64))
            .sum();
        assert_eq!(map.fold_all(), expected, "initial fold mismatch");

        // Remove elements one by one
        for step in 0..5 {
            if map.is_empty() {
                break;
            }

            let remove_nth = rng.gen_range(0..map.len());
            let (k, _) = map.nth(remove_nth);
            let k = *k;

            map.remove(&k);
            reference.remove(&k);

            // Verify fold matches brute-force sum after each removal
            let expected: i64 = reference
                .iter()
                .map(|(&k, &v)| (k as i64) + (v as i64))
                .sum();
            assert_eq!(
                map.fold_all(),
                expected,
                "fold mismatch at step {step} after removing key {k}"
            );
        }
    }
}

mod regression {
    use super::*;

    #[test]
    fn test_detach_root_bug_right_spine_deep_tree() {
        // DETERMINISTIC TEST for detach_root len-staleness bug.
        //
        // Strategy: insert keys in a specific order that forces splay to create
        // a right-spine structure in the left subtree, then delete the root.
        //
        // Key insight: insert in increasing order after the root to avoid splaying,
        // which creates a right-skewed tree. Then insert a right-subtree element.
        // When we delete the root, detach_root will walk the left's right-spine.

        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();

        // Insert sequential keys in increasing order
        // This creates a right-skewed tree structure naturally
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        map.insert(4, 40);
        map.insert(200, 2000);

        let before_len = map.len();
        assert_eq!(before_len, 5, "precondition: should have 5 elements before deletion");

        // The root of the map is one of these keys. When we remove the actual root,
        // detach_root will be called with both left and right subtrees populated.
        // The splay tree structure means the root changes, but there will be a key
        // that becomes root. Remove that key to trigger the bug.

        // Actually, remove a smaller key first to trigger splaying and see what root becomes
        if let Some(root_key) = map.iter().map(|(k, _)| *k).next() {
            map.remove(&root_key);
        }

        let after_len = map.len();
        assert_eq!(
            after_len, 4,
            "After removing 1 element, len should be 4, got {after_len}"
        );

        // Verify tree integrity via iter
        let iter_count = map.iter().count();
        assert_eq!(
            iter_count, after_len,
            "iter().count()={iter_count} should match len()={after_len}"
        );
    }
}

mod aggregation_consistency {
    use super::*;

    #[test]
    fn test_get_mut_preserves_fold_with_sumop() {
        // TDD Test: get_mut() で値を変更した場合、fold() が正しく更新されるか？
        // 現状の実装では、get_mut() は生の &mut V を返すため、
        // 値の変更後に prod（集約値）が再計算されず、fold() の結果が壊れる。
        //
        // このテストが PASS = 集約値が自動的に再計算される ガード型が実装されている
        // このテストが FAIL = 潜在バグが存在する（修正前の状態）

        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);

        let expected_before = 1 + 10 + 2 + 20 + 3 + 30;
        assert_eq!(map.fold_all(), expected_before, "Initial fold should be correct");

        // get_mut で値を変更
        if let Some(mut v) = map.get_mut(&2) {
            *v = 99; // 20 -> 99 に変更
        }

        // fold() の結果が更新されているか？
        // 正しくは: 1 + 10 + 2 + 99 + 3 + 30 = 145
        // バグの場合: (古い) 1 + 10 + 2 + 20 + 3 + 30 = 66 のまま
        let expected_after = 1 + 10 + 2 + 99 + 3 + 30;
        assert_eq!(
            map.fold_all(),
            expected_after,
            "fold() should reflect the value changed via get_mut()"
        );
    }

    #[test]
    fn test_fold_range_not_affected_by_get_mut_outside_range() {
        // fold_range() も同じバグに影響を受ける可能性
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        map.insert(4, 40);

        let range_before = map.fold_by_key(1..3); // [1, 3) = (1, 10) + (2, 20)
        assert_eq!(range_before, 1 + 10 + 2 + 20);

        // キー 4 の値を変更（範囲外）
        if let Some(mut v) = map.get_mut(&4) {
            *v = 99;
        }

        // [1, 3) のフォールドは変わらないはず
        let range_after = map.fold_by_key(1..3);
        assert_eq!(range_after, 1 + 10 + 2 + 20);

        // ただし全体のフォールドは変わる
        let fold_all = map.fold_all();
        assert_eq!(fold_all, 1 + 10 + 2 + 20 + 3 + 30 + 4 + 99);
    }
}

mod max_right_min_left {
    use super::*;

    #[test]
    fn test_max_right_basic() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..10 {
            map.insert(i, 1);
        }

        assert_eq!(map.max_right(0, |&s| s <= 3), 2);
        assert_eq!(map.max_right(0, |&s| s <= 15), 5);
        assert_eq!(map.max_right(0, |&s| s <= 55), 10);
    }

    #[test]
    fn test_min_left_basic() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..10 {
            map.insert(i, 1);
        }

        assert_eq!(map.min_left(2, |&s| s <= 3), 0);
        assert_eq!(map.min_left(5, |&s| s <= 15), 0);
        assert_eq!(map.min_left(10, |&s| s <= 55), 0);
    }

    #[test]
    fn test_max_right_edge_cases() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..10 {
            map.insert(i, 1);
        }

        assert_eq!(map.max_right(10, |&s| s <= 100), 10);
        assert_eq!(map.max_right(0, |&_| true), 10);
        assert_eq!(map.max_right(0, |&s| s <= 0), 0);
    }

    #[test]
    fn test_min_left_edge_cases() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..10 {
            map.insert(i, 1);
        }

        assert_eq!(map.min_left(0, |&_| true), 0);
        assert_eq!(map.min_left(10, |&_| true), 0);
        assert_eq!(map.min_left(10, |&s| s <= 0), 10);
    }

    #[test]
    fn test_max_right_random() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        let mut rng = StdRng::seed_from_u64(12345);

        for _ in 0..100 {
            let key = rng.gen_range(0..1000i32);
            map.insert(key, 1);
        }

        for l in 0..map.len() {
            let threshold = rng.gen_range(0..100i64);
            let result = map.max_right(l, |&s| s <= threshold);

            for r in l..result {
                assert!(map.fold_by_index(l..r) <= threshold);
            }
            if result < map.len() {
                assert!(map.fold_by_index(l..=result) > threshold);
            }
        }
    }

    #[test]
    fn test_min_left_random() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        let mut rng = StdRng::seed_from_u64(54321);

        for _ in 0..100 {
            let key = rng.gen_range(0..1000i32);
            map.insert(key, 1);
        }

        for r in 1..=map.len() {
            let threshold = rng.gen_range(0..100) as i64;
            let result = map.min_left(r, |&s| s <= threshold);

            for l in result..r {
                assert!(map.fold_by_index(l..r) <= threshold);
            }
            if result > 0 {
                assert!(map.fold_by_index(result - 1..r) > threshold);
            }
        }
    }
}

mod entry {
    use super::*;

    #[test]
    fn test_entry_vacant() {
        let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();

        match map.entry(1) {
            Entry::Vacant(ve) => {
                ve.insert("a");
            }
            Entry::Occupied(_) => panic!("Expected vacant entry"),
        }

        assert_eq!(map.get(&1), Some(&"a"));
    }

    #[test]
    fn test_entry_occupied() {
        let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
        map.insert(1, "a");

        match map.entry(1) {
            Entry::Occupied(oe) => {
                assert_eq!(oe.get(), &"a");
            }
            Entry::Vacant(_) => panic!("Expected occupied entry"),
        }

        assert_eq!(map.get(&1), Some(&"a"));
    }

    #[test]
    fn test_entry_or_insert_vacant() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        {
            let value = map.entry(1).or_insert(10);
            assert_eq!(*value, 10);
        }
        assert_eq!(map.get(&1), Some(&10));
    }

    #[test]
    fn test_entry_or_insert_occupied() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        map.insert(1, 10);
        {
            let value = map.entry(1).or_insert(20);
            assert_eq!(*value, 10);
        }
        assert_eq!(map.get(&1), Some(&10));
    }

    #[test]
    fn test_entry_or_insert_with() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        {
            let value = map.entry(1).or_insert_with(|| 10);
            assert_eq!(*value, 10);
        }
        assert_eq!(map.get(&1), Some(&10));
    }

    #[test]
    fn test_entry_or_default() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        {
            let value = map.entry(1).or_default();
            assert_eq!(*value, 0);
        }
        assert_eq!(map.get(&1), Some(&0));
    }

    #[test]
    fn test_entry_and_modify_occupied() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
        map.insert(1, 10);

        let entry = map.entry(1).and_modify(|v| *v += 5);
        {
            let value = entry.or_insert(0);
            assert_eq!(*value, 15);
        }
        assert_eq!(map.get(&1), Some(&15));
    }

    #[test]
    fn test_entry_and_modify_vacant() {
        let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();

        let entry = map.entry(1).and_modify(|v| *v += 5);
        {
            let value = entry.or_insert(10);
            assert_eq!(*value, 10);
        }
        assert_eq!(map.get(&1), Some(&10));
    }

    #[test]
    fn test_entry_key() {
        let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();

        let entry = map.entry(1);
        assert_eq!(entry.key(), &1);
    }

    #[test]
    fn test_entry_aggregation_consistency() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(1, 10);
        map.insert(2, 20);

        let initial_fold = map.fold_all();
        assert_eq!(initial_fold, (1 + 10) + (2 + 20));

        {
            let value = map.entry(1).and_modify(|v| *v = 30).or_insert(0);
            assert_eq!(*value, 30);
        }

        let after_fold = map.fold_all();
        assert_eq!(after_fold, (1 + 30) + (2 + 20));
    }
}

mod amortized_complexity {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_fold_by_index_amortized_complexity() {
        // Regression test: fold_by_index should maintain O(log n) amortized complexity
        // via split/merge-based implementation. This test verifies that repeated
        // fold_by_index calls over a large map don't degrade to O(n) per call.

        const MAP_SIZE: usize = 50_000;
        const NUM_QUERIES: usize = 10_000;
        const TIME_LIMIT_MS: u128 = 2000;

        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..MAP_SIZE as i32 {
            map.insert(i, 1);
        }

        let start = Instant::now();
        let mut sum = 0i64;
        for q in 0..NUM_QUERIES {
            let start_idx = q % MAP_SIZE;
            let end_idx = (start_idx + 100) % MAP_SIZE;
            if start_idx < end_idx {
                sum = sum.wrapping_add(map.fold_by_index(start_idx..end_idx));
            }
        }
        let elapsed = start.elapsed().as_millis();

        assert!(
            elapsed < TIME_LIMIT_MS,
            "fold_by_index regression: {elapsed} ms exceeds limit of {TIME_LIMIT_MS} ms (sum={sum} to prevent optimization)",
        );
    }

    #[test]
    fn test_fold_by_key_amortized_complexity() {
        // Regression test: fold_by_key should maintain O(log n) amortized complexity
        // via lower_bound/upper_bound + fold_by_index delegation.

        const MAP_SIZE: usize = 50_000;
        const NUM_QUERIES: usize = 10_000;
        const TIME_LIMIT_MS: u128 = 2000;

        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..MAP_SIZE as i32 {
            map.insert(i, 1);
        }

        let start = Instant::now();
        let mut sum = 0i64;
        for q in 0..NUM_QUERIES {
            let start_key = (q as i32) % (MAP_SIZE as i32);
            let end_key = start_key + 100;
            sum = sum.wrapping_add(map.fold_by_key(start_key..end_key));
        }
        let elapsed = start.elapsed().as_millis();

        assert!(
            elapsed < TIME_LIMIT_MS,
            "fold_by_key regression: {elapsed} ms exceeds limit of {TIME_LIMIT_MS} ms (sum={sum} to prevent optimization)",
        );
    }

    #[test]
    fn test_max_right_amortized_complexity() {
        // Regression test: max_right should maintain O(log n) amortized complexity.

        const MAP_SIZE: usize = 50_000;
        const NUM_QUERIES: usize = 10_000;
        const TIME_LIMIT_MS: u128 = 2000;

        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..MAP_SIZE as i32 {
            map.insert(i, 1);
        }

        let start = Instant::now();
        let mut sum = 0usize;
        for q in 0..NUM_QUERIES {
            let l = q % MAP_SIZE;
            let threshold = 50i64;
            let r = map.max_right(l, |&s| s <= threshold);
            sum = sum.wrapping_add(r);
        }
        let elapsed = start.elapsed().as_millis();

        assert!(
            elapsed < TIME_LIMIT_MS,
            "max_right regression: {elapsed} ms exceeds limit of {TIME_LIMIT_MS} ms (sum={sum} to prevent optimization)",
        );
    }

    #[test]
    fn test_min_left_amortized_complexity() {
        // Regression test: min_left should maintain O(log n) amortized complexity.

        const MAP_SIZE: usize = 50_000;
        const NUM_QUERIES: usize = 10_000;
        const TIME_LIMIT_MS: u128 = 2000;

        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 0..MAP_SIZE as i32 {
            map.insert(i, 1);
        }

        let start = Instant::now();
        let mut sum = 0usize;
        for q in 0..NUM_QUERIES {
            let r = (q % MAP_SIZE) + 1;
            let threshold = 50i64;
            let l = map.min_left(r, |&s| s <= threshold);
            sum = sum.wrapping_add(l);
        }
        let elapsed = start.elapsed().as_millis();

        assert!(
            elapsed < TIME_LIMIT_MS,
            "min_left regression: {elapsed} ms exceeds limit of {TIME_LIMIT_MS} ms (sum={sum} to prevent optimization)",
        );
    }
}
