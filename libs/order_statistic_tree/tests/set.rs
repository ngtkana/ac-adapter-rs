use order_statistic_tree::OrderStatisticSet;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

mod basic {
    use super::*;

    #[test]
    fn test_simple_operations() {
        let mut set: OrderStatisticSet<i32> = OrderStatisticSet::new();
        assert_eq!(set.len(), 0);

        assert!(set.insert(2));
        assert_eq!(set.len(), 1, "After insert 2");

        assert!(set.insert(1));
        assert_eq!(set.len(), 2, "After insert 1");

        assert!(set.insert(3));
        assert_eq!(set.len(), 3, "After insert 3");

        assert!(!set.insert(2));
        assert_eq!(set.len(), 3, "After duplicate insert");

        assert!(set.remove(&2));
        assert_eq!(set.len(), 2, "After remove");

        let collected: Vec<_> = set.iter().collect();
        assert_eq!(collected.len(), 2);
    }

    #[test]
    fn test_default_clear_from_extend() {
        let mut set: OrderStatisticSet<i32> = OrderStatisticSet::default();
        assert!(set.is_empty());

        let data = vec![1, 2, 3];
        set.extend(data.clone());
        assert_eq!(set.len(), 3);

        set.clear();
        assert!(set.is_empty());

        let set2: OrderStatisticSet<i32> = data.into_iter().collect();
        assert_eq!(set2.len(), 3);
    }

    #[test]
    fn test_get_take_replace() {
        let mut set: OrderStatisticSet<i32> = OrderStatisticSet::new();
        set.insert(1);
        set.insert(2);
        set.insert(3);

        assert_eq!(set.get(&2), Some(&2));
        assert_eq!(set.get(&99), None);

        let taken = set.take(&2);
        assert_eq!(taken, Some(2));
        assert_eq!(set.len(), 2);

        let replaced = set.replace(2);
        assert_eq!(replaced, None);
        assert_eq!(set.len(), 3);

        let replaced_again = set.replace(5);
        assert_eq!(replaced_again, None);
        assert_eq!(set.len(), 4);
    }

    #[test]
    #[should_panic(expected = "strictly less")]
    fn test_concat_panic_on_overlap() {
        let mut set1 = OrderStatisticSet::new();
        set1.insert(1);
        set1.insert(2);

        let mut set2 = OrderStatisticSet::new();
        set2.insert(2);
        set2.insert(3);

        set1.concat(&mut set2);
    }
}

mod split_concat {
    use super::*;

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_split_off_concat_roundtrip() {
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..200 {
            let n = rng.gen_range(1..=200);
            let q = rng.gen_range(0..=200);

            let mut set: OrderStatisticSet<i32> = OrderStatisticSet::new();
            let mut vec: Vec<i32> = Vec::new();

            for _ in 0..q {
                let value = rng.gen_range(0..n);
                set.insert(value);
                if !vec.contains(&value) {
                    let idx = vec.iter().position(|&v| v > value).unwrap_or(vec.len());
                    vec.insert(idx, value);
                }
            }

            let split_value = rng.gen_range(0..=(n + 1));
            let hi_set = set.split_off(&split_value);

            let lo_collected: Vec<_> = set.iter().collect();
            let hi_collected: Vec<_> = hi_set.iter().collect();

            let split_pos = vec
                .iter()
                .position(|&v| v >= split_value)
                .unwrap_or(vec.len());
            let lo_expected: Vec<_> = vec[..split_pos].iter().collect();
            let hi_expected: Vec<_> = vec[split_pos..].iter().collect();

            assert_eq!(lo_collected, lo_expected, "split_off lo mismatch");
            assert_eq!(hi_collected, hi_expected, "split_off hi mismatch");

            let mut set = set;
            let mut hi_set = hi_set;
            set.concat(&mut hi_set);

            let final_collected: Vec<_> = set.iter().collect();
            let final_expected: Vec<_> = vec.iter().collect();

            assert_eq!(final_collected, final_expected, "concat roundtrip mismatch");
            assert!(hi_set.is_empty(), "hi_set should be empty after concat");
        }
    }
}

mod random {
    use super::*;

    #[test]
    #[allow(clippy::too_many_lines)]
    fn test_insert_remove_nth_random() {
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..200 {
            let n = rng.gen_range(1..=200);
            let q = rng.gen_range(0..=200);

            let mut set: OrderStatisticSet<i32> = OrderStatisticSet::new();
            let mut vec: Vec<i32> = Vec::new();

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
                            set.remove_nth(idx);
                            vec.remove(idx);
                        }
                        1 => {
                            // pop_first or pop_last
                            if rng.gen_bool(0.5) {
                                set.pop_first();
                                vec.remove(0);
                            } else {
                                set.pop_last();
                                vec.pop();
                            }
                        }
                        2 => {
                            // take by value from existing elements
                            if !vec.is_empty() {
                                let idx = rng.gen_range(0..vec.len());
                                let val_to_remove = vec[idx];
                                set.take(&val_to_remove);
                                vec.retain(|&v| v != val_to_remove);
                            }
                        }
                        _ => unreachable!(),
                    }
                } else {
                    // Insert (types 0, 1)
                    let value = rng.gen_range(0..n);
                    set.insert(value);
                    if !vec.contains(&value) {
                        let idx = vec.iter().position(|&v| v > value).unwrap_or(vec.len());
                        vec.insert(idx, value);
                    }
                }

                // Verify invariants
                assert_eq!(set.len(), vec.len(), "Length mismatch");
                assert_eq!(set.is_empty(), vec.is_empty(), "Empty mismatch");

                if vec.is_empty() {
                    assert_eq!(set.first(), None);
                    assert_eq!(set.last(), None);
                } else {
                    assert_eq!(set.first(), Some(&vec[0]), "First mismatch");
                    assert_eq!(set.last(), Some(&vec[vec.len() - 1]), "Last mismatch");
                }

                let collected: Vec<_> = set.iter().collect();
                let expected: Vec<_> = vec.iter().collect();
                assert_eq!(collected, expected, "iter() mismatch");

                for (i, expected_val) in vec.iter().enumerate() {
                    assert_eq!(set.nth(i), expected_val, "nth({i}) mismatch");
                }

                // Query: get, contains, binary_search, lower_bound, upper_bound
                for value in 0..n {
                    let expected_get = vec.iter().find(|&&v| v == value);
                    assert_eq!(set.get(&value), expected_get, "get({value}) mismatch");

                    let expected_contains = vec.contains(&value);
                    assert_eq!(set.contains(&value), expected_contains, "contains({value}) mismatch");

                    let expected_binary_search = vec
                        .iter()
                        .position(|&v| v == value)
                        .ok_or_else(|| vec.iter().position(|&v| v > value).unwrap_or(vec.len()));
                    assert_eq!(
                        set.binary_search(&value),
                        expected_binary_search,
                        "binary_search({value}) mismatch"
                    );

                    let expected_lower_bound =
                        vec.iter().position(|&v| v >= value).unwrap_or(vec.len());
                    assert_eq!(
                        set.lower_bound(&value),
                        expected_lower_bound,
                        "lower_bound({value}) mismatch"
                    );

                    let expected_upper_bound =
                        vec.iter().position(|&v| v > value).unwrap_or(vec.len());
                    assert_eq!(
                        set.upper_bound(&value),
                        expected_upper_bound,
                        "upper_bound({value}) mismatch"
                    );
                }
            }
        }
    }
}
