use intrusive_splay_tree::{Op, Tree};

struct Value {
    size: usize,
    key: u32,
}
impl Value {
    fn size(&self) -> usize {
        self.size
    }
    fn key(&self) -> u32 {
        self.key
    }
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

#[test]
fn test_range_by_index() {
    let keys = [8, 1, 6];
    let mut tree = Tree::<O>::new();
    for &key in &keys {
        tree.push_back(Value { key, size: 1 });
    }

    // Range<usize>
    for start in 0..=keys.len() {
        for end in start..=keys.len() {
            let range = start..end;
            let result = tree
                .range_by_index(range.clone(), Value::size)
                .collect(Value::key);
            let expected = &keys[range.clone()];
            assert_eq!(result, expected, "range = {range:?}");
        }
    }

    // RangeFrom<usize>
    for start in 0..=keys.len() {
        let range = start..;
        let result = tree
            .range_by_index(range.clone(), Value::size)
            .collect(Value::key);
        let expected = &keys[range.clone()];
        assert_eq!(result, expected, "range = {range:?}");
    }

    // RangeInclusive<usize>
    for start in 0..keys.len() {
        for end in start..keys.len() {
            let range = start..=end;
            let result = tree
                .range_by_index(range.clone(), Value::size)
                .collect(Value::key);
            let expected = &keys[range.clone()];
            assert_eq!(result, expected, "range = {range:?}");
        }
    }

    // RangeToInclusive<usize>
    for end in 0..keys.len() {
        let range = ..=end;
        let result = tree
            .range_by_index(range.clone(), Value::size)
            .collect(Value::key);
        let expected = &keys[range.clone()];
        assert_eq!(result, expected, "range = {range:?}");
    }

    // RangeFull
    {
        let range = ..;
        let result = tree
            .range_by_index(range.clone(), Value::size)
            .collect(Value::key);
        let expected = &keys[range.clone()];
        assert_eq!(result, expected, "range = {range:?}");
    }
}

#[test]
fn test_range_by_key() {
    let keys = [4, 6, 8];
    let mut tree = Tree::<O>::new();
    for &key in &keys {
        tree.push_back(Value { key, size: 1 });
    }

    let min = 3;
    let max = 9;

    // Range<u32>
    for start in min..=max {
        for end in start..=max {
            let range = start..end;
            let result = tree
                .range_by_key(range.clone(), Value::key)
                .collect(Value::key);
            let expected = keys
                .iter()
                .copied()
                .filter(|&key| range.contains(&key))
                .collect::<Vec<_>>();
            assert_eq!(result, expected, "range = {range:?}");
        }
    }

    // RangeFrom<u32>
    for start in min..=max {
        let range = start..;
        let result = tree
            .range_by_key(range.clone(), Value::key)
            .collect(Value::key);
        let expected = keys
            .iter()
            .copied()
            .filter(|&key| range.contains(&key))
            .collect::<Vec<_>>();
        assert_eq!(result, expected, "range = {range:?}");
    }

    // RangeInclusive<u32>
    for start in min..=max {
        for end in min..=max {
            let range = start..=end;
            let result = tree
                .range_by_key(range.clone(), Value::key)
                .collect(Value::key);
            let expected = keys
                .iter()
                .copied()
                .filter(|&key| range.contains(&key))
                .collect::<Vec<_>>();
            assert_eq!(result, expected, "range = {range:?}");
        }
    }

    // RangeToInclusive<u32>
    for end in min..=max {
        let range = ..=end;
        let result = tree
            .range_by_key(range.clone(), Value::key)
            .collect(Value::key);
        let expected = keys
            .iter()
            .copied()
            .filter(|&key| range.contains(&key))
            .collect::<Vec<_>>();
        assert_eq!(result, expected, "range = {range:?}");
    }

    // RangeFull<u32>
    {
        let range = ..;
        let result = tree
            .range_by_key(range.clone(), Value::key)
            .collect(Value::key);
        let expected = keys.clone();
        assert_eq!(result, expected, "range = {range:?}");
    }
}
