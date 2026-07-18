use std::borrow::Borrow;
use std::fmt;
use std::ptr::NonNull;

// v1では未対応: entry, range/range_mut, append, split_off, retain, values_mut, into_iter

#[allow(dead_code)]
pub struct OrderStatisticMap<K, V> {
    root: Option<NonNull<Node<K, V>>>,
    len: usize,
}

impl<K: Ord, V> OrderStatisticMap<K, V> {
    // Group A: Core API
    pub fn new() -> Self {
        todo!()
    }

    pub fn len(&self) -> usize {
        todo!()
    }

    pub fn is_empty(&self) -> bool {
        todo!()
    }

    pub fn clear(&mut self) {
        todo!()
    }

    pub fn insert(&mut self, _key: K, _value: V) -> Option<V> {
        todo!()
    }

    pub fn remove<Q: Ord + ?Sized>(&mut self, _key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn get<Q: Ord + ?Sized>(&self, _key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn contains_key<Q: Ord + ?Sized>(&self, _key: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn iter(&self) -> Box<dyn Iterator<Item = (&K, &V)>> {
        todo!()
    }

    // Group B: Frequently used
    pub fn get_mut<Q: Ord + ?Sized>(&mut self, _key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn get_key_value<Q: Ord + ?Sized>(&self, _key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn remove_entry<Q: Ord + ?Sized>(&mut self, _key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        todo!()
    }

    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        todo!()
    }

    pub fn pop_first(&mut self) -> Option<(K, V)> {
        todo!()
    }

    pub fn pop_last(&mut self) -> Option<(K, V)> {
        todo!()
    }

    pub fn keys(&self) -> Box<dyn Iterator<Item = &K>> {
        todo!()
    }

    pub fn values(&self) -> Box<dyn Iterator<Item = &V>> {
        todo!()
    }

    // Group C: Order statistic
    pub fn nth(&self, _n: usize) -> (&K, &V) {
        todo!()
    }

    pub fn remove_nth(&mut self, _n: usize) -> (K, V) {
        todo!()
    }

    pub fn binary_search<Q: Ord + ?Sized>(&self, _key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn lower_bound<Q: Ord + ?Sized>(&self, _key: &Q) -> usize
    where
        K: Borrow<Q>,
    {
        todo!()
    }

    pub fn upper_bound<Q: Ord + ?Sized>(&self, _key: &Q) -> usize
    where
        K: Borrow<Q>,
    {
        todo!()
    }
}

impl<K: Ord, V> Default for OrderStatisticMap<K, V> {
    fn default() -> Self {
        todo!()
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug> fmt::Debug for OrderStatisticMap<K, V> {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl<'a, K: Ord, V> IntoIterator for &'a OrderStatisticMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = Box<dyn Iterator<Item = Self::Item> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        todo!()
    }
}

impl<K: Ord, V> FromIterator<(K, V)> for OrderStatisticMap<K, V> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(_iter: T) -> Self {
        todo!()
    }
}

impl<K: Ord, V> Extend<(K, V)> for OrderStatisticMap<K, V> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, _iter: T) {
        todo!()
    }
}

#[allow(dead_code)]
struct Node<K, V> {
    key: K,
    value: V,
    parent: Option<NonNull<Self>>,
    left: Option<NonNull<Self>>,
    right: Option<NonNull<Self>>,
    len: usize,
}

#[allow(dead_code)]
impl<K, V> Node<K, V> {
    fn update(&mut self) {
        unsafe {
            self.len = self.left.map_or(0, |left| (*left.as_ptr()).len)
                + 1
                + self.right.map_or(0, |rigth| (*rigth.as_ptr()).len);
        }
    }
}

#[allow(dead_code)]
fn splay<K, V>(mut x: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
    unsafe {
        while let Some(p) = (*x.as_ptr()).parent {
            if let Some(_q) = (*p.as_ptr()).parent {
                todo!()
            } else {
                if (*p.as_ptr()).left == Some(x) {
                    x = rotate_right(p);
                } else if (*p.as_ptr()).right == Some(x) {
                    x = rotate_left(p);
                } else {
                    unreachable!()
                }
            }
        }
        x
    }
}

#[allow(dead_code)]
fn rotate_left<K, V>(x: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
    unsafe {
        assert!((*x.as_ptr()).parent.is_none());
        let y = (*x.as_ptr()).right.unwrap();
        let c = (*y.as_ptr()).left;

        (*x.as_ptr()).right = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).left = Some(x);
        (*x.as_ptr()).parent = Some(y);
        (*y.as_ptr()).parent = None;
        y
    }
}

#[allow(dead_code)]
fn rotate_right<K, V>(x: NonNull<Node<K, V>>) -> NonNull<Node<K, V>> {
    unsafe {
        assert!((*x.as_ptr()).parent.is_none());
        let y = (*x.as_ptr()).left.unwrap();
        let c = (*y.as_ptr()).right;

        (*x.as_ptr()).left = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).right = Some(x);
        (*x.as_ptr()).parent = Some(y);
        (*y.as_ptr()).parent = None;
        y
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    #[test]
    fn test_insert_remove_nth_random() {
        const VALUE_LIM: i32 = 200;
        let mut rng = StdRng::seed_from_u64(42);

        for _ in 0..200 {
            let n = rng.gen_range(1..=200);
            let q = rng.gen_range(0..=200);

            let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
            let mut vec: Vec<(i32, i32)> = Vec::new();

            for _ in 0..q {
                match rng.gen_range(0..5) {
                    0 | 1 => {
                        // insert
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
                    2 => {
                        // remove or remove_entry
                        if rng.gen_bool(0.5) {
                            let key = rng.gen_range(0..n);
                            map.remove(&key);
                            vec.retain(|(k, _)| k != &key);
                        } else {
                            let key = rng.gen_range(0..n);
                            map.remove_entry(&key);
                            vec.retain(|(k, _)| k != &key);
                        }
                    }
                    3 => {
                        // remove_nth
                        if !vec.is_empty() {
                            let idx = rng.gen_range(0..vec.len());
                            map.remove_nth(idx);
                            vec.remove(idx);
                        }
                    }
                    4 => {
                        // pop_first or pop_last
                        if !vec.is_empty() {
                            if rng.gen_bool(0.5) {
                                map.pop_first();
                                vec.remove(0);
                            } else {
                                map.pop_last();
                                vec.pop();
                            }
                        }
                    }
                    _ => unreachable!(),
                }

                // Verify invariants
                assert_eq!(map.len(), vec.len(), "Length mismatch");
                assert_eq!(map.is_empty(), vec.is_empty(), "Empty mismatch");

                if !vec.is_empty() {
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
                } else {
                    assert_eq!(map.first_key_value(), None);
                    assert_eq!(map.last_key_value(), None);
                }

                let collected: Vec<_> = map.iter().collect();
                let expected: Vec<_> = vec.iter().map(|(k, v)| (k, v)).collect();
                assert_eq!(collected, expected, "iter() mismatch");

                for i in 0..vec.len() {
                    assert_eq!(
                        map.nth(i),
                        (&vec[i].0, &vec[i].1),
                        "nth({}) mismatch",
                        i
                    );
                }

                // Query: get, get_key_value, contains_key, binary_search, lower_bound, upper_bound
                for key in 0..n {
                    let expected_get = vec.iter().find(|(k, _)| k == &key).map(|(_, v)| v);
                    assert_eq!(map.get(&key), expected_get, "get({}) mismatch", key);

                    let expected_get_key_value = vec.iter().find(|(k, _)| k == &key).map(|(k, v)| (k, v));
                    assert_eq!(
                        map.get_key_value(&key),
                        expected_get_key_value,
                        "get_key_value({}) mismatch",
                        key
                    );

                    let expected_contains = vec.iter().any(|(k, _)| k == &key);
                    assert_eq!(
                        map.contains_key(&key),
                        expected_contains,
                        "contains_key({}) mismatch",
                        key
                    );

                    let expected_binary_search = vec
                        .iter()
                        .position(|(k, _)| k == &key)
                        .ok_or_else(|| {
                            vec.iter()
                                .position(|(k, _)| k > &key)
                                .unwrap_or(vec.len())
                        });
                    assert_eq!(
                        map.binary_search(&key),
                        expected_binary_search,
                        "binary_search({}) mismatch",
                        key
                    );

                    let expected_lower_bound = vec
                        .iter()
                        .position(|(k, _)| k >= &key)
                        .unwrap_or(vec.len());
                    assert_eq!(
                        map.lower_bound(&key),
                        expected_lower_bound,
                        "lower_bound({}) mismatch",
                        key
                    );

                    let expected_upper_bound = vec
                        .iter()
                        .position(|(k, _)| k > &key)
                        .unwrap_or(vec.len());
                    assert_eq!(
                        map.upper_bound(&key),
                        expected_upper_bound,
                        "upper_bound({}) mismatch",
                        key
                    );
                }
            }
        }
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

        if let Some(v) = map.get_mut(&1) {
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
}
