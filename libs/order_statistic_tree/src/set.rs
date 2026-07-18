use super::map::OrderStatisticMap;
use std::borrow::Borrow;
use std::fmt;

pub struct OrderStatisticSet<T> {
    map: OrderStatisticMap<T, ()>,
}

impl<T: Ord> OrderStatisticSet<T> {
    // Group A: Core API
    pub fn new() -> Self {
        Self {
            map: OrderStatisticMap::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn clear(&mut self) {
        self.map.clear();
    }

    pub fn insert(&mut self, value: T) -> bool {
        self.map.insert(value, ()).is_none()
    }

    pub fn remove<Q: Ord + ?Sized>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
    {
        self.map.remove(value).is_some()
    }

    pub fn contains<Q: Ord + ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
    {
        self.map.contains_key(value)
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.map.iter(),
        }
    }

    // Group B: Frequently used
    pub fn get<Q: Ord + ?Sized>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
    {
        self.map.get_key_value(value).map(|(k, ())| k)
    }

    pub fn take<Q: Ord + ?Sized>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
    {
        self.map.remove_entry(value).map(|(k, ())| k)
    }

    pub fn replace(&mut self, value: T) -> Option<T> {
        let old = self.map.remove_entry(&value).map(|(k, ())| k);
        self.map.insert(value, ());
        old
    }

    pub fn first(&self) -> Option<&T> {
        self.map.first_key_value().map(|(k, ())| k)
    }

    pub fn last(&self) -> Option<&T> {
        self.map.last_key_value().map(|(k, ())| k)
    }

    pub fn pop_first(&mut self) -> Option<T> {
        self.map.pop_first().map(|(k, ())| k)
    }

    pub fn pop_last(&mut self) -> Option<T> {
        self.map.pop_last().map(|(k, ())| k)
    }

    // Group C: Order statistic
    pub fn nth(&self, n: usize) -> &T {
        self.map.nth(n).0
    }

    pub fn remove_nth(&mut self, n: usize) -> T {
        self.map.remove_nth(n).0
    }

    pub fn binary_search<Q: Ord + ?Sized>(&self, value: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q>,
    {
        self.map.binary_search(value)
    }

    pub fn lower_bound<Q: Ord + ?Sized>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
    {
        self.map.lower_bound(value)
    }

    pub fn upper_bound<Q: Ord + ?Sized>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
    {
        self.map.upper_bound(value)
    }
}

impl<T: Ord> Default for OrderStatisticSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord + fmt::Debug> fmt::Debug for OrderStatisticSet<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<'a, T: Ord> IntoIterator for &'a OrderStatisticSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Ord> FromIterator<T> for OrderStatisticSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new();
        set.extend(iter);
        set
    }
}

impl<T: Ord> Extend<T> for OrderStatisticSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(value);
        }
    }
}

pub struct Iter<'a, T> {
    inner: super::map::Iter<'a, T, ()>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, ())| k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

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
                let op_type = rng.gen_range(0..5);
                match op_type {
                    0 | 1 => {
                        // insert
                        let value = rng.gen_range(0..n);
                        set.insert(value);
                        if !vec.contains(&value) {
                            let idx = vec.iter().position(|&v| v > value).unwrap_or(vec.len());
                            vec.insert(idx, value);
                        }
                    }
                    2 => {
                        // remove or take
                        let value = rng.gen_range(0..n);
                        if rng.gen_bool(0.5) {
                            set.remove(&value);
                        } else {
                            set.take(&value);
                        }
                        vec.retain(|&v| v != value);
                    }
                    3 => {
                        // remove_nth
                        if !vec.is_empty() {
                            let idx = rng.gen_range(0..vec.len());
                            set.remove_nth(idx);
                            vec.remove(idx);
                        }
                    }
                    4 => {
                        // pop_first or pop_last or replace
                        if !vec.is_empty() {
                            let choice = rng.gen_range(0..3);
                            match choice {
                                0 => {
                                    set.pop_first();
                                    vec.remove(0);
                                }
                                1 => {
                                    set.pop_last();
                                    vec.pop();
                                }
                                2 => {
                                    let value = rng.gen_range(0..n);
                                    set.replace(value);
                                    if !vec.contains(&value) {
                                        let idx =
                                            vec.iter().position(|&v| v > value).unwrap_or(vec.len());
                                        vec.insert(idx, value);
                                    }
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                    _ => unreachable!(),
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
}
