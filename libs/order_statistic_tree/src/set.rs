use super::map::OrderStatisticMap;
use std::borrow::Borrow;
use std::fmt;

/// An order-statistic set backed by a splay tree.
///
/// This data structure maintains unique values in sorted order and supports
/// order-statistic operations like `nth` and `binary_search`, all in amortized O(log n).
/// It is implemented as a wrapper around [`OrderStatisticMap<T, ()>`].
///
/// # Examples
///
/// ```
/// use order_statistic_tree::OrderStatisticSet;
///
/// let mut set = OrderStatisticSet::new();
/// set.insert(3);
/// set.insert(1);
/// set.insert(2);
///
/// assert_eq!(set.nth(0), &1);
/// assert!(set.contains(&2));
/// ```
pub struct OrderStatisticSet<T> {
    map: OrderStatisticMap<T, ()>,
}

impl<T: Ord> OrderStatisticSet<T> {
    // Group A: Core API
    /// Creates a new empty set.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let set = OrderStatisticSet::<i32>::new();
    /// assert!(set.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            map: OrderStatisticMap::new(),
        }
    }

    /// Returns the number of elements in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// assert_eq!(set.len(), 0);
    /// set.insert(1);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// assert!(set.is_empty());
    /// set.insert(1);
    /// assert!(!set.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Clears the set, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// set.clear();
    /// assert!(set.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Adds a value to the set, returning whether the value was newly inserted.
    ///
    /// Returns `true` if the value was not already in the set, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// assert!(set.insert(1));
    /// assert!(!set.insert(1)); // Already present
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.map.insert(value, ()).is_none()
    }

    /// Removes a value from the set, returning whether it was present.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// assert!(set.remove(&1));
    /// assert!(!set.remove(&1));
    /// ```
    pub fn remove<Q: Ord + ?Sized>(&mut self, value: &Q) -> bool
    where
        T: Borrow<Q>,
    {
        self.map.remove(value).is_some()
    }

    /// Returns `true` if the set contains the specified value.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// assert!(set.contains(&1));
    /// assert!(!set.contains(&2));
    /// ```
    pub fn contains<Q: Ord + ?Sized>(&self, value: &Q) -> bool
    where
        T: Borrow<Q>,
    {
        self.map.contains_key(value)
    }

    /// Returns an iterator over the set in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(3);
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// let values: Vec<_> = set.iter().collect();
    /// assert_eq!(values, vec![&1, &2, &3]);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            inner: self.map.iter(),
        }
    }

    // Group B: Frequently used
    /// Returns a reference to the value in the set that is equal to the given value, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// assert_eq!(set.get(&1), Some(&1));
    /// assert_eq!(set.get(&2), None);
    /// ```
    pub fn get<Q: Ord + ?Sized>(&self, value: &Q) -> Option<&T>
    where
        T: Borrow<Q>,
    {
        self.map.get_key_value(value).map(|(k, ())| k)
    }

    /// Removes and returns the value in the set that is equal to the given value, if any.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// assert_eq!(set.take(&1), Some(1));
    /// assert_eq!(set.take(&1), None);
    /// ```
    pub fn take<Q: Ord + ?Sized>(&mut self, value: &Q) -> Option<T>
    where
        T: Borrow<Q>,
    {
        self.map.remove_entry(value).map(|(k, ())| k)
    }

    /// Adds a value to the set, replacing an existing value if it equals the given one and
    /// returning the old value.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// assert_eq!(set.replace(1), Some(1));
    /// assert_eq!(set.replace(2), None);
    /// ```
    pub fn replace(&mut self, value: T) -> Option<T> {
        let old = self.map.remove_entry(&value).map(|(k, ())| k);
        self.map.insert(value, ());
        old
    }

    /// Returns a reference to the smallest value in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// assert_eq!(set.first(), None);
    /// set.insert(2);
    /// set.insert(1);
    /// assert_eq!(set.first(), Some(&1));
    /// ```
    pub fn first(&self) -> Option<&T> {
        self.map.first_key_value().map(|(k, ())| k)
    }

    /// Returns a reference to the largest value in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// assert_eq!(set.last(), None);
    /// set.insert(2);
    /// set.insert(1);
    /// assert_eq!(set.last(), Some(&2));
    /// ```
    pub fn last(&self) -> Option<&T> {
        self.map.last_key_value().map(|(k, ())| k)
    }

    /// Removes and returns the smallest value in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(2);
    /// set.insert(1);
    /// assert_eq!(set.pop_first(), Some(1));
    /// ```
    pub fn pop_first(&mut self) -> Option<T> {
        self.map.pop_first().map(|(k, ())| k)
    }

    /// Removes and returns the largest value in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(2);
    /// set.insert(1);
    /// assert_eq!(set.pop_last(), Some(2));
    /// ```
    pub fn pop_last(&mut self) -> Option<T> {
        self.map.pop_last().map(|(k, ())| k)
    }

    // Group C: Order statistic
    /// Returns a reference to the value at the given index.
    ///
    /// The values are indexed in sorted order, starting from 0.
    ///
    /// # Panics
    ///
    /// Panics if `n >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(3);
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// assert_eq!(set.nth(0), &1);
    /// assert_eq!(set.nth(1), &2);
    /// assert_eq!(set.nth(2), &3);
    /// ```
    pub fn nth(&self, n: usize) -> &T {
        self.map.nth(n).0
    }

    /// Removes and returns the value at the given index.
    ///
    /// The values are indexed in sorted order, starting from 0.
    ///
    /// # Panics
    ///
    /// Panics if `n >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(3);
    /// set.insert(1);
    /// set.insert(2);
    ///
    /// assert_eq!(set.remove_nth(1), 2);
    /// assert_eq!(set.len(), 2);
    /// ```
    pub fn remove_nth(&mut self, n: usize) -> T {
        self.map.remove_nth(n).0
    }

    /// Searches for a value and returns its index if found, or the insertion position if not.
    ///
    /// Returns `Ok(rank)` if the value is found, where `rank` is its index in sorted order.
    /// Returns `Err(rank)` if the value is not found, where `rank` is the index where the
    /// value would be inserted to maintain sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// set.insert(3);
    ///
    /// assert_eq!(set.binary_search(&1), Ok(0));
    /// assert_eq!(set.binary_search(&2), Err(1));
    /// assert_eq!(set.binary_search(&3), Ok(1));
    /// ```
    pub fn binary_search<Q: Ord + ?Sized>(&self, value: &Q) -> Result<usize, usize>
    where
        T: Borrow<Q>,
    {
        self.map.binary_search(value)
    }

    /// Returns the index of the first value that is not less than the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// set.insert(3);
    /// set.insert(5);
    ///
    /// assert_eq!(set.lower_bound(&1), 0);
    /// assert_eq!(set.lower_bound(&2), 1);
    /// assert_eq!(set.lower_bound(&6), 3);
    /// ```
    pub fn lower_bound<Q: Ord + ?Sized>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
    {
        self.map.lower_bound(value)
    }

    /// Returns the index of the first value that is strictly greater than the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// set.insert(3);
    /// set.insert(5);
    ///
    /// assert_eq!(set.upper_bound(&1), 1);
    /// assert_eq!(set.upper_bound(&2), 1);
    /// assert_eq!(set.upper_bound(&6), 3);
    /// ```
    pub fn upper_bound<Q: Ord + ?Sized>(&self, value: &Q) -> usize
    where
        T: Borrow<Q>,
    {
        self.map.upper_bound(value)
    }
}

/// Creates an empty set. Equivalent to [`OrderStatisticSet::new`].
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

/// Creates an iterator over the set. Equivalent to [`OrderStatisticSet::iter`].
impl<'a, T: Ord> IntoIterator for &'a OrderStatisticSet<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Constructs a set from an iterator of values.
impl<T: Ord> FromIterator<T> for OrderStatisticSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new();
        set.extend(iter);
        set
    }
}

/// Extends the set with the contents of an iterator of values.
impl<T: Ord> Extend<T> for OrderStatisticSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for value in iter {
            self.insert(value);
        }
    }
}

/// An iterator over the values of an [`OrderStatisticSet`], yielding them in sorted order.
///
/// This iterator is returned by the [`OrderStatisticSet::iter`] method.
///
/// # Examples
///
/// ```
/// use order_statistic_tree::OrderStatisticSet;
///
/// let mut set = OrderStatisticSet::new();
/// set.insert(1);
/// set.insert(2);
///
/// for value in set.iter() {
///     println!("{}", value);
/// }
/// ```
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
