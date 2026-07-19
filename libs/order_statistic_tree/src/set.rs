//! v1では未対応: entry, range/range_mut, retain, values_mut, into_iter

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

    /// Concatenates `other` into `self`, requiring all values in `self` to be strictly less than
    /// all values in `other`.
    ///
    /// After this operation, `other` becomes empty and `self` contains all values from both
    /// sets, sorted. This operation takes O(log n) amortized time.
    ///
    /// # Panics
    ///
    /// Panics if both sets are non-empty and the maximum value in `self` is not strictly less
    /// than the minimum value in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set1 = OrderStatisticSet::new();
    /// set1.insert(1);
    /// set1.insert(2);
    ///
    /// let mut set2 = OrderStatisticSet::new();
    /// set2.insert(3);
    /// set2.insert(4);
    ///
    /// set1.concat(&mut set2);
    /// assert_eq!(set1.len(), 4);
    /// assert!(set2.is_empty());
    /// ```
    pub fn concat(&mut self, other: &mut Self) {
        self.map.concat(&mut other.map);
    }

    /// Splits the set into two at the given split value, returning a new set containing all
    /// values greater than or equal to the split value.
    ///
    /// This operation takes O(log n) amortized time. The original set retains all values
    /// strictly less than the split value.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticSet;
    ///
    /// let mut set = OrderStatisticSet::new();
    /// set.insert(1);
    /// set.insert(2);
    /// set.insert(3);
    /// set.insert(4);
    ///
    /// let high = set.split_off(&3);
    /// assert_eq!(set.len(), 2);
    /// assert_eq!(high.len(), 2);
    /// assert!(set.contains(&1));
    /// assert!(high.contains(&3));
    /// ```
    pub fn split_off<Q: Ord + ?Sized>(&mut self, value: &Q) -> Self
    where
        T: Borrow<Q>,
    {
        Self {
            map: self.map.split_off(value),
        }
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
    inner: super::map::Iter<'a, T, (), super::map::NoOp<T, ()>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, ())| k)
    }
}

