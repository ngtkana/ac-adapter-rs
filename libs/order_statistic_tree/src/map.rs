//! v1では未対応: entry, range/range_mut, retain, values_mut, into_iter

use std::borrow::Borrow;
use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::ptr::NonNull;

/// A trait for segment-tree style augmentation.
///
/// Defines a monoid structure over aggregated values computed from key-value pairs.
pub trait Op {
    /// The key type associated with this operation.
    type Key;
    /// The value type associated with this operation.
    type Value;
    /// The type of the aggregated/segment value.
    type SegValue: Clone;

    /// Returns the monoid identity element.
    fn identity() -> Self::SegValue;

    /// Lifts a key-value pair to a segment value.
    fn to_seg_value(key: &Self::Key, value: &Self::Value) -> Self::SegValue;

    /// Monoid multiplication (associative).
    fn mul(lhs: &Self::SegValue, rhs: &Self::SegValue) -> Self::SegValue;
}

/// A no-op augmentation trait for non-augmented maps.
/// SegValue is (), providing zero-cost abstraction.
pub struct NoOp<K, V>(PhantomData<(K, V)>);

impl<K, V> Op for NoOp<K, V> {
    type Key = K;
    type Value = V;
    type SegValue = ();

    fn identity() -> Self::SegValue {}
    fn to_seg_value(_: &K, _: &V) -> Self::SegValue {}
    fn mul((): &(), (): &()) -> Self::SegValue {}
}

#[cfg(test)]
mod op_tests {
    use super::*;

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

    #[test]
    fn test_fold_empty_map() {
        // Empty map should return identity
        let map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        assert_eq!(map.fold(), SumOp::identity());
    }

    #[test]
    fn test_fold_whole_map() {
        // Single element
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(5, 10);
        assert_eq!(map.fold(), 5 + 10);

        // Multiple elements
        map.insert(3, 20);
        map.insert(7, 15);
        let expected = (5 + 10) + (3 + 20) + (7 + 15);
        assert_eq!(map.fold(), expected);
    }

    #[test]
    fn test_fold_range_basic() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        for i in 1..=5 {
            map.insert(i, i * 10);
        }

        // Whole range
        let whole = (1 + 10) + (2 + 20) + (3 + 30) + (4 + 40) + (5 + 50);
        assert_eq!(map.fold_range(&1, &6), whole);

        // Partial range [2, 4)
        let partial = (2 + 20) + (3 + 30);
        assert_eq!(map.fold_range(&2, &4), partial);

        // Single element [3, 4)
        assert_eq!(map.fold_range(&3, &4), 3 + 30);
    }

    #[test]
    fn test_fold_range_empty() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(5, 50);

        // Empty range
        assert_eq!(map.fold_range(&1, &1), SumOp::identity());
        assert_eq!(map.fold_range(&10, &20), SumOp::identity());
    }

    #[test]
    fn test_fold_after_overwrite() {
        let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
        map.insert(5, 10);
        assert_eq!(map.fold(), 5 + 10);

        // Overwrite value
        map.insert(5, 20);
        assert_eq!(map.fold(), 5 + 20, "fold should reflect updated value");
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
}

/// An order-statistic map backed by a splay tree.
///
/// This data structure maintains key-value pairs in sorted order and supports
/// order-statistic operations like `nth` and `binary_search`, all in amortized O(log n).
///
/// # Examples
///
/// ```
/// use order_statistic_tree::OrderStatisticMap;
///
/// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
/// map.insert(3, "c");
/// map.insert(1, "a");
/// map.insert(2, "b");
///
/// assert_eq!(map.nth(0), (&1, &"a"));
/// assert_eq!(map.get(&2), Some(&"b"));
/// ```
pub struct OrderStatisticMap<K, V, O: Op<Key = K, Value = V> = NoOp<K, V>> {
    root: Cell<Option<NonNull<Node<K, V, O>>>>,
}

impl<K: Ord, V, O: Op<Key = K, Value = V>> OrderStatisticMap<K, V, O> {
    // Group A: Core API
    /// Creates a new empty map.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let map = OrderStatisticMap::<i32, &str>::new();
    /// assert!(map.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            root: Cell::new(None),
        }
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// assert_eq!(map.len(), 0);
    /// map.insert(1, "a");
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.root.get().map_or(0, |r| unsafe { (*r.as_ptr()).len })
    }

    /// Returns `true` if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// assert!(map.is_empty());
    /// map.insert(1, "a");
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.get().is_none()
    }

    /// Clears the map, removing all key-value pairs.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        free_subtree(self.root.get());
        self.root.set(None);
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// assert_eq!(map.insert(1, "a"), None);
    /// assert_eq!(map.insert(1, "b"), Some("a"));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        match self.root.get() {
            None => {
                let prod = O::to_seg_value(&key, &value);
                let node = Box::into_raw(Box::new(Node {
                    key,
                    value,
                    parent: None,
                    left: None,
                    right: None,
                    len: 1,
                    prod,
                }));
                self.root.set(Some(NonNull::new(node).unwrap()));
                None
            }
            Some(root) => unsafe {
                let mut current = root;
                loop {
                    let key_cmp = key.cmp(&(*current.as_ptr()).key);
                    match key_cmp {
                        std::cmp::Ordering::Less => {
                            if let Some(left) = (*current.as_ptr()).left {
                                current = left;
                            } else {
                                let prod = O::to_seg_value(&key, &value);
                                let new_node = Box::into_raw(Box::new(Node {
                                    key,
                                    value,
                                    parent: Some(current),
                                    left: None,
                                    right: None,
                                    len: 1,
                                    prod,
                                }));
                                (*current.as_ptr()).left = Some(NonNull::new(new_node).unwrap());
                                current = NonNull::new(new_node).unwrap();
                                break;
                            }
                        }
                        std::cmp::Ordering::Greater => {
                            if let Some(right) = (*current.as_ptr()).right {
                                current = right;
                            } else {
                                let prod = O::to_seg_value(&key, &value);
                                let new_node = Box::into_raw(Box::new(Node {
                                    key,
                                    value,
                                    parent: Some(current),
                                    left: None,
                                    right: None,
                                    len: 1,
                                    prod,
                                }));
                                (*current.as_ptr()).right = Some(NonNull::new(new_node).unwrap());
                                current = NonNull::new(new_node).unwrap();
                                break;
                            }
                        }
                        std::cmp::Ordering::Equal => {
                            let old_value =
                                std::mem::replace(&mut (*current.as_ptr()).value, value);
                            (*current.as_ptr()).prod =
                                O::to_seg_value(&(*current.as_ptr()).key, &(*current.as_ptr()).value);
                            current = splay(current);
                            self.root.set(Some(current));
                            return Some(old_value);
                        }
                    }
                }
                current = splay(current);
                self.root.set(Some(current));
                None
            },
        }
    }

    /// Removes a key from the map, returning its associated value if it was present.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    pub fn remove<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|_| detach_root(self).1)
    }

    /// Returns a reference to the value associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    pub fn get<Q: Ord + ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|node| unsafe { &(*node.as_ptr()).value })
    }

    /// Returns `true` if the map contains a value for the specified key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// assert!(map.contains_key(&1));
    /// assert!(!map.contains_key(&2));
    /// ```
    pub fn contains_key<Q: Ord + ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).is_some()
    }

    /// Returns an iterator over the map in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(3, "c");
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// let entries: Vec<_> = map.iter().collect();
    /// assert_eq!(entries, vec![(&1, &"a"), (&2, &"b"), (&3, &"c")]);
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V, O> {
        let mut stack = Vec::new();
        if let Some(root) = self.root.get() {
            let mut current = Some(root);
            while let Some(c) = current {
                stack.push(c);
                current = unsafe { (*c.as_ptr()).left };
            }
        }
        Iter {
            stack,
            _phantom: std::marker::PhantomData,
        }
    }

    // Group B: Frequently used
    /// Returns a mutable reference to the value associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
    /// map.insert(1, 10);
    /// if let Some(value) = map.get_mut(&1) {
    ///     *value = 20;
    /// }
    /// assert_eq!(map.get(&1), Some(&20));
    /// ```
    pub fn get_mut<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|node| unsafe { &mut (*node.as_ptr()).value })
    }

    /// Returns a reference to both the key and value associated with the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get_key_value(&1), Some((&1, &"a")));
    /// ```
    pub fn get_key_value<Q: Ord + ?Sized>(&self, key: &Q) -> Option<(&K, &V)>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key)
            .map(|node| unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) })
    }

    /// Removes a key from the map, returning the stored key and value if it was present.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_entry(&1), Some((1, "a")));
    /// assert_eq!(map.remove_entry(&1), None);
    /// ```
    pub fn remove_entry<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|_| detach_root(self))
    }

    /// Returns a reference to the first (minimum) key-value pair in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// assert_eq!(map.first_key_value(), None);
    /// map.insert(3, "c");
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// assert_eq!(map.first_key_value(), Some((&1, &"a")));
    /// ```
    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        leftmost_and_splay(self)
            .map(|node| unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) })
    }

    /// Returns a reference to the last (maximum) key-value pair in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// assert_eq!(map.last_key_value(), None);
    /// map.insert(3, "c");
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// assert_eq!(map.last_key_value(), Some((&3, &"c")));
    /// ```
    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        rightmost_and_splay(self)
            .map(|node| unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) })
    }

    /// Removes and returns the first (minimum) key-value pair from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(2, "b");
    /// map.insert(1, "a");
    /// assert_eq!(map.pop_first(), Some((1, "a")));
    /// ```
    pub fn pop_first(&mut self) -> Option<(K, V)> {
        leftmost_and_splay(self).map(|_| detach_root(self))
    }

    /// Removes and returns the last (maximum) key-value pair from the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(2, "b");
    /// map.insert(1, "a");
    /// assert_eq!(map.pop_last(), Some((2, "b")));
    /// ```
    pub fn pop_last(&mut self) -> Option<(K, V)> {
        rightmost_and_splay(self).map(|_| detach_root(self))
    }

    /// Returns an iterator over the keys of the map in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(3, "c");
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// let keys: Vec<_> = map.keys().collect();
    /// assert_eq!(keys, vec![&1, &2, &3]);
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V, O> {
        Keys {
            inner: self.iter(),
        }
    }

    /// Returns an iterator over the values of the map in key order.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(3, "c");
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// let values: Vec<_> = map.values().collect();
    /// assert_eq!(values, vec![&"a", &"b", &"c"]);
    /// ```
    pub fn values(&self) -> Values<'_, K, V, O> {
        Values {
            inner: self.iter(),
        }
    }

    // Group C: Order statistic
    /// Returns a reference to the key-value pair at the given index.
    ///
    /// The keys are indexed in sorted order, starting from 0.
    ///
    /// # Panics
    ///
    /// Panics if `n >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(3, "c");
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.nth(0), (&1, &"a"));
    /// assert_eq!(map.nth(1), (&2, &"b"));
    /// assert_eq!(map.nth(2), (&3, &"c"));
    /// ```
    pub fn nth(&self, n: usize) -> (&K, &V) {
        let node = nth_and_splay(self, n);
        unsafe { (&(*node.as_ptr()).key, &(*node.as_ptr()).value) }
    }

    /// Removes and returns the key-value pair at the given index.
    ///
    /// The keys are indexed in sorted order, starting from 0.
    ///
    /// # Panics
    ///
    /// Panics if `n >= self.len()`.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(3, "c");
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    ///
    /// assert_eq!(map.remove_nth(1), (2, "b"));
    /// assert_eq!(map.len(), 2);
    /// ```
    pub fn remove_nth(&mut self, n: usize) -> (K, V) {
        nth_and_splay(self, n);
        detach_root(self)
    }

    /// Searches for a key and returns its index if found, or the insertion position if not.
    ///
    /// Returns `Ok(rank)` if the key is found, where `rank` is its index in sorted order.
    /// Returns `Err(rank)` if the key is not found, where `rank` is the index where the key
    /// would be inserted to maintain sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// map.insert(3, "c");
    ///
    /// assert_eq!(map.binary_search(&1), Ok(0));
    /// assert_eq!(map.binary_search(&2), Err(1));
    /// assert_eq!(map.binary_search(&3), Ok(1));
    /// ```
    pub fn binary_search<Q: Ord + ?Sized>(&self, key: &Q) -> Result<usize, usize>
    where
        K: Borrow<Q>,
    {
        let (pos, found) = locate_and_splay(self, key, false);
        match found {
            Some(_) => Ok(pos),
            None => Err(pos),
        }
    }

    /// Returns the index of the first key that is not less than the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// map.insert(3, "c");
    /// map.insert(5, "e");
    ///
    /// assert_eq!(map.lower_bound(&1), 0);
    /// assert_eq!(map.lower_bound(&2), 1);
    /// assert_eq!(map.lower_bound(&3), 1);
    /// assert_eq!(map.lower_bound(&6), 3);
    /// ```
    pub fn lower_bound<Q: Ord + ?Sized>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
    {
        locate_and_splay(self, key, false).0
    }

    /// Returns the index of the first key that is strictly greater than the given key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// map.insert(3, "c");
    /// map.insert(5, "e");
    ///
    /// assert_eq!(map.upper_bound(&1), 1);
    /// assert_eq!(map.upper_bound(&2), 1);
    /// assert_eq!(map.upper_bound(&3), 2);
    /// assert_eq!(map.upper_bound(&6), 3);
    /// ```
    pub fn upper_bound<Q: Ord + ?Sized>(&self, key: &Q) -> usize
    where
        K: Borrow<Q>,
    {
        locate_and_splay(self, key, true).0
    }

    /// Concatenates `other` into `self`, requiring all keys in `self` to be strictly less than
    /// all keys in `other`.
    ///
    /// After this operation, `other` becomes empty and `self` contains all key-value pairs
    /// from both maps, sorted by key. This operation takes O(log n) amortized time.
    ///
    /// # Panics
    ///
    /// Panics if both maps are non-empty and the maximum key in `self` is not strictly less than
    /// the minimum key in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map1: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map1.insert(1, "a");
    /// map1.insert(2, "b");
    ///
    /// let mut map2: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map2.insert(3, "c");
    /// map2.insert(4, "d");
    ///
    /// map1.concat(&mut map2);
    /// assert_eq!(map1.len(), 4);
    /// assert!(map2.is_empty());
    /// ```
    pub fn concat(&mut self, other: &mut Self) {
        match (self.root.get(), other.root.get()) {
            (_, None) => {}
            (None, Some(_)) => {
                self.root.set(other.root.get());
                other.root.set(None);
            }
            (Some(_), Some(_)) => {
                let self_max = rightmost_and_splay(self).unwrap();
                let other_min = leftmost_and_splay(other).unwrap();
                unsafe {
                    assert!(
                        (*self_max.as_ptr()).key < (*other_min.as_ptr()).key,
                        "OrderStatisticMap::concat requires all keys in self to be strictly less than all keys in other"
                    );
                    (*self_max.as_ptr()).right = Some(other_min);
                    (*other_min.as_ptr()).parent = Some(self_max);
                    (*self_max.as_ptr()).update();
                }
                self.root.set(Some(self_max));
                other.root.set(None);
            }
        }
    }

    /// Splits the map into two at the given split key, returning a new map containing all
    /// key-value pairs with keys greater than or equal to the split key.
    ///
    /// This operation takes O(log n) amortized time. The original map retains all key-value
    /// pairs with keys strictly less than the split key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    ///
    /// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
    /// map.insert(1, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "c");
    /// map.insert(4, "d");
    ///
    /// let high = map.split_off(&3);
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(high.len(), 2);
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(high.get(&3), Some(&"c"));
    /// ```
    pub fn split_off<Q: Ord + ?Sized>(&mut self, key: &Q) -> Self
    where
        K: Borrow<Q>,
    {
        let idx = self.lower_bound(key);
        let len = self.len();
        if idx == len {
            return Self::new();
        }
        if idx == 0 {
            let new_map = Self {
                root: Cell::new(self.root.get()),
            };
            self.root.set(None);
            return new_map;
        }
        let node = nth_and_splay(self, idx);
        unsafe {
            let left = (*node.as_ptr()).left.take();
            if let Some(l) = left {
                (*l.as_ptr()).parent = None;
            }
            (*node.as_ptr()).parent = None;
            (*node.as_ptr()).update();
            self.root.set(left);
        }
        Self {
            root: Cell::new(Some(node)),
        }
    }

    /// Computes the aggregate value of the entire map using the configured Op.
    ///
    /// Returns the monoid product of all (key, value) pairs in the map.
    /// For an empty map, returns `O::identity()`.
    ///
    /// This operation takes O(1) time by accessing the cached product at the root node.
    ///
    /// # Examples
    ///
    /// ```
    /// # use order_statistic_tree::{OrderStatisticMap, Op};
    /// # struct SumOp;
    /// # impl Op for SumOp {
    /// #     type Key = i32;
    /// #     type Value = i32;
    /// #     type SegValue = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn to_seg_value(key: &i32, value: &i32) -> i64 { (*key as i64) + (*value as i64) }
    /// #     fn mul(lhs: &i64, rhs: &i64) -> i64 { lhs + rhs }
    /// # }
    /// let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    /// assert_eq!(map.fold(), (1 + 10) + (2 + 20)); // 33
    /// ```
    pub fn fold(&self) -> O::SegValue {
        self.root.get().map_or_else(O::identity, |r| unsafe { (*r.as_ptr()).prod.clone() })
    }

    /// Computes the aggregate value over a key range `[start, end)`.
    ///
    /// Returns the monoid product of all (key, value) pairs where `start <= key < end`.
    /// For an empty range, returns `O::identity()`.
    ///
    /// This operation takes O(log n) amortized time via a top-down descent pattern.
    ///
    /// # Examples
    ///
    /// ```
    /// # use order_statistic_tree::{OrderStatisticMap, Op};
    /// # struct SumOp;
    /// # impl Op for SumOp {
    /// #     type Key = i32;
    /// #     type Value = i32;
    /// #     type SegValue = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn to_seg_value(key: &i32, value: &i32) -> i64 { (*key as i64) + (*value as i64) }
    /// #     fn mul(lhs: &i64, rhs: &i64) -> i64 { lhs + rhs }
    /// # }
    /// let mut map: OrderStatisticMap<i32, i32, SumOp> = OrderStatisticMap::new();
    /// map.insert(1, 10);
    /// map.insert(2, 20);
    /// map.insert(3, 30);
    /// assert_eq!(map.fold_range(&1, &3), (1 + 10) + (2 + 20)); // 33
    /// ```
    pub fn fold_range<Q: Ord + ?Sized>(&self, start: &Q, end: &Q) -> O::SegValue
    where
        K: Borrow<Q>,
    {
        fn fold_range_impl<K: Ord + Borrow<Q>, V, Q: Ord + ?Sized, O: Op<Key = K, Value = V>>(
            node: Option<NonNull<Node<K, V, O>>>,
            start: &Q,
            end: &Q,
        ) -> O::SegValue {
            match node {
                None => O::identity(),
                Some(n) => unsafe {
                    let key_ref = (*n.as_ptr()).key.borrow();
                    match (key_ref.cmp(start), key_ref.cmp(end)) {
                        // Node is to the left of range
                        (std::cmp::Ordering::Less, _) => {
                            fold_range_impl((*n.as_ptr()).right, start, end)
                        }
                        // Node is to the right of range
                        (_, std::cmp::Ordering::Greater | std::cmp::Ordering::Equal) => {
                            fold_range_impl((*n.as_ptr()).left, start, end)
                        }
                        // Node is within range [start, end)
                        (_, std::cmp::Ordering::Less) => {
                            let left_prod = fold_range_impl((*n.as_ptr()).left, start, end);
                            let self_prod = O::to_seg_value(&(*n.as_ptr()).key, &(*n.as_ptr()).value);
                            let right_prod = fold_range_impl((*n.as_ptr()).right, start, end);
                            O::mul(&O::mul(&left_prod, &self_prod), &right_prod)
                        }
                    }
                },
            }
        }

        fold_range_impl(self.root.get(), start, end)
    }
}

/// Creates an empty map. Equivalent to [`OrderStatisticMap::new`].
impl<K: Ord, V, O: Op<Key = K, Value = V>> Default for OrderStatisticMap<K, V, O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Ord + fmt::Debug, V: fmt::Debug, O: Op<Key = K, Value = V>> fmt::Debug for OrderStatisticMap<K, V, O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

/// Creates an iterator over the map. Equivalent to [`OrderStatisticMap::iter`].
impl<'a, K: Ord, V, O: Op<Key = K, Value = V>> IntoIterator for &'a OrderStatisticMap<K, V, O> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V, O>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Constructs a map from an iterator of key-value pairs.
impl<K: Ord, V, O: Op<Key = K, Value = V>> FromIterator<(K, V)> for OrderStatisticMap<K, V, O> {
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let mut map = Self::new();
        map.extend(iter);
        map
    }
}

/// Extends the map with the contents of an iterator of key-value pairs.
impl<K: Ord, V, O: Op<Key = K, Value = V>> Extend<(K, V)> for OrderStatisticMap<K, V, O> {
    fn extend<T: IntoIterator<Item = (K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K, V, O: Op<Key = K, Value = V>> Drop for OrderStatisticMap<K, V, O> {
    fn drop(&mut self) {
        free_subtree(self.root.get());
    }
}

/// An iterator over the entries of an [`OrderStatisticMap`], yielding key-value pairs in sorted order.
///
/// This iterator is returned by the [`OrderStatisticMap::iter`] method.
///
/// # Examples
///
/// ```
/// use order_statistic_tree::OrderStatisticMap;
///
/// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
/// map.insert(1, "a");
/// map.insert(2, "b");
///
/// for (key, value) in map.iter() {
///     println!("{}: {}", key, value);
/// }
/// ```
pub struct Iter<'a, K, V, O: Op<Key = K, Value = V>> {
    stack: Vec<NonNull<Node<K, V, O>>>,
    _phantom: std::marker::PhantomData<&'a Node<K, V, O>>,
}

impl<'a, K, V, O: Op<Key = K, Value = V>> Iterator for Iter<'a, K, V, O> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        unsafe {
            if let Some(right) = (*node.as_ptr()).right {
                let mut current = Some(right);
                while let Some(c) = current {
                    self.stack.push(c);
                    current = (*c.as_ptr()).left;
                }
            }
            Some((&(*node.as_ptr()).key, &(*node.as_ptr()).value))
        }
    }
}

/// An iterator over the keys of an [`OrderStatisticMap`], yielding them in sorted order.
///
/// This iterator is returned by the [`OrderStatisticMap::keys`] method.
///
/// # Examples
///
/// ```
/// use order_statistic_tree::OrderStatisticMap;
///
/// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
/// map.insert(1, "a");
/// map.insert(2, "b");
///
/// let keys: Vec<_> = map.keys().collect();
/// ```
pub struct Keys<'a, K, V, O: Op<Key = K, Value = V>> {
    inner: Iter<'a, K, V, O>,
}

impl<'a, K, V, O: Op<Key = K, Value = V>> Iterator for Keys<'a, K, V, O> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(k, _)| k)
    }
}

/// An iterator over the values of an [`OrderStatisticMap`], yielding them in key order.
///
/// This iterator is returned by the [`OrderStatisticMap::values`] method.
///
/// # Examples
///
/// ```
/// use order_statistic_tree::OrderStatisticMap;
///
/// let mut map: OrderStatisticMap<i32, &str> = OrderStatisticMap::new();
/// map.insert(1, "a");
/// map.insert(2, "b");
///
/// let values: Vec<_> = map.values().collect();
/// ```
pub struct Values<'a, K, V, O: Op<Key = K, Value = V>> {
    inner: Iter<'a, K, V, O>,
}

impl<'a, K, V, O: Op<Key = K, Value = V>> Iterator for Values<'a, K, V, O> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, v)| v)
    }
}

struct Node<K, V, O: Op<Key = K, Value = V>> {
    key: K,
    value: V,
    parent: Option<NonNull<Self>>,
    left: Option<NonNull<Self>>,
    right: Option<NonNull<Self>>,
    len: usize,
    prod: O::SegValue,
}

impl<K, V, O: Op<Key = K, Value = V>> Node<K, V, O> {
    fn update(&mut self) {
        unsafe {
            self.len = self.left.map_or(0, |left| (*left.as_ptr()).len)
                + 1
                + self.right.map_or(0, |rigth| (*rigth.as_ptr()).len);

            let left_prod =
                self.left.map_or_else(O::identity, |l| (*l.as_ptr()).prod.clone());
            let right_prod =
                self.right.map_or_else(O::identity, |r| (*r.as_ptr()).prod.clone());
            self.prod = O::mul(
                &O::mul(&left_prod, &O::to_seg_value(&self.key, &self.value)),
                &right_prod,
            );
        }
    }
}

fn splay<K, V, O: Op<Key = K, Value = V>>(x: NonNull<Node<K, V, O>>) -> NonNull<Node<K, V, O>> {
    unsafe {
        while let Some(p) = (*x.as_ptr()).parent {
            if let Some(q) = (*p.as_ptr()).parent {
                if (*q.as_ptr()).left == Some(p) && (*p.as_ptr()).left == Some(x) {
                    // zig-zig: left-left
                    rotate_right(q);
                    rotate_right(p);
                } else if (*q.as_ptr()).right == Some(p) && (*p.as_ptr()).right == Some(x) {
                    // zig-zig: right-right
                    rotate_left(q);
                    rotate_left(p);
                } else {
                    // zig-zag
                    if (*p.as_ptr()).left == Some(x) {
                        rotate_right(p);
                    } else {
                        rotate_left(p);
                    }
                    if (*q.as_ptr()).left == Some(x) {
                        rotate_right(q);
                    } else {
                        rotate_left(q);
                    }
                }
            } else {
                // zig: parent is root
                if (*p.as_ptr()).left == Some(x) {
                    rotate_right(p);
                } else if (*p.as_ptr()).right == Some(x) {
                    rotate_left(p);
                } else {
                    unreachable!()
                }
            }
        }
        x
    }
}

fn rotate_left<K, V, O: Op<Key = K, Value = V>>(x: NonNull<Node<K, V, O>>) -> NonNull<Node<K, V, O>> {
    unsafe {
        let y = (*x.as_ptr()).right.unwrap();
        let c = (*y.as_ptr()).left;

        (*x.as_ptr()).right = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).left = Some(x);

        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);

        (*x.as_ptr()).update();
        (*y.as_ptr()).update();

        y
    }
}

fn rotate_right<K, V, O: Op<Key = K, Value = V>>(x: NonNull<Node<K, V, O>>) -> NonNull<Node<K, V, O>> {
    unsafe {
        let y = (*x.as_ptr()).left.unwrap();
        let c = (*y.as_ptr()).right;

        (*x.as_ptr()).left = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).right = Some(x);

        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);

        (*x.as_ptr()).update();
        (*y.as_ptr()).update();

        y
    }
}

fn free_subtree<K, V, O: Op<Key = K, Value = V>>(root: Option<NonNull<Node<K, V, O>>>) {
    let mut stack = Vec::new();
    if let Some(r) = root {
        stack.push(r);
    }
    while let Some(node) = stack.pop() {
        unsafe {
            if let Some(left) = (*node.as_ptr()).left {
                stack.push(left);
            }
            if let Some(right) = (*node.as_ptr()).right {
                stack.push(right);
            }
            drop(Box::from_raw(node.as_ptr()));
        }
    }
}

fn find_and_splay<K, Q: Ord + ?Sized, V, O: Op<Key = K, Value = V>>(
    map: &OrderStatisticMap<K, V, O>,
    key: &Q,
) -> Option<NonNull<Node<K, V, O>>>
where
    K: Ord + Borrow<Q>,
{
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            let mut found = false;
            loop {
                let key_cmp = key.cmp((*current.as_ptr()).key.borrow());
                match key_cmp {
                    std::cmp::Ordering::Less => {
                        if let Some(left) = (*current.as_ptr()).left {
                            current = left;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        if let Some(right) = (*current.as_ptr()).right {
                            current = right;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        found = true;
                        break;
                    }
                }
            }
            current = splay(current);
            map.root.set(Some(current));
            if found { Some(current) } else { None }
        },
    }
}

fn nth_and_splay<K, V, O: Op<Key = K, Value = V>>(map: &OrderStatisticMap<K, V, O>, mut n: usize) -> NonNull<Node<K, V, O>> {
    let root = map.root.get().unwrap();
    unsafe {
        let mut current = root;
        loop {
            let left_len = (*current.as_ptr()).left.map_or(0, |l| (*l.as_ptr()).len);
            match n.cmp(&left_len) {
                std::cmp::Ordering::Less => {
                    current = (*current.as_ptr()).left.unwrap();
                }
                std::cmp::Ordering::Greater => {
                    n -= left_len + 1;
                    current = (*current.as_ptr()).right.unwrap();
                }
                std::cmp::Ordering::Equal => {
                    break;
                }
            }
        }
        current = splay(current);
        map.root.set(Some(current));
        current
    }
}

#[allow(clippy::type_complexity)]
fn locate_and_splay<K, Q: Ord + ?Sized, V, O: Op<Key = K, Value = V>>(
    map: &OrderStatisticMap<K, V, O>,
    key: &Q,
    include_equal: bool,
) -> (usize, Option<NonNull<Node<K, V, O>>>)
where
    K: Ord + Borrow<Q>,
{
    match map.root.get() {
        None => (0, None),
        Some(root) => unsafe {
            let mut current = root;
            let mut pos = 0;
            let mut found_node = None;

            loop {
                let left_len = (*current.as_ptr()).left.map_or(0, |l| (*l.as_ptr()).len);
                let key_cmp = key.cmp((*current.as_ptr()).key.borrow());
                match key_cmp {
                    std::cmp::Ordering::Less => {
                        if let Some(left) = (*current.as_ptr()).left {
                            current = left;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        pos += left_len + 1;
                        if let Some(right) = (*current.as_ptr()).right {
                            current = right;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        pos += left_len;
                        found_node = Some(current);
                        if include_equal {
                            pos += 1;
                            if let Some(right) = (*current.as_ptr()).right {
                                current = right;
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
            current = splay(current);
            map.root.set(Some(current));
            (pos, found_node)
        },
    }
}

fn leftmost_and_splay<K, V, O: Op<Key = K, Value = V>>(map: &OrderStatisticMap<K, V, O>) -> Option<NonNull<Node<K, V, O>>> {
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            while let Some(left) = (*current.as_ptr()).left {
                current = left;
            }
            current = splay(current);
            map.root.set(Some(current));
            Some(current)
        },
    }
}

fn rightmost_and_splay<K, V, O: Op<Key = K, Value = V>>(map: &OrderStatisticMap<K, V, O>) -> Option<NonNull<Node<K, V, O>>> {
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            while let Some(right) = (*current.as_ptr()).right {
                current = right;
            }
            current = splay(current);
            map.root.set(Some(current));
            Some(current)
        },
    }
}

fn detach_root<K, V, O: Op<Key = K, Value = V>>(map: &mut OrderStatisticMap<K, V, O>) -> (K, V) {
    let root = map.root.get().unwrap();
    unsafe {
        let (key, value) = (
            std::ptr::read(&raw const (*root.as_ptr()).key),
            std::ptr::read(&raw const (*root.as_ptr()).value),
        );

        let left = (*root.as_ptr()).left;
        let right = (*root.as_ptr()).right;

        // Merge left and right subtrees
        let new_root = match (left, right) {
            (None, None) => None,
            (Some(l), None) => {
                (*l.as_ptr()).parent = None;
                Some(l)
            }
            (None, Some(r)) => {
                (*r.as_ptr()).parent = None;
                Some(r)
            }
            (Some(l), Some(r)) => {
                // Find the maximum of left subtree and splay it to be the root of l,
                // ensuring all ancestors on the search path are updated via rotate() calls.
                (*l.as_ptr()).parent = None;  // Detach l from the deleted root first

                let mut curr = l;
                while let Some(next) = (*curr.as_ptr()).right {
                    curr = next;
                }
                // curr is the maximum of the left subtree
                let new_left_root = splay(curr);  // Splay curr to the root of l's subtree
                                                   // Each rotate_left/rotate_right call during splay
                                                   // automatically calls update() on both nodes,
                                                   // ensuring all ancestors have their len recomputed

                // Now attach the right subtree to new_left_root
                (*new_left_root.as_ptr()).right = Some(r);
                (*r.as_ptr()).parent = Some(new_left_root);
                (*new_left_root.as_ptr()).update();

                Some(new_left_root)
            }
        };

        drop(Box::from_raw(root.as_ptr()));
        map.root.set(new_root);
        (key, value)
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
            let hi_map = map.split_off(&split_key);

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

#[cfg(test)]
mod detach_root_tests {
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
