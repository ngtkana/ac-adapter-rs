//! v1では未対応: range/range_mut, retain, values_mut, into_iter

use std::borrow::Borrow;
use std::cell::Cell;
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Bound, RangeBounds};
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

mod node;
mod entry;

use node::{Node, detach_root, find_and_splay, free_subtree, leftmost_and_splay, locate_and_splay, nth_and_splay, rightmost_and_splay, splay};
pub use entry::{Entry, OccupiedEntry, VacantEntry, ValueMut};

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
    /// if let Some(mut value) = map.get_mut(&1) {
    ///     *value = 20;
    /// }
    /// assert_eq!(map.get(&1), Some(&20));
    /// ```
    pub fn get_mut<Q: Ord + ?Sized>(&mut self, key: &Q) -> Option<ValueMut<'_, K, V, O>>
    where
        K: Borrow<Q>,
    {
        find_and_splay(self, key).map(|node| ValueMut::new(node))
    }

    /// Gets the entry in the map for inserting or retrieving the value associated with a key.
    ///
    /// # Examples
    ///
    /// ```
    /// use order_statistic_tree::OrderStatisticMap;
    /// use order_statistic_tree::map::Entry;
    ///
    /// let mut map: OrderStatisticMap<i32, i32> = OrderStatisticMap::new();
    /// match map.entry(1) {
    ///     Entry::Vacant(ve) => {
    ///         ve.insert(10);
    ///     }
    ///     Entry::Occupied(mut oe) => {
    ///         *oe.get_mut() += 1;
    ///     }
    /// }
    /// assert_eq!(map.get(&1), Some(&10));
    /// ```
    pub fn entry(&mut self, key: K) -> Entry<'_, K, V, O> {
        match find_and_splay(self, &key) {
            Some(node) => Entry::Occupied(OccupiedEntry::new(node)),
            None => Entry::Vacant(VacantEntry {
                map: self,
                key,
            }),
        }
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
        let self_root = self.root.get();
        let other_root = other.root.get();
        match (self_root, other_root) {
            (_, None) => {}
            (None, Some(_)) => {
                self.root.set(other_root);
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
                }
                let merged = node::merge_trees(Some(self_max), Some(other_min));
                self.root.set(merged);
                other.root.set(None);
            }
        }
    }

    /// Internal helper for splitting at a given index.
    fn split_off_at(&mut self, idx: usize) -> Self {
        let len = self.len();
        assert!(idx <= len, "index out of bounds: idx={idx} len={len}");
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
    /// let high = map.split_off_by_key(&3);
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(high.len(), 2);
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(high.get(&3), Some(&"c"));
    /// ```
    pub fn split_off_by_key<Q: Ord + ?Sized>(&mut self, key: &Q) -> Self
    where
        K: Borrow<Q>,
    {
        let idx = self.lower_bound(key);
        self.split_off_at(idx)
    }

    /// Splits the map into two at the given index, returning a new map containing all
    /// key-value pairs at indices >= the given index.
    ///
    /// This operation takes O(log n) amortized time. The original map retains all key-value
    /// pairs at indices < the given index.
    ///
    /// # Panics
    ///
    /// Panics if `index > len()`.
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
    /// let high = map.split_off_by_index(2);
    /// assert_eq!(map.len(), 2);
    /// assert_eq!(high.len(), 2);
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(high.get(&3), Some(&"c"));
    /// ```
    pub fn split_off_by_index(&mut self, index: usize) -> Self {
        self.split_off_at(index)
    }

    /// Deprecated: use `split_off_by_key` instead.
    #[deprecated(since = "0.1.0", note = "use `split_off_by_key` instead")]
    pub fn split_off<Q: Ord + ?Sized>(&mut self, key: &Q) -> Self
    where
        K: Borrow<Q>,
    {
        self.split_off_by_key(key)
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
    /// assert_eq!(map.fold_all(), (1 + 10) + (2 + 20)); // 33
    /// ```
    pub fn fold_all(&self) -> O::SegValue {
        self.root.get().map_or_else(O::identity, |r| unsafe { (*r.as_ptr()).prod.clone() })
    }

    /// Computes the aggregate value over a key range.
    ///
    /// Returns the monoid product of all (key, value) pairs within the specified key range.
    /// The range can be specified using any `RangeBounds<K>` (e.g., `1..3`, `1..=3`, `..5`).
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
    /// assert_eq!(map.fold_by_key(1..3), (1 + 10) + (2 + 20)); // 33
    /// ```
    pub fn fold_by_key<Q: Ord + ?Sized>(&self, range: impl RangeBounds<Q>) -> O::SegValue
    where
        K: Borrow<Q>,
    {
        let start = match range.start_bound() {
            Bound::Included(k) => self.lower_bound(k),
            Bound::Excluded(k) => self.upper_bound(k),
            Bound::Unbounded => 0,
        };
        let end = match range.end_bound() {
            Bound::Included(k) => self.upper_bound(k),
            Bound::Excluded(k) => self.lower_bound(k),
            Bound::Unbounded => self.len(),
        };
        if end <= start {
            return O::identity();
        }
        self.fold_by_index(start..end)
    }

    /// Computes the aggregate value over an index range.
    ///
    /// Returns the monoid product of all (key, value) pairs at indices within the specified range.
    /// Indices are in sorted order, starting from 0.
    /// The range can be specified using any `RangeBounds<usize>` (e.g., `0..3`, `0..=2`, `..5`).
    /// For an empty range, returns `O::identity()`.
    ///
    /// # Panics
    ///
    /// Panics if the range exceeds the bounds of the map.
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
    /// assert_eq!(map.fold_by_index(0..2), (1 + 10) + (2 + 20)); // 33
    /// ```
    pub fn fold_by_index(&self, range: impl RangeBounds<usize>) -> O::SegValue {
        let len = self.len();
        let (start, end) = to_half_open_range(range, len);
        assert!(start <= end && end <= len, "range out of bounds: {start}..{end}, len={len}");

        if start == end {
            return O::identity();
        }
        if start == 0 && end == len {
            return self.fold_all();
        }

        let (left, rest) = node::split_at_index(self.root.get(), start);
        let (mid, right) = node::split_at_index(rest, end - start);
        let result = mid.map_or_else(O::identity, |m| unsafe { (*m.as_ptr()).prod.clone() });
        self.root.set(node::merge_trees(node::merge_trees(left, mid), right));
        result
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

fn to_half_open_range<R: RangeBounds<usize>>(range: R, len: usize) -> (usize, usize) {
    let start = match range.start_bound() {
        Bound::Included(&s) => s,
        Bound::Excluded(&s) => s + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&e) => e + 1,
        Bound::Excluded(&e) => e,
        Bound::Unbounded => len,
    };
    (start, end)
}
