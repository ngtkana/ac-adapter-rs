//! A predecessor data structure based on van Emde Boas trees.
//!
//! This is implemented with hash maps, so `new()` is $O(\log\log n)$.
//!
//! # Example
//!
//! ```
//! # use veb::VebSet;
//! let mut veb = VebSet::new(1_000_000); // capacity
//! veb.insert(42);
//! assert!(veb.contains(42));
//! veb.remove(42);
//! assert!(!veb.contains(42));
//!
//! let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
//! assert_eq!(veb.collect(), vec![12, 34, 56, 78]);
//! assert_eq!(veb.min(), Some(12));
//! assert_eq!(veb.max(), Some(78));
//! assert_eq!(veb.succ(34), Some(56));
//! assert_eq!(veb.pred(34), Some(12));
//! assert_eq!(veb.contains(34), true);
//! assert_eq!(veb.contains(35), false);
//! assert_eq!(veb.len(), 4);
//!
//! assert_eq!(veb.collect(), vec![12, 34, 56, 78]); // Useful for debugging
//! ```
//!
//! # Operations
//!
//! NOTE: `min`, `max`, `succ`, and `pred` return `None` if the set is empty.
//!
//! | Operation    | Time Complexity | Explanation |
//! |--------------|-----------------|-------------|
//! | `insert(x)`  | $O(\log\log n)$ | $S \leftarrow S \cup \{x\}$ |
//! | `remove(x)`  | $O(\log\log n)$ | $S \leftarrow S \setminus \{x\}$ |
//! | `contains(x)`| $O(\log\log n)$ | $x \in S$ |
//! | `min()`      | $O(1)$          | $\min S$ |
//! | `max()`      | $O(1)$          | $\max S$ |
//! | `succ(x)`    | $O(\log\log n)$ | $\min\\{y \in S \mid y > x\\}$ |
//! | `pred(x)`    | $O(\log\log n)$ | $\max\\{y \in S \mid y < x\\}$ |
//! | `len()`      | $O(1)$          | $\|S\|$ |
//! | `is_empty()` | $O(1)$          | $S = \emptyset$ |
//! | `collect()`  | $O(\|S\|\log\log n)$ | Convert to a [`Vec`] |

use std::collections::HashMap;

macro_rules! multi_or_else {
    ($e:expr, $($f:expr),+) => {
        $e.or_else(|| multi_or_else!($($f),+))
    };
    ($e:expr) => {
        $e
    };
}

/// A van Emde Boas tree-based map.
/// The map is implemented as a van Emde Boas tree with a hash map.
///
/// # Example
/// ```
/// use veb::VebMap;
/// let mut veb = VebMap::from_iter(vec![(42, "foo"), (43, "bar")]);
/// assert_eq!(veb.get(42), Some(&"foo"));
/// assert_eq!(veb.get(43), Some(&"bar"));
/// assert_eq!(veb.get(44), None);
///
/// assert_eq!(veb.min(), Some((42, &"foo")));
/// assert_eq!(veb.min_key(), Some(42));
/// assert_eq!(veb.min_value(), Some(&"foo"));
/// ```
pub struct VebMap<V> {
    veb: VebSet,
    map: HashMap<usize, V>,
}
impl<V> VebMap<V> {
    /// Creates a new van Emde Boas tree-based map with the given capacity.
    ///
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::new(1_000_000);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            veb: VebSet::new(n),
            map: HashMap::new(),
        }
    }

    /// Inserts an element into the map.
    /// Returns the previous value if the key was already present.
    ///
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1_000_000);
    /// assert_eq!(veb.insert(42, "foo"), None);
    /// assert_eq!(veb.insert(42, "bar"), Some("foo"));
    /// ```
    pub fn insert(&mut self, i: usize, v: V) -> Option<V> {
        self.veb.insert(i);
        self.map.insert(i, v)
    }

    /// Removes an element from the map.
    /// Returns the value if the key was present.
    ///
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1_000_000);
    /// veb.insert(42, "foo");
    /// assert_eq!(veb.remove(42), Some("foo"));
    /// assert_eq!(veb.remove(42), None);
    /// ```
    pub fn remove(&mut self, i: usize) -> Option<V> {
        self.veb.remove(i);
        self.map.remove(&i)
    }

    /// Returns the value corresponding to the key.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1_000_000);
    /// veb.insert(42, "foo");
    /// assert_eq!(veb.get(42), Some(&"foo"));
    /// assert_eq!(veb.get(43), None);
    /// ```
    pub fn get(&self, i: usize) -> Option<&V> {
        self.map.get(&i)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let mut veb = VebMap::new(1_000_000);
    /// veb.insert(42, "foo");
    /// assert_eq!(veb.get_mut(42), Some(&mut "foo"));
    /// assert_eq!(veb.get_mut(43), None);
    /// ```
    pub fn get_mut(&mut self, i: usize) -> Option<&mut V> {
        self.map.get_mut(&i)
    }

    /// Returns the minimum element in the map.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.min(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.min(), Some((42, &"foo")));
    /// ```
    pub fn min_key(&self) -> Option<usize> {
        self.veb.min()
    }

    /// Returns the minimum value in the map.
    /// Returns `None` if the map is empty.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.min_value(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.min_value(), Some(&"foo"));
    /// ```
    pub fn min_value(&self) -> Option<&V> {
        self.veb.min().and_then(|i| self.map.get(&i))
    }

    /// Returns the minimum element and value in the map.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.min(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.min(), Some((42, &"foo")));
    /// ```
    pub fn min(&self) -> Option<(usize, &V)> {
        self.veb
            .min()
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// Returns the maximum element in the map.
    /// Returns `None` if the map is empty.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.max(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.max(), Some((42, &"foo")));
    /// ```
    pub fn max_key(&self) -> Option<usize> {
        self.veb.max()
    }

    /// Returns the maximum value in the map.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.max_value(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.max_value(), Some(&"foo"));
    /// ```
    pub fn max_value(&self) -> Option<&V> {
        self.veb.max().and_then(|i| self.map.get(&i))
    }

    /// Returns the maximum element and value in the map.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.max(), None);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.max(), Some((42, &"foo")));
    /// ```
    pub fn max(&self) -> Option<(usize, &V)> {
        self.veb
            .max()
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// Returns the strict successor of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_key(34), Some(56));
    /// assert_eq!(veb.succ_value(34), Some(&"baz"));
    /// assert_eq!(veb.succ(34), Some((56, &"baz")));
    /// assert_eq!(veb.succ(78), None);
    /// ```
    pub fn succ_key(&self, i: usize) -> Option<usize> {
        self.veb.succ(i)
    }

    /// Returns the strict successor value of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_value(34), Some(&"baz"));
    /// assert_eq!(veb.succ_value(78), None);
    /// ```
    pub fn succ_value(&self, i: usize) -> Option<&V> {
        self.veb.succ(i).and_then(|i| self.map.get(&i))
    }

    /// Returns the strict successor of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ(34), Some((56, &"baz")));
    /// assert_eq!(veb.succ(78), None);
    /// ```
    pub fn succ(&self, i: usize) -> Option<(usize, &V)> {
        self.veb
            .succ(i)
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// Returns the non-strict successor of the given element.
    ///
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_eq_key(34), Some(34));
    /// assert_eq!(veb.succ_eq_key(35), Some(56));
    /// ```
    pub fn succ_eq_key(&self, i: usize) -> Option<usize> {
        if self.contains_key(i) {
            return Some(i);
        }
        self.succ_key(i)
    }

    /// Returns the non-strict successor value of the given element.
    ///
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_eq_value(34), Some(&"bar"));
    /// assert_eq!(veb.succ_eq_value(35), Some(&"baz"));
    /// ```
    pub fn succ_eq_value(&self, i: usize) -> Option<&V> {
        if let Some(v) = self.get(i) {
            return Some(v);
        }
        self.succ_value(i)
    }

    /// Returns the non-strict successor of the given element.
    ///
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.succ_eq(34), Some((34, &"bar")));
    /// assert_eq!(veb.succ_eq(35), Some((56, &"baz")));
    /// ```
    pub fn succ_eq(&self, i: usize) -> Option<(usize, &V)> {
        if let Some(v) = self.get(i) {
            return Some((i, v));
        }
        self.succ(i)
    }

    /// Returns the strict predecessor of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_key(34), Some(12));
    /// assert_eq!(veb.pred_value(34), Some(&"foo"));
    /// assert_eq!(veb.pred(34), Some((12, &"foo")));
    /// assert_eq!(veb.pred(12), None);
    /// ```
    pub fn pred_key(&self, i: usize) -> Option<usize> {
        self.veb.pred(i)
    }

    /// Returns the strict predecessor value of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_value(34), Some(&"foo"));
    /// assert_eq!(veb.pred_value(12), None);
    /// ```
    pub fn pred_value(&self, i: usize) -> Option<&V> {
        self.veb.pred(i).and_then(|i| self.map.get(&i))
    }

    /// Returns the strict predecessor of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred(34), Some((12, &"foo")));
    /// assert_eq!(veb.pred(12), None);
    /// ```
    pub fn pred(&self, i: usize) -> Option<(usize, &V)> {
        self.veb
            .pred(i)
            .and_then(|i| self.map.get(&i).map(|v| (i, v)))
    }

    /// Returns the non-strict predecessor of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_eq_key(34), Some(34));
    /// assert_eq!(veb.pred_eq_key(35), Some(12));
    /// ```
    pub fn pred_eq_key(&self, i: usize) -> Option<usize> {
        if self.contains_key(i) {
            return Some(i);
        }
        self.pred_key(i)
    }

    /// Returns the non-strict predecessor value of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_eq_value(34), Some(&"bar"));
    /// assert_eq!(veb.pred_eq_value(35), Some(&"foo"));
    /// ```
    pub fn pred_eq_value(&self, i: usize) -> Option<&V> {
        if let Some(v) = self.get(i) {
            return Some(v);
        }
        self.pred_value(i)
    }

    /// Returns the non-strict predecessor of the given element.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.pred_eq(34), Some((34, &"bar")));
    /// assert_eq!(veb.pred_eq(35), Some((12, &"foo")));
    /// ```
    pub fn pred_eq(&self, i: usize) -> Option<(usize, &V)> {
        if let Some(v) = self.get(i) {
            return Some((i, v));
        }
        self.pred(i)
    }

    /// Returns the number of elements in the map.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.len(), 0);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.veb.len()
    }

    /// Returns `true` if the map is empty.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![]);
    /// assert_eq!(veb.is_empty(), true);
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.veb.is_empty()
    }

    /// Returns `true` if the map contains the given key.
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(42, "foo")]);
    /// assert_eq!(veb.contains_key(42), true);
    /// assert_eq!(veb.contains_key(43), false);
    /// ```
    pub fn contains_key(&self, i: usize) -> bool {
        self.veb.contains(i)
    }

    /// Returns the elements in the map in ascending order.
    /// The elements are collected into a [`Vec`].
    /// # Example
    /// ```
    /// # use veb::VebMap;
    /// let veb = VebMap::from_iter(vec![(12, "foo"), (34, "bar"), (56, "baz"), (78, "qux")]);
    /// assert_eq!(veb.collect(), vec![
    ///     (12, &"foo"),
    ///     (34, &"bar"),
    ///     (56, &"baz"),
    ///     (78, &"qux")
    /// ]);
    /// ```
    pub fn collect(&self) -> Vec<(usize, &V)> {
        self.veb
            .collect()
            .into_iter()
            .filter_map(|i| self.map.get(&i).map(|v| (i, v)))
            .collect()
    }
}

impl<V: std::fmt::Debug> std::fmt::Debug for VebMap<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.collect()).finish()
    }
}

impl<V> std::ops::Index<usize> for VebMap<V> {
    type Output = V;

    fn index(&self, i: usize) -> &V {
        self.get(i).unwrap()
    }
}
impl<V> std::ops::IndexMut<usize> for VebMap<V> {
    fn index_mut(&mut self, i: usize) -> &mut V {
        self.get_mut(i).unwrap()
    }
}

/// A van Emde Boas tree.
pub enum VebSet {
    Internal {
        min: usize,
        max: usize,
        len: usize,
        csize: usize,
        summary: Box<VebSet>,
        chunks: HashMap<usize, VebSet>,
    },
    Leaf(u64),
}
impl VebSet {
    /// Creates a new van Emde Boas tree with the given capacity.
    ///
    /// # Example
    /// ```
    /// use veb::VebSet;
    /// let veb = VebSet::new(1_000_000);
    /// ```
    pub fn new(n: usize) -> Self {
        if n <= 64 {
            VebSet::Leaf(0)
        } else {
            let csize = (n as f64).sqrt().ceil() as usize;
            let ccount = (n + csize - 1) / csize;
            Self::Internal {
                min: 0,
                max: 0,
                csize,
                len: 0,
                summary: Box::new(VebSet::new(ccount)),
                chunks: HashMap::new(),
            }
        }
    }

    /// Returns the minimum element in the set.
    /// Returns `None` if the set is empty.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).min(), None);
    /// assert_eq!(VebSet::from_iter(vec![42]).min(), Some(42));
    /// assert_eq!(VebSet::from_iter(vec![42, 43]).min(), Some(42));
    /// ```
    pub fn min(&self) -> Option<usize> {
        match self {
            Self::Internal { min, len, .. } => Some(*min).filter(|_| *len > 0),
            Self::Leaf(bs) => Some(bs.trailing_zeros() as usize).filter(|&i| i < 64),
        }
    }

    /// Returns the maximum element in the set.
    /// Returns `None` if the set is empty.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).max(), None);
    /// assert_eq!(VebSet::from_iter(vec![42]).max(), Some(42));
    /// assert_eq!(VebSet::from_iter(vec![42, 43]).max(), Some(43));
    /// ```
    pub fn max(&self) -> Option<usize> {
        match self {
            Self::Internal { max, len, .. } => Some(*max).filter(|_| *len > 0),
            Self::Leaf(bs) => bs.checked_ilog2().map(|i| i as usize),
        }
    }

    /// Returns the number of elements in the set.
    ///
    /// # Example
    /// ```
    /// use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).len(), 0);
    /// assert_eq!(VebSet::from_iter(vec![42]).len(), 1);
    /// assert_eq!(VebSet::from_iter(vec![42, 43]).len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        match self {
            Self::Internal { len, .. } => *len,
            Self::Leaf(bs) => bs.count_ones() as usize,
        }
    }

    /// Returns `true` if the set is empty.
    /// Returns `false` if the set is not empty.
    /// Equivalent to `self.len() == 0`.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// assert_eq!(VebSet::from_iter(vec![]).is_empty(), true);
    /// assert_eq!(VebSet::from_iter(vec![42]).is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Inserts an element into the set.
    /// Returns `true` if the element was not already present.
    /// Returns `false` if the element was already present.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// let mut veb = VebSet::new(1_000_000);
    /// assert_eq!(veb.insert(42), true);
    /// assert_eq!(veb.insert(42), false);
    /// ```
    pub fn insert(&mut self, mut i: usize) -> bool {
        match self {
            Self::Internal {
                min,
                max,
                csize,
                len,
                summary,
                chunks,
            } => {
                if *len == 0 {
                    *min = i;
                    *max = i;
                    *len = 1;
                    true
                } else {
                    if i < *min {
                        std::mem::swap(&mut i, min);
                    }
                    *max = (*max).max(i);
                    if i == *min {
                        return false;
                    }
                    let j = i / *csize;
                    let k = i % *csize;
                    let result = if let Some(chunk) = chunks.get_mut(&j) {
                        chunk.insert(k)
                    } else {
                        let mut chunk = VebSet::new(*csize);
                        assert!(chunk.insert(k));
                        chunks.insert(j, chunk);
                        summary.insert(j);
                        true
                    };
                    if result {
                        *len += 1;
                    }
                    result
                }
            }
            Self::Leaf(bs) => {
                let result = *bs >> i & 1;
                *bs |= 1 << i;
                result == 0
            }
        }
    }

    /// Removes an element from the set.
    /// Returns `true` if the element was present.
    /// Returns `false` if the element was not present.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// let mut veb = VebSet::new(1_000_000);
    /// veb.insert(42);
    /// assert_eq!(veb.remove(42), true);
    /// assert_eq!(veb.remove(42), false);
    /// ```
    pub fn remove(&mut self, mut i: usize) -> bool {
        match self {
            Self::Internal {
                min,
                max,
                csize,
                len,
                summary,
                chunks,
            } => match len {
                0 => false,
                1 => {
                    let result = i == *min;
                    if result {
                        *min = 0;
                        *max = 0;
                        *len = 0;
                    }
                    result
                }
                _ => {
                    if i == *min {
                        let j = summary.min().unwrap();
                        i = j * *csize + chunks[&j].min().unwrap();
                        *min = i;
                    }
                    let j = i / *csize;
                    let k = i % *csize;
                    let result = chunks.get_mut(&j).map_or(false, |chunk| chunk.remove(k));
                    if result {
                        *len -= 1;
                        if chunks[&j].is_empty() {
                            chunks.remove(&j);
                            summary.remove(j);
                        }
                        if i == *max {
                            *max = if let Some(j) = summary.max() {
                                j * *csize + chunks[&j].max().unwrap()
                            } else {
                                *min
                            };
                        }
                    }
                    result
                }
            },
            Self::Leaf(bs) => {
                let result = *bs >> i & 1;
                *bs &= !(1 << i);
                result == 1
            }
        }
    }

    /// Returns the successor of the given element.
    /// Returns `None` if the given element is the maximum element.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
    /// assert_eq!(veb.succ(34), Some(56));
    /// assert_eq!(veb.succ(78), None);
    /// ```
    pub fn succ(&self, i: usize) -> Option<usize> {
        match self {
            Self::Internal {
                min,
                max,
                len,
                csize,
                summary,
                chunks,
                ..
            } => {
                let j = i / csize;
                let k = i % csize;
                match () {
                    () if *len == 0 || *max <= i => None,
                    () if i < *min => Some(*min),
                    () => multi_or_else!(
                        chunks
                            .get(&j)
                            .and_then(|chunk| chunk.succ(k))
                            .map(|k1| j * csize + k1),
                        summary
                            .succ(j)
                            .map(|j1| j1 * csize + chunks[&j1].min().unwrap())
                    ),
                }
            }
            &Self::Leaf(bs) => match i {
                63 => None,
                _ => Some(i + 1 + (bs >> (i + 1)).trailing_zeros() as usize).filter(|&i1| i1 < 64),
            },
        }
    }

    /// Returns the predecessor of the given element.
    /// Returns `None` if the given element is the minimum element.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
    /// assert_eq!(veb.pred(34), Some(12));
    /// assert_eq!(veb.pred(12), None);
    /// ```
    pub fn pred(&self, i: usize) -> Option<usize> {
        match self {
            Self::Internal {
                min,
                max,
                csize,
                len,
                summary,
                chunks,
            } => {
                let j = i / csize;
                let k = i % csize;
                match () {
                    () if *len == 0 || i <= *min => None,
                    () if *max < i => Some(*max),
                    () => multi_or_else!(
                        chunks
                            .get(&j)
                            .and_then(|chunk| chunk.pred(k))
                            .map(|k1| { j * csize + k1 }),
                        summary
                            .pred(j)
                            .map(|j1| { j1 * csize + chunks[&j1].max().unwrap() }),
                        Some(*min)
                    ),
                }
            }
            &Self::Leaf(bs) => (bs & ((1 << i) - 1)).checked_ilog2().map(|j| j as usize),
        }
    }

    /// Returns `true` if the set contains the given element.
    /// Returns `false` if the set does not contain the given element.
    ///
    /// # Example
    /// ```
    /// # use veb::VebSet;
    /// let veb: VebSet = vec![12, 34, 56, 78].into_iter().collect();
    /// assert_eq!(veb.contains(34), true);
    /// assert_eq!(veb.contains(35), false);
    /// ```
    pub fn contains(&self, i: usize) -> bool {
        match self {
            Self::Internal {
                min,
                csize,
                len,
                chunks,
                ..
            } => {
                let j = i / csize;
                let k = i % csize;
                *len != 0 && (i == *min || chunks.get(&j).map_or(false, |chunk| chunk.contains(k)))
            }
            Self::Leaf(bs) => bs >> i & 1 == 1,
        }
    }

    /// Returns the elements in the set in ascending order.
    /// The elements are collected into a [`Vec`].
    pub fn collect(&self) -> Vec<usize> {
        let mut result = Vec::with_capacity(self.len());
        let mut i = self.min();
        for _ in 0..self.len() {
            result.push(i.unwrap());
            i = self.succ(i.unwrap());
        }
        result
    }
}

impl std::fmt::Debug for VebSet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_set().entries(self.collect()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;
    use std::collections::BTreeMap;
    use std::collections::BTreeSet;
    use std::ops::RangeInclusive;

    #[rstest]
    #[case(0..=64)]
    #[case(62..=66)]
    #[case(65..=4096)]
    #[case(4094..=4098)]
    #[case(1_000_000_000..=2_000_000_000)]
    fn test_veb_set(#[case] nrange: RangeInclusive<usize>) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(nrange.clone());
            let mut veb = VebSet::new(n);
            let mut set = BTreeSet::new();
            for _ in 0..200 {
                let i = rng.gen_range(0..n);
                match rng.gen_range(0..5) {
                    0 => assert_eq!(veb.insert(i), set.insert(i), "insert({i})"),
                    1 => assert_eq!(veb.remove(i), set.remove(&i), "remove({i})"),
                    2 => assert_eq!(veb.succ(i), set.range(i + 1..).next().copied(), "succ({i})"),
                    3 => assert_eq!(
                        veb.pred(i),
                        set.range(..i).next_back().copied(),
                        "pred({i})"
                    ),
                    4 => assert_eq!(veb.contains(i), set.contains(&i), "contains({i})"),
                    _ => unreachable!(),
                }
                assert_eq!(veb.min(), set.iter().next().copied(), "min");
                assert_eq!(veb.max(), set.iter().next_back().copied(), "max");
            }
        }
    }

    #[rstest]
    fn test_veb_map() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..1_000);
            let mut veb = VebMap::new(n);
            let mut map = BTreeMap::new();
            for _ in 0..200 {
                let i = rng.gen_range(0..n);
                match rng.gen_range(0..5) {
                    0 => {
                        let v = rng.gen_range(0..1_000);
                        assert_eq!(veb.insert(i, v), map.insert(i, v), "insert({i})");
                    }
                    1 => assert_eq!(veb.remove(i), map.remove(&i), "remove({i})"),
                    2 => assert_eq!(
                        veb.succ(i),
                        map.range(i + 1..).next().map(|(&i, v)| (i, v)),
                        "succ({i})"
                    ),
                    3 => assert_eq!(
                        veb.pred(i),
                        map.range(..i).next_back().map(|(&i, v)| (i, v)),
                        "pred({i})"
                    ),
                    4 => assert_eq!(veb.get(i), map.get(&i), "get({i})"),
                    _ => unreachable!(),
                }
                assert_eq!(veb.min(), map.iter().next().map(|(&i, v)| (i, v)), "min");
                assert_eq!(
                    veb.max(),
                    map.iter().next_back().map(|(&i, v)| (i, v)),
                    "max"
                );
            }
        }
    }
}
