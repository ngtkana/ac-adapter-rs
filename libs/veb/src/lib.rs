//! A predecessor data structure based on van Emde Boas trees.
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
            #[allow(unused_variables)]
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

impl Default for VebSet {
    fn default() -> Self {
        Self::new(0)
    }
}

impl std::iter::FromIterator<usize> for VebSet {
    fn from_iter<T: IntoIterator<Item = usize>>(iter: T) -> Self {
        let mut veb = VebSet::default();
        for i in iter {
            veb.insert(i);
        }
        veb
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
    use std::collections::BTreeSet;
    use std::ops::RangeInclusive;

    #[rstest]
    #[case(0..=64)]
    #[case(62..=66)]
    #[case(65..=4096)]
    #[case(4094..=4098)]
    #[case(1_000_000_000..=2_000_000_000)]
    fn test(#[case] nrange: RangeInclusive<usize>) {
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
}
