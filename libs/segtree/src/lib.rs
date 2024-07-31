//! Segment tree and its variants.
//!
//! # [`Op`] trait
//!
//! * [`Op::identity`] returns the identity value $e$.
//! * [`Op::mul`] multiplies two values: $x \cdot y$.
//!
//! The multiplication must be associative.
//!
//! Furthermore, when this is used for [`Sparse2dSegtree`] or [`Dense2dSegtree`], the multiplication must be commutative.
//!
//! # Modifier APIs
//!
//! While [`Segtree`], [`SegtreeWithCompression`], and [`Dense2dSegtree`] have `entry` API, [`Sparse2dSegtree`] does not have it.
//! Instead, it has `apply` API. You can apply a function $f$ that satisfies $f(x \cdot y) = x \cdot f(y)$ to a single element..

use core::fmt;
use std::collections::BTreeMap;
use std::iter::FromIterator;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Index;
use std::ops::RangeBounds;

/// A trait for segment tree operations.
pub trait Op {
    /// The value type.
    type Value;

    /// Returns the identity value $e$.
    fn identity() -> Self::Value;
    /// Multiplies two values: $x \cdot y$.
    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

/// A segment tree.
/// Use [`as_slice()`](Self::as_slice()) to debug.
pub struct Segtree<O: Op> {
    len: usize,
    offset: usize,
    values: Vec<O::Value>,
}
impl<O: Op> Segtree<O> {
    /// Constructs a new segment tree with the specified length.
    pub fn from_len(len: usize) -> Self
    where
        O::Value: Clone,
    {
        let offset = len.next_power_of_two();
        Self {
            len,
            offset,
            values: vec![O::identity(); 2 * offset],
        }
    }

    /// Constructs with the specified values.
    pub fn new(elms: &[O::Value]) -> Self
    where
        O::Value: Clone,
    {
        let len = elms.len();
        let offset = len.next_power_of_two();
        let mut values = vec![O::identity(); 2 * offset];
        values[offset..offset + len].clone_from_slice(elms);
        for i in (1..offset).rev() {
            values[i] = O::mul(&values[i * 2], &values[i * 2 + 1]);
        }
        Self {
            len,
            offset,
            values,
        }
    }

    /// Returns $x_l \cdot x_{l+1} \cdot \ldots \cdot x_{r-1}$.
    pub fn fold<R: RangeBounds<usize>>(&self, range: R) -> O::Value {
        let Self {
            len,
            offset,
            ref values,
        } = *self;
        let (mut start, mut end) = open(range, len);
        assert!((start..=len).contains(&len));
        start += offset;
        end += offset;
        let mut left = O::identity();
        let mut right = O::identity();
        while start < end {
            if start % 2 == 1 {
                left = O::mul(&left, &values[start]);
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                right = O::mul(&values[end], &right);
            }
            start /= 2;
            end /= 2;
        }
        O::mul(&left, &right)
    }

    /// Returns the maximum $r$ s.t. $f(x _ l \cdot \dots \cdot x _ { r - 1 })$ is `true`, if $f$ is monotone.
    ///
    /// More precisely, $r$ satisfies:
    ///
    /// 1. $f(x _ l \cdot \dots \cdot x _ { r - 1 })$ is `true`, or $l = r$
    /// 2. $f(x _ l \cdot \dots \cdot x _ { r } )$ is `false`, or $r = n$
    pub fn max_right(&self, start: usize, mut f: impl FnMut(&O::Value) -> bool) -> usize {
        debug_assert!(f(&O::identity()));
        let Self {
            len,
            offset,
            ref values,
        } = *self;
        let mut end = start + offset;
        let mut value = O::identity();
        loop {
            let p = end.trailing_zeros();
            let end1 = end + (1 << p);
            if offset + len < end1 {
                break;
            }
            let value1 = O::mul(&value, &values[end >> p]);
            if !f(&value1) {
                break;
            }
            end = end1;
            value = value1;
        }
        for p in (0..end.trailing_zeros()).rev() {
            let end1 = end + (1 << p);
            if offset + len < end1 {
                continue;
            }
            let value1 = O::mul(&value, &values[end >> p]);
            if !f(&value1) {
                continue;
            }
            end = end1;
            value = value1;
        }
        end - offset
    }

    /// Returns the minimum $l$ s.t. $f(x _ l \cdot \dots \cdot x _ { r - 1 })$ is `true`, if $f$ is monotone.
    ///
    /// More precisely, $r$ satisfies:
    ///
    /// 1. $f(x _ l \cdot \dots \cdot x _ { r - 1 })$ is `true`, or $l = r$
    /// 2. $f(x _ { l - 1 } \cdot \dots \cdot x _ { r - 1 } )$ is `false`, or $l = 0$
    pub fn min_left(&self, end: usize, mut f: impl FnMut(&O::Value) -> bool) -> usize {
        debug_assert!(f(&O::identity()));
        if end == 0 {
            return 0;
        }
        let Self {
            offset, ref values, ..
        } = *self;
        let mut start = end + offset;
        let mut value = O::identity();
        loop {
            let p = (start | offset).trailing_zeros();
            let start1 = start - (1 << p);
            let value1 = O::mul(&value, &values[start1 >> p]);
            if !f(&value1) {
                break;
            }
            start = start1;
            value = value1;
            if start == offset {
                return 0;
            }
        }
        for p in (0..(start | offset).trailing_zeros()).rev() {
            let start1 = start - (1 << p);
            let value1 = O::mul(&value, &values[start1 >> p]);
            if !f(&value1) {
                continue;
            }
            start = start1;
            value = value1;
        }
        start - offset
    }

    /// Returns the entry of $x_i$.
    pub fn entry(&mut self, index: usize) -> Entry<O> {
        let offset = self.offset;
        Entry {
            segtree: self,
            index: offset + index,
        }
    }

    /// Returns an iterator of $x_0, x_1, \ldots, x_{n-1}$.
    pub fn iter(&self) -> std::slice::Iter<O::Value> {
        self.values[self.offset..self.offset + self.len].iter()
    }

    /// Returns a slice of $x_0, x_1, \ldots, x_{n-1}$.
    pub fn as_slice(&self) -> &[O::Value] {
        &self.values[self.offset..self.offset + self.len]
    }
}

impl<O: Op> fmt::Debug for Segtree<O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Segtree")
            .field("values", &self.values)
            .finish()
    }
}

impl<O: Op> FromIterator<O::Value> for Segtree<O>
where
    O::Value: Clone,
{
    fn from_iter<I: IntoIterator<Item = O::Value>>(iter: I) -> Self {
        Self::new(&iter.into_iter().collect::<Vec<_>>())
    }
}

impl<O: Op> Index<usize> for Segtree<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        &self.values[self.values.len() / 2 + index]
    }
}

/// The result of [`Segtree::entry`].
pub struct Entry<'a, O: Op> {
    segtree: &'a mut Segtree<O>,
    index: usize,
}
impl<'a, O: Op> Drop for Entry<'a, O> {
    fn drop(&mut self) {
        let mut index = self.index;
        while index != 0 {
            index /= 2;
            self.segtree.values[index] = O::mul(
                &self.segtree.values[index * 2],
                &self.segtree.values[index * 2 + 1],
            );
        }
    }
}
impl<'a, O: Op> Deref for Entry<'a, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target {
        &self.segtree.values[self.index]
    }
}
impl<'a, O: Op> DerefMut for Entry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.segtree.values[self.index]
    }
}
impl<'a, O: Op> fmt::Debug for Entry<'a, O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Entry").field("index", &self.index).finish()
    }
}

/// A sparse (compressed) segment tree.
/// Use [`collect_map()`](Self::collect_map()) to debug.
pub struct SegtreeWithCompression<K, O: Op> {
    inner: Segtree<O>,
    keys: Vec<K>,
}
impl<K: Ord, O: Op> SegtreeWithCompression<K, O> {
    /// Constructs with the specified key-value pairs.
    pub fn new(kv: &[(K, O::Value)]) -> Self
    where
        K: Clone,
        O::Value: Clone,
    {
        let mut keys = kv.iter().map(|(k, _)| k.clone()).collect::<Vec<_>>();
        keys.sort();
        let values = kv.iter().map(|(_, v)| v.clone()).collect::<Vec<_>>();
        Self {
            inner: Segtree::new(&values),
            keys,
        }
    }

    /// Folds $\left \lbrace x_k \mid k \in \text{{range}} \right \rbrace$.
    pub fn fold<R: RangeBounds<K>>(&self, range: R) -> O::Value {
        let (start, end) = to_range(range, &self.keys);
        self.inner.fold(start..end)
    }

    /// Returns the entry of $x_k$.
    /// If $k$ is not found, it panics.
    pub fn entry(&mut self, key: &K) -> Entry<'_, O> {
        let index = self.keys.binary_search(key).unwrap();
        self.inner.entry(index)
    }

    /// Returns the keys.
    pub fn keys(&self) -> &[K] {
        &self.keys
    }

    /// Returns an iterator of $(k, x_k)$.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &O::Value)> {
        self.keys.iter().zip(self.inner.as_slice())
    }

    /// Collects the key-value pairs into a `BTreeMap`.
    pub fn collect_map(&self) -> BTreeMap<K, O::Value>
    where
        K: Clone,
        O::Value: Clone,
    {
        self.keys
            .iter()
            .cloned()
            .zip(self.inner.iter().cloned())
            .collect()
    }
}

impl<K, O: Op> fmt::Debug for SegtreeWithCompression<K, O>
where
    K: fmt::Debug,
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SparseSegtree")
            .field("inner", &self.inner)
            .field("keys", &self.keys)
            .finish()
    }
}

impl<K: Ord, O: Op> FromIterator<(K, O::Value)> for SegtreeWithCompression<K, O>
where
    K: Clone,
    O::Value: Clone,
{
    fn from_iter<I: IntoIterator<Item = (K, O::Value)>>(iter: I) -> Self {
        Self::new(&iter.into_iter().collect::<Vec<_>>())
    }
}

impl<K: Ord, O: Op> Index<K> for SegtreeWithCompression<K, O> {
    type Output = O::Value;

    fn index(&self, key: K) -> &Self::Output {
        &self.inner[self.keys.binary_search(&key).unwrap()]
    }
}

/// A segment tree of segment trees (2D segment tree).
/// The multiplication must be commutative.
pub struct Sparse2dSegtree<K, L, O: Op> {
    segtrees: Vec<SegtreeWithCompression<L, O>>,
    keys: Vec<K>,
}
impl<K, L, O: Op> Sparse2dSegtree<K, L, O>
where
    K: Ord + Clone,
    L: Ord + Clone,
    O::Value: Clone,
{
    /// Constructs with the specified key-value pairs.
    pub fn new(points: &[(K, L, O::Value)]) -> Self {
        let mut keys = points.iter().map(|(k, _, _)| k.clone()).collect::<Vec<_>>();
        keys.sort();
        keys.dedup();
        let mut lvs = vec![vec![]; keys.len() * 2];
        for (k, l, v) in points {
            let mut i = keys.binary_search(k).unwrap();
            i += keys.len();
            while i != 0 {
                lvs[i].push((l.clone(), v.clone()));
                i /= 2;
            }
        }
        let segtrees = lvs
            .into_iter()
            .map(|lvs_| {
                let mut ls = lvs_.iter().map(|(l, _)| l).collect::<Vec<_>>();
                ls.sort();
                ls.dedup();
                let mut lvs = ls
                    .iter()
                    .map(|&l| (l.clone(), O::identity()))
                    .collect::<Vec<_>>();
                for (l, v) in &lvs_ {
                    let i = ls.binary_search(&l).unwrap();
                    lvs[i].1 = O::mul(&lvs[i].1, v);
                }
                SegtreeWithCompression::new(&lvs)
            })
            .collect::<Vec<_>>();
        Self { segtrees, keys }
    }

    /// Folds $\left \lbrace x_{k, l} \mid (k, l) \in \text{{range}} \right \rbrace$.
    pub fn fold(&self, i: impl RangeBounds<K>, j: impl RangeBounds<L> + Clone) -> O::Value {
        let (mut i0, mut i1) = to_range(i, &self.keys);
        i0 += self.keys.len();
        i1 += self.keys.len();
        let mut left = O::identity();
        let mut right = O::identity();
        while i0 < i1 {
            if i0 % 2 == 1 {
                left = O::mul(&left, &self.segtrees[i0].fold(j.clone()));
                i0 += 1;
            }
            if i1 % 2 == 1 {
                i1 -= 1;
                right = O::mul(&self.segtrees[i1].fold(j.clone()), &right);
            }
            i0 /= 2;
            i1 /= 2;
        }
        O::mul(&left, &right)
    }

    /// Apply a function to $x_{k, l}$.
    ///
    /// The function $f$ must satisfy $f(x \cdot y) = x \cdot f(y)$.
    pub fn apply(&mut self, k: &K, l: &L, mut f: impl FnMut(&mut O::Value)) {
        let mut i = self.keys.binary_search(k).unwrap();
        i += self.keys.len();
        while i != 0 {
            f(&mut self.segtrees[i].entry(l));
            i /= 2;
        }
    }

    /// Returns the iterator of $(k, l, x_{k, l})$.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &L, &O::Value)> {
        self.keys
            .iter()
            .zip(self.segtrees[self.keys.len()..].iter())
            .flat_map(|(k, segtree)| segtree.iter().map(move |(l, v)| (k, l, v)))
    }

    /// Collects the key-value pairs into a `BTreeMap`.
    pub fn collect_map(&self) -> BTreeMap<(K, L), O::Value>
    where
        K: Clone,
        L: Clone,
        O::Value: Clone,
    {
        self.keys
            .iter()
            .flat_map(|k| {
                self.segtrees[self.keys.len() + self.keys.binary_search(k).unwrap()]
                    .iter()
                    .map(move |(l, v)| ((k.clone(), l.clone()), v.clone()))
            })
            .collect()
    }
}

impl<K, L, O: Op> fmt::Debug for Sparse2dSegtree<K, L, O>
where
    K: fmt::Debug,
    L: fmt::Debug,
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sparse2dSegtree")
            .field("segtrees", &self.segtrees)
            .field("keys", &self.keys)
            .finish()
    }
}

impl<K, L, O: Op> FromIterator<(K, L, O::Value)> for Sparse2dSegtree<K, L, O>
where
    K: Ord + Clone,
    L: Ord + Clone,
    O::Value: Clone,
{
    fn from_iter<I: IntoIterator<Item = (K, L, O::Value)>>(iter: I) -> Self {
        Self::new(&iter.into_iter().collect::<Vec<_>>())
    }
}

impl<K: Ord, L: Ord, O: Op> Index<K> for Sparse2dSegtree<K, L, O> {
    type Output = SegtreeWithCompression<L, O>;

    fn index(&self, i: K) -> &Self::Output {
        &self.segtrees[self.keys.binary_search(&i).unwrap() + self.keys.len()]
    }
}

impl<K: Ord, L: Ord, O: Op> Index<(K, L)> for Sparse2dSegtree<K, L, O> {
    type Output = O::Value;

    fn index(&self, (i, j): (K, L)) -> &Self::Output {
        &self.segtrees[self.keys.binary_search(&i).unwrap() + self.keys.len()][j]
    }
}

/// A dense 2D segment tree.
pub struct Dense2dSegtree<O: Op> {
    values: Vec<Vec<O::Value>>,
}
impl<O: Op> Dense2dSegtree<O> {
    /// Constructs with the specified values.
    pub fn new(values: &[Vec<O::Value>]) -> Self
    where
        O::Value: Clone,
    {
        let values_ = values;
        let h = values.len();
        let w = values.get(0).map_or(0, Vec::len);
        let mut values = vec![vec![O::identity(); 2 * w]; 2 * h];
        for (values, values_) in values[h..].iter_mut().zip(values_) {
            values[w..].clone_from_slice(values_);
            for j in (1..w).rev() {
                values[j] = O::mul(&values[j * 2], &values[j * 2 + 1]);
            }
        }
        for i in (1..h).rev() {
            for j in 0..2 * w {
                values[i][j] = O::mul(&values[i * 2][j], &values[i * 2 + 1][j]);
            }
        }
        Self { values }
    }

    /// Fold $\left \lbrace x_{i, j} \mid i \in \text{{range}}_i, j \in \text{{range}}_j \right \rbrace$.
    pub fn fold(&self, i: impl RangeBounds<usize>, j: impl RangeBounds<usize>) -> O::Value {
        let h = self.values.len() / 2;
        let w = self.values.get(0).map_or(0, |v| v.len() / 2);
        let (mut i0, mut i1) = open(i, h);
        assert!(i0 <= i1 && i1 <= h);
        let (mut j0, mut j1) = open(j, w);
        assert!(j0 <= j1 && j1 <= w);
        i0 += h;
        i1 += h;
        j0 += w;
        j1 += w;
        let mut left = O::identity();
        let mut right = O::identity();
        while i0 < i1 {
            if i0 % 2 == 1 {
                let mut j0 = j0;
                let mut j1 = j1;
                while j0 < j1 {
                    if j0 % 2 == 1 {
                        left = O::mul(&left, &self.values[i0][j0]);
                        j0 += 1;
                    }
                    if j1 % 2 == 1 {
                        j1 -= 1;
                        right = O::mul(&self.values[i0][j1], &right);
                    }
                    j0 /= 2;
                    j1 /= 2;
                }
                i0 += 1;
            }
            if i1 % 2 == 1 {
                i1 -= 1;
                let mut j0 = j0;
                let mut j1 = j1;
                while j0 < j1 {
                    if j0 % 2 == 1 {
                        left = O::mul(&left, &self.values[i1][j0]);
                        j0 += 1;
                    }
                    if j1 % 2 == 1 {
                        j1 -= 1;
                        right = O::mul(&self.values[i1][j1], &right);
                    }
                    j0 /= 2;
                    j1 /= 2;
                }
            }
            i0 /= 2;
            i1 /= 2;
        }
        O::mul(&left, &right)
    }

    /// Returns the entry of $x_{i, j}$.
    pub fn entry(&mut self, i: usize, j: usize) -> Dense2dEntry<O> {
        let h = self.values.len() / 2;
        let w = self.values.get(0).map_or(0, |v| v.len() / 2);
        Dense2dEntry {
            segtree: self,
            i: h + i,
            j: w + j,
        }
    }

    /// Returns an iterator that returns the rows $(x_{i, 0}, x_{i, 1}, \ldots, x_{i, w-1})$.
    pub fn iter(&self) -> impl Iterator<Item = &[O::Value]> {
        self.values[self.values.len() / 2..]
            .iter()
            .map(|v| &v[v.len() / 2..])
    }

    /// Collect to a $2$-dimensional vector.
    pub fn collect_vec(&self) -> Vec<Vec<O::Value>>
    where
        O::Value: Clone,
    {
        self.iter().map(<[_]>::to_vec).collect()
    }
}

impl<O: Op> fmt::Debug for Dense2dSegtree<O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Dense2dSegtree")
            .field("values", &self.values)
            .finish()
    }
}

impl<O: Op> Index<usize> for Dense2dSegtree<O> {
    type Output = [O::Value];

    fn index(&self, index: usize) -> &Self::Output {
        &self.values[self.values.len() / 2 + index]
    }
}

/// The result of [`Dense2dSegtree::entry`].
pub struct Dense2dEntry<'a, O: Op> {
    segtree: &'a mut Dense2dSegtree<O>,
    i: usize,
    j: usize,
}
impl<'a, O: Op> Drop for Dense2dEntry<'a, O> {
    fn drop(&mut self) {
        let mut i = self.i;
        let mut j = self.j / 2;
        while j != 0 {
            self.segtree.values[i][j] = O::mul(
                &self.segtree.values[i][2 * j],
                &self.segtree.values[i][2 * j + 1],
            );
            j /= 2;
        }
        i /= 2;
        while i != 0 {
            let mut j = self.j;
            while j != 0 {
                self.segtree.values[i][j] = O::mul(
                    &self.segtree.values[i * 2][j],
                    &self.segtree.values[i * 2 + 1][j],
                );
                j /= 2;
            }
            i /= 2;
        }
    }
}
impl<'a, O: Op> Deref for Dense2dEntry<'a, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target {
        &self.segtree.values[self.i][self.j]
    }
}
impl<'a, O: Op> DerefMut for Dense2dEntry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.segtree.values[self.i][self.j]
    }
}

fn open<B: RangeBounds<usize>>(bounds: B, n: usize) -> (usize, usize) {
    use std::ops::Bound;
    let start = match bounds.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    };
    let end = match bounds.end_bound() {
        Bound::Unbounded => n,
        Bound::Included(&x) => x + 1,
        Bound::Excluded(&x) => x,
    };
    (start, end)
}

fn to_range<K: Ord, B: RangeBounds<K>>(bounds: B, keys: &[K]) -> (usize, usize) {
    use std::ops::Bound;
    let start = match bounds.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(x) => match keys.binary_search(x) {
            Ok(i) | Err(i) => i,
        },
        Bound::Excluded(x) => match keys.binary_search(x) {
            Ok(i) => i + 1,
            Err(i) => i,
        },
    };
    let end = match bounds.end_bound() {
        Bound::Unbounded => keys.len(),
        Bound::Included(x) => match keys.binary_search(x) {
            Ok(i) => i + 1,
            Err(i) => i,
        },
        Bound::Excluded(x) => match keys.binary_search(x) {
            Ok(i) | Err(i) => i,
        },
    };
    (start, end)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter::repeat_with;
    use std::ops::Range;

    mod rolling_hash {
        use super::*;
        pub const P: u64 = 998244353;
        pub const BASE: u64 = 10;
        pub enum O {}
        impl Op for O {
            type Value = (u64, u64);

            fn identity() -> Self::Value {
                (0, 1)
            }

            fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                ((lhs.0 * rhs.1 + rhs.0) % P, lhs.1 * rhs.1 % P)
            }
        }
    }

    mod xor {
        use super::*;
        pub enum O {}
        impl Op for O {
            type Value = u64;

            fn identity() -> Self::Value {
                0
            }

            fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                lhs ^ rhs
            }
        }
    }

    mod sum {
        use super::*;
        pub enum O {}
        impl Op for O {
            type Value = u64;

            fn identity() -> Self::Value {
                0
            }

            fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
                lhs + rhs
            }
        }
    }

    #[test]
    fn test_segtree() {
        use rolling_hash::BASE;
        use rolling_hash::O;

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let mut vec = repeat_with(|| (rng.gen_range(0..BASE), BASE))
                .take(n)
                .collect::<Vec<_>>();
            let mut segtree = Segtree::<O>::new(&vec);
            for _ in 0..q {
                match rng.gen_range(0..2) {
                    // fold
                    0 => {
                        let range = random_range(&mut rng, n);
                        let expected = vec[range.clone()]
                            .iter()
                            .fold(O::identity(), |acc, x| O::mul(&acc, x));
                        let result = segtree.fold(range);
                        assert_eq!(expected, result);
                    }
                    // update
                    1 => {
                        let i = rng.gen_range(0..n);
                        let x = (rng.gen_range(0..BASE), BASE);
                        vec[i] = x;
                        *segtree.entry(i) = x;
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_segtree_bisect() {
        use sum::O;
        const VALUE_LIM: u64 = 10;

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let mut vec = repeat_with(|| rng.gen_range(1..VALUE_LIM))
                .take(n)
                .collect::<Vec<_>>();
            let mut segtree = Segtree::<O>::new(&vec);
            for _ in 0..q {
                match rng.gen_range(0..4) {
                    // fold
                    0 => {
                        let range = random_range(&mut rng, n);
                        let expected = vec[range.clone()]
                            .iter()
                            .fold(O::identity(), |acc, x| O::mul(&acc, x));
                        let result = segtree.fold(range);
                        assert_eq!(expected, result);
                    }
                    // update
                    1 => {
                        let i = rng.gen_range(0..n);
                        let x = rng.gen_range(1..VALUE_LIM);
                        vec[i] = x;
                        *segtree.entry(i) = x;
                    }
                    // max_right
                    2 => {
                        let Range { start, end } = random_range(&mut rng, n);
                        let value_start = vec[start..end].iter().sum::<u64>();
                        let value_end =
                            value_start + vec.get(end).copied().unwrap_or(VALUE_LIM / 2);
                        let max = rng.gen_range(value_start..value_end);
                        let result = segtree.max_right(start, |&x| x <= max);
                        assert_eq!(end, result);
                    }
                    // min_left
                    3 => {
                        let Range { start, end } = random_range(&mut rng, n);
                        let value_start = vec[start..end].iter().sum::<u64>();
                        let value_end =
                            value_start + start.checked_sub(1).map_or(VALUE_LIM / 2, |i| vec[i]);
                        let max = rng.gen_range(value_start..value_end);
                        let result = segtree.min_left(end, |&x| x <= max);
                        assert_eq!(start, result);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_segtree_usability() {
        use rolling_hash::O;
        let _ = Segtree::<O>::from_len(1);
        let _ = Segtree::<O>::new(&[(0, 1)]);
        let _ = Segtree::<O>::from_iter(vec![(0, 1)]);
        let mut segtree = Segtree::<O>::new(&[(0, 1)]);
        let _ = segtree.fold(0..1);
        let _ = segtree.entry(0);
        assert_eq!(segtree.as_slice()[0], (0, 1));
        assert_eq!(segtree[0], (0, 1));
    }

    #[test]
    fn test_sparse_segtree() {
        use rolling_hash::BASE;
        use rolling_hash::O;

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let mut keys = repeat_with(|| rng.gen_range(0..n))
                .take(n)
                .collect::<Vec<_>>();
            keys.sort_unstable();
            let mut vec = keys
                .iter()
                .copied()
                .map(|key| (key, (rng.gen_range(0..BASE), BASE)))
                .collect::<Vec<_>>();
            let mut segtree = vec
                .iter()
                .copied()
                .collect::<SegtreeWithCompression<_, O>>();
            for _ in 0..q {
                match rng.gen_range(0..2) {
                    // fold
                    0 => {
                        let range = random_range(&mut rng, n);
                        let start = keys.binary_search(&range.start).unwrap_or_else(|i| i);
                        let end = keys.binary_search(&range.end).unwrap_or_else(|i| i);
                        let expected = vec[start..end]
                            .iter()
                            .map(|(_, x)| x)
                            .fold(O::identity(), |acc, x| O::mul(&acc, x));
                        let result = segtree.fold(range.clone());
                        assert_eq!(expected, result);
                    }
                    // update
                    1 => {
                        let k = rng.gen_range(0..n);
                        let x = (rng.gen_range(0..BASE), BASE);
                        if let Ok(j) = keys.binary_search(&k) {
                            *segtree.entry(&k) = x;
                            vec[j].1 = x;
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_sparse_segtree_usability() {
        use rolling_hash::O;
        let _ = SegtreeWithCompression::<usize, O>::new(&[(0, (1, 1))]);
        let _ = SegtreeWithCompression::<usize, O>::from_iter(vec![(0, (1, 1))]);
        let mut segtree = SegtreeWithCompression::<usize, O>::new(&[(0, (1, 1))]);
        let _ = segtree.fold(0..1);
        let _ = segtree.entry(&0);
        assert_eq!(segtree[0], (1, 1));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn test_segtree_of_segtree() {
        use xor::O;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..30 {
            let h = rng.gen_range(1..=20);
            let w = rng.gen_range(1..=20);
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=400);
            let mut vec = repeat_with(|| {
                (
                    rng.gen_range(0..h),
                    rng.gen_range(0..w),
                    rng.gen_range(0..u64::MAX),
                )
            })
            .take(n)
            .collect::<Vec<_>>();
            let mut segtree = Sparse2dSegtree::<usize, usize, O>::new(&vec);
            for _ in 0..q {
                match rng.gen_range(0..1) {
                    // fold
                    0 => {
                        let i = random_range(&mut rng, h);
                        let j = random_range(&mut rng, w);
                        let expected = vec
                            .iter()
                            .filter(|(x, y, _)| i.contains(x) && j.contains(y))
                            .map(|(_, _, v)| v)
                            .fold(O::identity(), |acc, x| O::mul(&acc, x));
                        let result = segtree.fold(i.clone(), j.clone());
                        assert_eq!(expected, result);
                    }
                    // update
                    1 => {
                        let k = rng.gen_range(0..n);
                        let y = rng.gen_range(0..u64::MAX);
                        let (i, j, x) = vec[k];
                        vec[k].2 = x ^ y;
                        segtree.apply(&i, &j, |v| *v ^= y);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_dense_2d_segtree() {
        use xor::O;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let h = rng.gen_range(1..=10);
            let w = rng.gen_range(1..=10);
            let q = rng.gen_range(1..=100);
            let mut vec = repeat_with(|| {
                repeat_with(|| rng.gen_range(0..u64::MAX))
                    .take(w)
                    .collect::<Vec<_>>()
            })
            .take(h)
            .collect::<Vec<_>>();
            let mut segtree = Dense2dSegtree::<O>::new(&vec);
            for _ in 0..q {
                match rng.gen_range(0..2) {
                    // fold
                    0 => {
                        let i = random_range(&mut rng, h);
                        let j = random_range(&mut rng, w);
                        let expected = vec[i.clone()]
                            .iter()
                            .flat_map(|v| v[j.clone()].iter())
                            .fold(O::identity(), |acc, x| O::mul(&acc, x));
                        let result = segtree.fold(i.clone(), j.clone());
                        assert_eq!(expected, result);
                    }
                    // update
                    1 => {
                        let i = rng.gen_range(0..h);
                        let j = rng.gen_range(0..w);
                        let x = rng.gen_range(0..u64::MAX);
                        vec[i][j] = x;
                        *segtree.entry(i, j) = x;
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_dense_2d_segtree_usability() {
        use xor::O;
        let _ = Dense2dSegtree::<O>::new(&[vec![0]]);
        let mut segtree = Dense2dSegtree::<O>::new(&[vec![0]]);
        let _ = segtree.fold(0..1, 0..1);
        let _ = segtree.entry(0, 0);
        assert_eq!(segtree[0][0], 0);
    }

    fn random_range(rng: &mut StdRng, n: usize) -> Range<usize> {
        let start = rng.gen_range(0..=n + 1);
        let end = rng.gen_range(0..=n);
        if start <= end {
            start..end
        } else {
            end..start - 1
        }
    }
}
