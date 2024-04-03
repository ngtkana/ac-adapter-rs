//! # Sparse Table
//!
//! * [`SparseTable`] (1-dimensional)
//! * [`SparseTable2d`] (2-dimensional)
//!
//! # [`Op`] trait
//!
//! [`Op::mul`] must be associative and idempotent.

use std::fmt::Debug;
use std::iter::FromIterator;
use std::ops::Index;
use std::ops::RangeBounds;

/// A trait for the operation used in sparse tables.
pub trait Op {
    /// The type of the values.
    type Value;

    /// Multiplies two values: $x \cdot y$.
    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

/// A sparse table for 1-dimensional range queries.
pub struct SparseTable<O: Op> {
    table: Vec<Vec<O::Value>>,
}
impl<O: Op> SparseTable<O> {
    /// Constructs a sparse table from a vector of values.
    pub fn new(values: Vec<O::Value>) -> Self {
        values.into()
    }

    /// Constructs a sparse table from a slice of values.
    pub fn clone_from_slice(values: &[O::Value]) -> Self
    where
        O::Value: Clone,
    {
        values.into()
    }

    /// Returns the value at the given index.
    pub fn get(&self, index: usize) -> &O::Value {
        &self.table[0][index]
    }

    /// Returns $x_l \cdot x_{l+1} \cdot \ldots \cdot x_{r-1}$, or `None` if $l = r$.
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Value> {
        let (start, end) = open(range, self.table[0].len());
        assert!(start <= end);
        (start < end).then_some(())?;
        let p = (end - start).ilog2() as usize;
        let row = &self.table[p];
        Some(O::mul(&row[start], &row[end - (1 << p)]))
    }

    /// Returns an iterator over the values.
    pub fn iter(&self) -> impl Iterator<Item = &O::Value> {
        self.table[0].iter()
    }

    /// Returns a slice of the values.
    pub fn as_slice(&self) -> &[O::Value] {
        &self.table[0]
    }

    /// Collects the values into a vector.
    pub fn collect_vec(&self) -> Vec<O::Value>
    where
        O::Value: Clone,
    {
        self.table[0].clone()
    }

    /// Returns the inner table.
    pub fn inner(&self) -> &Vec<Vec<O::Value>> {
        &self.table
    }
}

impl<O: Op> Debug for SparseTable<O>
where
    O::Value: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SparseTable")
            .field("table", &self.table)
            .finish()
    }
}

impl<O: Op> From<Vec<O::Value>> for SparseTable<O> {
    fn from(values: Vec<O::Value>) -> Self {
        let n = values.len();
        let mut table = vec![values];
        let mut i = 1;
        while i * 2 <= n {
            let last = table.last().unwrap();
            let current = last
                .iter()
                .zip(&last[i..])
                .map(|(a, b)| O::mul(a, b))
                .collect();
            table.push(current);
            i *= 2;
        }
        Self { table }
    }
}

impl<'a, O: Op> From<&'a [O::Value]> for SparseTable<O>
where
    O::Value: Clone,
{
    fn from(values: &'a [O::Value]) -> Self {
        values.to_vec().into()
    }
}

impl<O: Op> FromIterator<O::Value> for SparseTable<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        iter.into_iter().collect::<Vec<_>>().into()
    }
}

impl<O: Op> Index<usize> for SparseTable<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        &self.table[0][index]
    }
}

/// A sparse table for 2-dimensional range queries.
///
/// The operation must also be commutative.
pub struct SparseTable2d<O: Op> {
    table: Vec<Vec<Vec<Vec<O::Value>>>>,
}

impl<O: Op> SparseTable2d<O> {
    /// Constructs a sparse table from a vector of values.
    pub fn new(values: Vec<Vec<O::Value>>) -> Self {
        values.into()
    }

    /// Constructs a sparse table from a slice of values.
    pub fn clone_from_slice(values: &[Vec<O::Value>]) -> Self
    where
        O::Value: Clone,
    {
        values.into()
    }

    /// Returns $(x_{i_0, j_0} \cdot \dots \cdot x_{i_1-1, j_0}) \cdot \dots \cdot (x_{i_0, j_1-1} \cdot \dots \cdot x_{i_1-1, j_1-1})$, or `None` if $i_0 = i_1$ or $j_0 = j_1$.
    pub fn fold(&self, i: impl RangeBounds<usize>, j: impl RangeBounds<usize>) -> Option<O::Value> {
        let (i0, mut i1) = open(i, self.table[0][0].len());
        let (j0, mut j1) = open(j, self.table[0][0].first().map_or(0, Vec::len));
        assert!(i0 <= i1);
        assert!(j0 <= j1);
        (i0 < i1 && j0 < j1).then_some(())?;
        let p = (i1 - i0).ilog2() as usize;
        let q = (j1 - j0).ilog2() as usize;
        let grid = &self.table[p][q];
        i1 -= 1 << p;
        j1 -= 1 << q;
        Some(O::mul(
            &O::mul(&grid[i0][j0], &grid[i1][j0]),
            &O::mul(&grid[i0][j1], &grid[i1][j1]),
        ))
    }

    /// Returns that yields the row of the table.
    pub fn iter(&self) -> impl Iterator<Item = &[O::Value]> {
        self.table[0][0].iter().map(Vec::as_slice)
    }

    /// Returns a slice of the values.
    pub fn as_slice(&self) -> &[Vec<O::Value>] {
        &self.table[0][0]
    }

    /// Collects the values into a vector of vectors.
    pub fn collect_vec(&self) -> Vec<Vec<O::Value>>
    where
        O::Value: Clone,
    {
        self.table[0][0].clone()
    }

    /// Returns the inner table.
    pub fn inner(&self) -> &Vec<Vec<Vec<Vec<O::Value>>>> {
        &self.table
    }
}

impl<O: Op> Debug for SparseTable2d<O>
where
    O::Value: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SparseTable2d")
            .field("table", &self.table)
            .finish()
    }
}

impl<O: Op> From<Vec<Vec<O::Value>>> for SparseTable2d<O> {
    fn from(values: Vec<Vec<O::Value>>) -> Self {
        let h = values.len();
        let w = values.first().map_or(0, Vec::len);
        let mut table = vec![vec![values]];
        let mut j = 1;
        while j * 2 <= w {
            let last = table[0].last().unwrap();
            let current = last
                .iter()
                .map(|row| {
                    row.iter()
                        .zip(&row[j..])
                        .map(|(a, b)| O::mul(a, b))
                        .collect::<Vec<_>>()
                })
                .collect();
            table[0].push(current);
            j *= 2;
        }
        let mut i = 1;
        while i * 2 <= h {
            let last = table.last().unwrap();
            let current = last
                .iter()
                .map(|grid| {
                    grid.iter()
                        .zip(&grid[i..])
                        .map(|(a, b)| {
                            a.iter()
                                .zip(b)
                                .map(|(a, b)| O::mul(a, b))
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>()
                })
                .collect();
            table.push(current);
            i *= 2;
        }
        Self { table }
    }
}

impl<'a, O: Op> From<&'a [Vec<O::Value>]> for SparseTable2d<O>
where
    O::Value: Clone,
{
    fn from(values: &'a [Vec<O::Value>]) -> Self {
        values.to_vec().into()
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

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::ops::Range;

    enum O {}
    impl Op for O {
        type Value = u64;

        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            (*lhs).max(*rhs)
        }
    }

    #[test]
    fn test_sparse_table() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let vec = (0..n)
                .map(|_| rng.gen_range(0..u64::MAX))
                .collect::<Vec<_>>();
            let st = SparseTable::<O>::clone_from_slice(&vec);
            for _ in 0..q {
                let range = random_range(&mut rng, n);
                let expected = vec[range.clone()].iter().copied().max();
                let actual = st.fold(range.clone());
                assert_eq!(expected, actual);
            }
        }
    }

    #[test]
    fn test_sparse_table_2d() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let h = rng.gen_range(1..=10);
            let w = rng.gen_range(1..=10);
            let q = rng.gen_range(1..=100);
            let vec = (0..h)
                .map(|_| {
                    (0..w)
                        .map(|_| rng.gen_range(0..u64::MAX))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>();
            let st = SparseTable2d::<O>::clone_from_slice(&vec);
            for _ in 0..q {
                let i = random_range(&mut rng, h);
                let j = random_range(&mut rng, w);
                let expected = vec[i.clone()]
                    .iter()
                    .flat_map(|row| &row[j.clone()])
                    .max()
                    .copied();
                let actual = st.fold(i.clone(), j.clone());
                assert_eq!(expected, actual);
            }
        }
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
