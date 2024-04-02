//! # Suffix Sum
//!
//! # [`Op`] trait
//!
//! * [`Op::identity`]: Returns the identity value $e$.
//! * [`Op::mul`]: Multiplies two values: $x \cdot y$.
//! * [`Op::div`]: Divides two values: $x \cdot y^{-1}$.
//!
//! The multiplication must be associative and invertible (divisible).
//!
//! Furthermore, the multiplication must be commutative for [`SuffixSum2d`].
use std::fmt;
use std::iter::repeat_with;
use std::ops::RangeBounds;

/// A trait for segment tree operations.
pub trait Op {
    /// The value type.
    type Value;

    /// Returns the identity value $e$.
    fn identity() -> Self::Value;
    /// Multiplies two values: $x \cdot y$.
    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
    /// Divides two values: $x \cdot y^{-1}$.
    fn div(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

/// A structure that stores the suffix sum of a sequence.
pub struct SuffixSum<O: Op> {
    values: Vec<O::Value>,
}
impl<O: Op> SuffixSum<O> {
    /// Constructs a new instance.
    pub fn new(values: &[O::Value]) -> Self
    where
        O::Value: Clone,
    {
        Self::from(values.to_vec())
    }

    /// Returns $x_i$.
    pub fn get(&self, index: usize) -> O::Value {
        assert!(index < self.values.len() - 1);
        O::div(&self.values[index], &self.values[index + 1])
    }

    /// Returns $x_l \cdot x_{l+1} \cdot \ldots \cdot x_{r-1}$.
    pub fn fold(&self, range: impl RangeBounds<usize>) -> O::Value {
        let (start, end) = open(range, self.values.len() - 1);
        assert!(start <= end && end < self.values.len());
        O::div(&self.values[start], &self.values[end])
    }

    /// Collects the values to a vector.
    pub fn collect_vec(&self) -> Vec<O::Value>
    where
        O::Value: Clone,
    {
        let mut values = self.values.clone();
        values.pop();
        let n = values.len();
        if n != 0 {
            for i in 0..n - 1 {
                values[i] = O::div(&values[i], &values[i + 1]);
            }
        }
        values
    }

    /// Returns a reference to the inner values.
    pub fn inner(&self) -> &[O::Value] {
        &self.values
    }
}

impl<O: Op> fmt::Debug for SuffixSum<O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SuffixSum").field(&self.values).finish()
    }
}

impl<O: Op> FromIterator<O::Value> for SuffixSum<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        Self::from(iter.into_iter().collect::<Vec<_>>())
    }
}

impl<O: Op> From<Vec<O::Value>> for SuffixSum<O> {
    fn from(mut values: Vec<O::Value>) -> Self {
        let n = values.len();
        values.push(O::identity());
        if n != 0 {
            for i in (0..n - 1).rev() {
                values[i] = O::mul(&values[i], &values[i + 1]);
            }
        }
        Self { values }
    }
}

/// A structure that stores the suffix sum of a 2D sequence.
///
/// The multiplication must be commutative.
pub struct SuffixSum2d<O: Op> {
    values: Vec<Vec<O::Value>>,
}
impl<O: Op> SuffixSum2d<O> {
    /// Constructs a new instance.
    pub fn new(values: &[Vec<O::Value>]) -> Self
    where
        O::Value: Clone,
    {
        Self::from(values.to_vec())
    }

    /// Returns $x_{i,j}$.
    pub fn get(&self, i: usize, j: usize) -> O::Value {
        assert!(i < self.values.len() - 1);
        assert!(j < self.values[0].len() - 1);
        O::div(
            &O::mul(&self.values[i][j], &self.values[i + 1][j + 1]),
            &O::mul(&self.values[i][j + 1], &self.values[i + 1][j]),
        )
    }

    /// Returns $\left ( x_{i_0, j_0} \cdot \dots \cdot x_{i_0, j_1-1} \right ) \cdot \left ( x_{i_1, j_0} \cdot \dots \cdot x_{i_1-1, j_0} \right )$.
    pub fn fold(&self, i: impl RangeBounds<usize>, j: impl RangeBounds<usize>) -> O::Value {
        let (i0, i1) = open(i, self.values.len() - 1);
        let (j0, j1) = open(j, self.values[0].len());
        assert!(i0 <= i1 && i1 < self.values.len());
        assert!(j0 <= j1 && j1 <= self.values.get(0).map_or(0, Vec::len));
        O::div(
            &O::mul(&self.values[i0][j0], &self.values[i1][j1]),
            &O::mul(&self.values[i0][j1], &self.values[i1][j0]),
        )
    }

    /// Collects the values to a vector.
    pub fn collect_vec(&self) -> Vec<Vec<O::Value>>
    where
        O::Value: Clone,
    {
        let mut values = self.values.clone();
        let h = values.len();
        let w = values[0].len();
        for values in &mut values {
            for j in 0..w - 1 {
                values[j] = O::div(&values[j], &values[j + 1]);
            }
        }
        for i in 0..h - 1 {
            for j in 0..w {
                values[i][j] = O::div(&values[i][j], &values[i + 1][j]);
            }
        }
        for values in &mut values {
            values.pop().unwrap();
        }
        values.pop().unwrap();
        values
    }

    /// Returns a reference to the inner values.
    pub fn inner(&self) -> &Vec<Vec<O::Value>> {
        &self.values
    }
}

impl<O: Op> fmt::Debug for SuffixSum2d<O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SuffixSum2d").field(&self.values).finish()
    }
}

impl<O: Op> From<Vec<Vec<O::Value>>> for SuffixSum2d<O> {
    fn from(mut values: Vec<Vec<O::Value>>) -> Self {
        let h = values.len();
        let w = values.get(0).map_or(0, Vec::len);
        values.push(repeat_with(O::identity).take(w).collect());
        for values in &mut values {
            values.push(O::identity());
        }
        for i in (0..=h).rev() {
            for j in (0..w).rev() {
                values[i][j] = O::mul(&values[i][j], &values[i][j + 1]);
            }
        }
        for i in (0..h).rev() {
            for j in (0..=w).rev() {
                values[i][j] = O::mul(&values[i][j], &values[i + 1][j]);
            }
        }
        Self { values }
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
    use std::ops::Bound;
    use std::ops::Range;

    const P: u64 = 998244353;
    enum O {}
    impl Op for O {
        type Value = u64;

        fn identity() -> Self::Value {
            0
        }

        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            (lhs + rhs) % P
        }

        fn div(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            (lhs + P - rhs) % P
        }
    }

    #[test]
    fn test_suffix_sum() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=100);
            let q = rng.gen_range(1..=100);
            let values: Vec<_> = (0..n).map(|_| rng.gen_range(0..P)).collect();
            let suffix_sum = SuffixSum::<O>::new(&values);
            assert_eq!(suffix_sum.collect_vec(), values);
            for _ in 0..q {
                match rng.gen_range(0..2) {
                    // get
                    0 => {
                        let index = rng.gen_range(0..n);
                        let expected = values[index];
                        assert_eq!(suffix_sum.get(index), expected);
                    }
                    // fold
                    1 => {
                        let range = random_range(&mut rng, n);
                        let expected = values[range.clone()]
                            .iter()
                            .fold(0, |acc, &x| (acc + x) % P);
                        assert_eq!(suffix_sum.fold(range), expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_suffix_sum_usability() {
        let _ = SuffixSum::<O>::new(&[1, 2, 3, 4, 5]);
        let _ = SuffixSum::<O>::from(vec![1, 2, 3, 4, 5]);
        let _ = [1, 2, 3, 4, 5].into_iter().collect::<SuffixSum<O>>();
        let _ = SuffixSum::<O>::new(&[1, 2, 3, 4, 5]).collect_vec();
        let _ = SuffixSum::<O>::new(&[1, 2, 3, 4, 5]).fold(..);
    }

    #[test]
    fn test_suffix_sum_various_ranges() {
        let values = vec![1, 2, 3, 4, 5];
        let suffix_sum = SuffixSum::<O>::new(&values);
        assert_eq!(suffix_sum.fold(..), 15);
        assert_eq!(suffix_sum.fold(..2), 3);
        assert_eq!(suffix_sum.fold(1..), 14);
        assert_eq!(suffix_sum.fold(1..3), 5);
        assert_eq!(suffix_sum.fold(1..=3), 9);
        assert_eq!(suffix_sum.fold((Bound::Included(1), Bound::Excluded(3))), 5);
    }

    #[test]
    fn test_suffix_sum_empty() {
        let values = vec![];
        let suffix_sum = SuffixSum::<O>::new(&values);
        assert_eq!(suffix_sum.collect_vec(), values);
        assert_eq!(suffix_sum.fold(..), 0);
    }

    #[test]
    #[should_panic]
    #[allow(clippy::reversed_empty_ranges)]
    fn test_suffix_sum_invalid_range() {
        let values = vec![1, 2, 3, 4, 5];
        let suffix_sum = SuffixSum::<O>::new(&values);
        suffix_sum.fold(3..1);
    }

    #[test]
    #[should_panic]
    fn test_suffix_sum_out_of_range() {
        let values = vec![1, 2, 3, 4, 5];
        let suffix_sum = SuffixSum::<O>::new(&values);
        suffix_sum.fold(0..6);
    }

    #[test]
    fn test_suffix_sum_2d() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let h = rng.gen_range(1..=10);
            let w = rng.gen_range(1..=10);
            let q = rng.gen_range(1..=100);
            let values: Vec<Vec<_>> = (0..h)
                .map(|_| (0..w).map(|_| rng.gen_range(0..P)).collect())
                .collect();
            let suffix_sum = SuffixSum2d::<O>::new(&values);
            assert_eq!(suffix_sum.collect_vec(), values);
            for _ in 0..q {
                match rng.gen_range(0..2) {
                    // get
                    0 => {
                        let i = rng.gen_range(0..h);
                        let j = rng.gen_range(0..w);
                        let expected = values[i][j];
                        assert_eq!(suffix_sum.get(i, j), expected);
                    }
                    // fold
                    1 => {
                        let row = random_range(&mut rng, h);
                        let col = random_range(&mut rng, w);
                        let expected = values[row.clone()]
                            .iter()
                            .flat_map(|row| &row[col.clone()])
                            .fold(0, |acc, x| (acc + x) % P);
                        assert_eq!(suffix_sum.fold(row, col), expected);
                    }
                    _ => unreachable!(),
                }
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
