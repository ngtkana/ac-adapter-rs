//! An extension trait of [`Iterator`]

use std::ops::{AddAssign, Sub};

/// Returns $\sum \left \lbrace a _ j \vert 0 \le j \lt i \right \rbrace$.
///
/// # Example
/// ```
/// # use itermore::open_prefix_sum;
/// # use itertools::assert_equal;
/// assert_equal(
///     open_prefix_sum(vec![10, 11, 12], 0),
///     vec![0, 10, 21],
/// );
/// ```
pub fn open_prefix_sum<I: IntoIterator<Item = T>, T>(
    iter: I,
    zero: T,
) -> OpenPrefixSum<I::IntoIter> {
    OpenPrefixSum {
        sum: zero,
        iter: iter.into_iter(),
    }
}

/// Returns $\sum \left \lbrace a _ j \vert 0 \le j \le i \right \rbrace$.
///
/// # Example
/// ```
/// # use itermore::closed_prefix_sum;
/// # use itertools::assert_equal;
/// assert_equal(
///     closed_prefix_sum(vec![10, 11, 12], 0),
///     vec![10, 21, 33],
/// );
/// ```
pub fn closed_prefix_sum<I: IntoIterator<Item = T>, T>(
    iter: I,
    zero: T,
) -> ClosedPrefixSum<I::IntoIter> {
    ClosedPrefixSum {
        sum: zero,
        iter: iter.into_iter(),
    }
}

/// Returns $a _ i - \min \left \lbrace a _ j \vert 0 \le j \le i \right \rbrace$.
///
/// # Example
/// ```
/// # use itermore::closed_max_increase;
/// # use itertools::assert_equal;
/// assert_equal(
///     closed_max_increase(vec![10, 11, 8, 12, 5, 11], std::i32::MAX),
///     vec![0, 1, 0, 4, 0, 6],
/// );
/// ```
pub fn closed_max_increase<I: IntoIterator<Item = T>, T>(
    iter: I,
    max: T,
) -> ClosedMaxIncrease<I::IntoIter> {
    ClosedMaxIncrease {
        min: max,
        iter: iter.into_iter(),
    }
}

/// An extension trait of [`Iterator`]
pub trait IterMore: Iterator + Sized {
    fn open_prefix_sum(self, zero: Self::Item) -> OpenPrefixSum<Self>;
    fn closed_prefix_sum(self, zero: Self::Item) -> ClosedPrefixSum<Self>;
    fn closed_max_increase(self, zero: Self::Item) -> ClosedMaxIncrease<Self>;
}
impl<I: Iterator> IterMore for I {
    fn open_prefix_sum(self, zero: Self::Item) -> OpenPrefixSum<Self> {
        OpenPrefixSum {
            sum: zero,
            iter: self,
        }
    }
    fn closed_prefix_sum(self, zero: Self::Item) -> ClosedPrefixSum<Self> {
        ClosedPrefixSum {
            sum: zero,
            iter: self,
        }
    }
    fn closed_max_increase(self, max: Self::Item) -> ClosedMaxIncrease<Self> {
        ClosedMaxIncrease {
            min: max,
            iter: self,
        }
    }
}
/// Return value of [`open_prefix_sum`].
pub struct OpenPrefixSum<I: Iterator> {
    sum: I::Item,
    iter: I,
}
impl<I: Iterator> Iterator for OpenPrefixSum<I>
where
    I::Item: AddAssign + Copy,
{
    type Item = I::Item;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(key) => {
                let ans = self.sum;
                self.sum += key;
                Some(ans)
            }
            None => None,
        }
    }
}
/// Return value of [`closed_prefix_sum`].
pub struct ClosedPrefixSum<I: Iterator> {
    sum: I::Item,
    iter: I,
}
impl<I: Iterator> Iterator for ClosedPrefixSum<I>
where
    I::Item: AddAssign + Copy,
{
    type Item = I::Item;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(key) => {
                self.sum += key;
                Some(self.sum)
            }
            None => None,
        }
    }
}
/// Return value of [`closed_max_increase`].
pub struct ClosedMaxIncrease<I: Iterator> {
    min: I::Item,
    iter: I,
}
impl<I: Iterator> Iterator for ClosedMaxIncrease<I>
where
    I::Item: Sub<Output = I::Item> + Ord + Copy,
{
    type Item = I::Item;
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            Some(key) => {
                self.min = self.min.min(key);
                Some(key - self.min)
            }
            None => None,
        }
    }
}
