#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! slice の機能を増やします。

/// slice に実装されます。
pub trait Partitioned {
    /// slice `[T]` ならば `T` のことです。
    type Item;

    /// `f(&self[i])` が `true` となる最小の `i` を返します。
    /// 存在しない場合は `self.len()` を返します。
    ///
    /// # Example
    /// ```
    /// use slicetools::Partitioned;
    /// let seq = [3, 4, 6, 6, 7];
    /// assert_eq!(
    ///     seq.partition_point(|&x| 5 <= x),
    ///     2
    /// );
    /// ```
    fn partition_point(&self, f: impl Fn(&Self::Item) -> bool) -> usize;
}

impl<T> Partitioned for [T] {
    type Item = T;
    fn partition_point(&self, f: impl Fn(&Self::Item) -> bool) -> usize {
        if f(&self[0]) {
            0
        } else {
            let mut l = 0;
            let mut r = self.len();
            while 1 < r - l {
                let c = l + (r - l) / 2;
                match f(&self[c]) {
                    false => {
                        l = c;
                    }
                    true => {
                        r = c;
                    }
                }
            }
            r
        }
    }
}

/// `Ord` を実装したアイテムからなる slice に実装されます。
pub trait Sorted: Partitioned
where
    Self::Item: Ord,
{
    /// `x <= f(i)` が `true` となる最小の `i` を返します。
    /// 存在しない場合は `self.len()` を返します。
    ///
    /// # Example
    /// ```
    /// use slicetools::{Partitioned, Sorted};
    /// let seq = [3, 4, 6, 6, 7];
    /// assert_eq!(seq.lower_bound(&2), 0);
    /// assert_eq!(seq.lower_bound(&3), 0);
    /// assert_eq!(seq.lower_bound(&4), 1);
    /// assert_eq!(seq.lower_bound(&5), 2);
    /// assert_eq!(seq.lower_bound(&6), 2);
    /// assert_eq!(seq.lower_bound(&7), 4);
    /// assert_eq!(seq.lower_bound(&8), 5);
    /// assert_eq!(seq.lower_bound(&9), 5);
    /// ```
    fn lower_bound(&self, x: &Self::Item) -> usize {
        self.partition_point(|y| x <= y)
    }

    /// `x < f(i)` が `true` となる最小の `i` を返します。
    /// 存在しない場合は `self.len()` を返します。
    ///
    /// # Example
    /// ```
    /// use slicetools::{Partitioned, Sorted};
    /// let seq = [3, 4, 6, 6, 7];
    /// assert_eq!(seq.upper_bound(&2), 0);
    /// assert_eq!(seq.upper_bound(&3), 1);
    /// assert_eq!(seq.upper_bound(&4), 2);
    /// assert_eq!(seq.upper_bound(&5), 2);
    /// assert_eq!(seq.upper_bound(&6), 4);
    /// assert_eq!(seq.upper_bound(&7), 5);
    /// assert_eq!(seq.upper_bound(&8), 5);
    /// assert_eq!(seq.upper_bound(&9), 5);
    /// ```
    fn upper_bound(&self, x: &Self::Item) -> usize {
        self.partition_point(|y| x < y)
    }
}

impl<T: Partitioned + ?Sized> Sorted for T where T::Item: Ord {}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
