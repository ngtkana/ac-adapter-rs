//! 累積和です。
//!
//! # 使い方
//!
//! 零元はコンストラクタ引数で指定します。
//!
//! [`get`], [`range`], [`sum`] などで要素を取得して、[`push`] で後ろに入れます。
//! 途中の更新は原理的に不可能（やりたければ BIT を使いましょう！）ですから、
//! 作っていません。
//!
//! ```
//! use prefix_sum::*;
//! let mut a = PrefixSum::with_zero(0u32);
//!
//! a.push(2);
//! a.push(4);
//! a.push(3);
//!
//! assert_eq!(a.get(0), 2);
//! assert_eq!(a.get(1), 4);
//! assert_eq!(a.get(2), 3);
//!
//! assert_eq!(a.range(..), vec![2, 4, 3]);
//! assert_eq!(a.range(..2), vec![2, 4]);
//! assert_eq!(a.range(0..=0), vec![2]);
//!
//! assert_eq!(a.sum(..), 9);
//! assert_eq!(a.sum(..2), 6);
//! assert_eq!(a.sum(0..=0), 2);
//! ```
//!
//! [`get`]: struct.PrefixSum.html#method.get
//! [`range`]: struct.PrefixSum.html#method.range
//! [`sum`]: struct.PrefixSum.html#method.sum
//! [`push`]: struct.PrefixSum.html#method.push

use std::ops;

/// 本体です。
#[derive(Debug, Clone)]
pub struct PrefixSum<T>
where
    T: Clone + ops::Add<Output = T> + ops::Sub<Output = T>,
{
    table: Vec<T>,
}

impl<T> PrefixSum<T>
where
    T: Clone + ops::Add<Output = T> + ops::Sub<Output = T>,
{
    /// 空であることです。
    pub fn is_empty(&self) -> bool {
        self.table.len() == 1
    }

    /// 長さです。中身の長さは `self.len() + 1` です。
    pub fn len(&self) -> usize {
        self.table.len() - 1
    }

    /// コンストラクタです。引数は零元です。
    pub fn with_zero(x: T) -> Self {
        Self { table: vec![x] }
    }

    /// 挿入します。
    pub fn push(&mut self, x: T) {
        let x = self.table.last().unwrap().clone() + x;
        self.table.push(x);
    }

    /// 和を取ります。
    pub fn sum(&self, range: impl ops::RangeBounds<usize>) -> T {
        let ops::Range { start, end } = range_bounds_to_range(range, self.len());
        assert!(
            start <= end,
            "変な区間を渡すのをやめましょう！ len = {}, range = {:?}",
            self.len(),
            start..end
        );
        assert!(
            end <= self.len(),
            "添字が大きすぎます！ len = {}, range = {:?}",
            self.len(),
            start..end
        );
        self.table[end].clone() - self.table[start].clone()
    }

    /// `i` 番目を取ります。
    pub fn get(&self, i: usize) -> T {
        assert!(
            i < self.len(),
            "添字が大きすぎます！ len = {}, i = {}",
            self.len(),
            i
        );
        self.table[i + 1].clone() - self.table[i].clone()
    }

    /// 範囲を `Vec` に集めます。
    pub fn range(&self, range: impl ops::RangeBounds<usize>) -> Vec<T> {
        let ops::Range { start, end } = range_bounds_to_range(range, self.len());
        (start..end).map(|i| self.get(i)).collect()
    }
}

fn range_bounds_to_range(range: impl ops::RangeBounds<usize>, len: usize) -> ops::Range<usize> {
    let start = match range.start_bound() {
        ops::Bound::Excluded(&x) => x + 1,
        ops::Bound::Included(&x) => x,
        ops::Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        ops::Bound::Excluded(&x) => x,
        ops::Bound::Included(&x) => x + 1,
        ops::Bound::Unbounded => len,
    };
    ops::Range { start, end }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hand() {
        let mut a = PrefixSum::with_zero(0_u32);
        a.push(1);
        assert_eq!(a.get(0), 1);
        assert_eq!(a.range(..), vec![1]);
        assert_eq!(a.sum(..), 1);
    }
}
