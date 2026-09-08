use std::ops::AddAssign;
use std::ops::SubAssign;

/// スライス $A$ の累積和・その逆変換をまとめたトレイト。全て破壊的（in-place）に書き換える。
///
/// # 例
///
/// ```
/// use riff::SliceAccum;
/// let mut a = [1, 2, 3, 4, 5];
/// a.prefix_sum();
/// assert_eq!(a, [1, 3, 6, 10, 15]);
/// a.prefix_sum_inv();
/// assert_eq!(a, [1, 2, 3, 4, 5]);
/// ```
pub trait SliceAccum<T> {
    /// 隣接する要素対 $(A_{i-1}, A_i)$ に、$i = 1, \ldots, n-1$ の順に $f$ を適用する。
    fn for_each_forward<F>(&mut self, f: F)
    where
        F: FnMut(&mut T, &mut T);

    /// 隣接する要素対 $(A_{i-1}, A_i)$ に、$i = n-1, \ldots, 1$ の順に $f$ を適用する。
    fn for_each_backward<F>(&mut self, f: F)
    where
        F: FnMut(&mut T, &mut T);

    /// 累積和に変換する：$A_i \gets \sum_{j=0}^{i} A_j$。
    fn prefix_sum(&mut self)
    where
        for<'a> T: AddAssign<&'a T>,
    {
        self.for_each_forward(|x, y| *x += y);
    }

    /// [`prefix_sum`](Self::prefix_sum) の逆変換：$A_i \gets A_i - A_{i-1}$（$A_{-1} = 0$）。
    fn prefix_sum_inv(&mut self)
    where
        for<'a> T: SubAssign<&'a T>,
    {
        self.for_each_backward(|x, y| *y -= x);
    }

    /// 逆順の累積和に変換する：$A_i \gets \sum_{j=i}^{n-1} A_j$。
    fn suffix_sum(&mut self)
    where
        for<'a> T: AddAssign<&'a T>,
    {
        self.for_each_backward(|x, y| *x += y);
    }

    /// [`suffix_sum`](Self::suffix_sum) の逆変換：$A_i \gets A_i - A_{i+1}$（$A_n = 0$）。
    fn suffix_sum_inv(&mut self)
    where
        for<'a> T: SubAssign<&'a T>,
    {
        self.for_each_forward(|x, y| *y -= x);
    }
}

impl<T> SliceAccum<T> for [T] {
    fn for_each_forward<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T, &mut T),
    {
        for i in 1..self.len() {
            let (left, right) = self.split_at_mut(i);
            f(&mut right[0], &mut left[i - 1]);
        }
    }

    fn for_each_backward<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut T, &mut T),
    {
        for i in (1..self.len()).rev() {
            let (left, right) = self.split_at_mut(i);
            f(&mut left[i - 1], &mut right[0]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prefix_sum_by() {
        let mut a = [1, 2, 3, 4, 5];
        a.prefix_sum();
        assert_eq!(a, [1, 3, 6, 10, 15]);
        a.prefix_sum_inv();
        assert_eq!(a, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_suffix_sum_by_for_empty() {
        let mut a: [i32; 0] = [];
        a.prefix_sum();
        assert_eq!(a, []);
        a.prefix_sum_inv();
        assert_eq!(a, []);
    }
}
