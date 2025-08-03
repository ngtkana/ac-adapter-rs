use std::ops::AddAssign;
use std::ops::SubAssign;

/// Prefix sum, suffix sum, etc.
pub trait SliceAccum<T> {
    /// Apply $f$ to each adjacent pair from left to right.
    fn for_each_forward<F>(&mut self, f: F)
    where
        F: FnMut(&mut T, &mut T);

    /// Apply $f$ to each adjacent pair from right to left.
    fn for_each_backward<F>(&mut self, f: F)
    where
        F: FnMut(&mut T, &mut T);

    /// Replace $A_i$ with $\sum_{j=0}^{i} A_j$.
    fn prefix_sum(&mut self)
    where
        for<'a> T: AddAssign<&'a T>,
    {
        self.for_each_forward(|x, y| *x += y);
    }

    /// Replace $A_i$ with $A_i - A_{i-1}$.
    fn prefix_sum_inv(&mut self)
    where
        for<'a> T: SubAssign<&'a T>,
    {
        self.for_each_backward(|x, y| *y -= x);
    }

    /// Replace $A_i$ with $\sum_{j=i}^{n-1} A_j$.
    fn suffix_sum(&mut self)
    where
        for<'a> T: AddAssign<&'a T>,
    {
        self.for_each_backward(|x, y| *x += y);
    }

    /// Replace $A_i$ with $A_i - A_{i+1}$.
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
