//! Solve an assignment problem using Hungarian algorithm.
//!
//!
//! # Examples
//!
//! Here is an example seen in [Library Checker](https://judge.yosupo.jp/problem/assignment).
//!
//! ```
//! use hungarian;
//!
//! let c = [
//!     vec![4, 3, 5],
//!     vec![3, 5, 9],
//!     vec![4, 1, 4],
//! ];
//!
//! let result = hungarian::hungarian(&c);
//! assert_eq!(result.value(&c), 9); // Needs `c` to calculate the optimal value.
//! ```

use std::{
    cmp::Ord,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// Returns an optimal solution of an assignment problem.
///
/// [See the crate level documentation](crate)
pub fn hungarian<T: Value>(c: &[Vec<T>]) -> HungarianResult<T> {
    let n = c.len();
    let mut slack = Slack::new(c);
    let mut match_x = vec![None::<usize>; n];
    let mut match_y = vec![None::<usize>; n];
    'OUTER: while let Some(r) = (0..n).find(|&r| match_x[r].is_none()) {
        let mut px = vec![None; n];
        let mut py = vec![None; n];
        let mut sigma = vec![r; n];
        let mut queue = std::collections::VecDeque::from(vec![r]);
        while let Some(x) = queue.pop_front() {
            for y in 0..n {
                if py[y].is_some() || slack.slack(x, y) != T::zero() {
                    continue;
                }
                py[y].replace(x);
                if let Some(z) = match_y[y] {
                    assert_eq!(match_x[z], Some(y));
                    assert_eq!(match_y[y], Some(z));
                    px[z].replace(y);
                    queue.push_back(z);
                    for (j, sj) in sigma.iter_mut().enumerate() {
                        *sj = [z, *sj]
                            .iter()
                            .copied()
                            .min_by_key(|&i| slack.slack(i, j))
                            .unwrap();
                    }
                } else {
                    let mut option_j = Some(y);
                    while let Some(j) = option_j {
                        let i = py[j].unwrap();
                        match_y[j] = Some(i);
                        option_j = match_x[i].replace(j);
                    }
                    continue 'OUTER;
                }
            }
        }
        let delta = (0..n)
            .filter(|&y| py[y].is_none())
            .map(|y| slack.slack(sigma[y], y))
            .min()
            .unwrap();
        slack.add(r, delta);
        (0..n)
            .filter(|&i| px[i].is_some())
            .for_each(|i| slack.add(i, delta));
        (0..n)
            .filter(|&j| py[j].is_some())
            .for_each(|j| slack.sub(j, delta));
    }
    HungarianResult {
        match_x: match_x.iter().map(|&match_x| match_x.unwrap()).collect(),
        match_y: match_y.iter().map(|&match_y| match_y.unwrap()).collect(),
        weight_x: slack.weight_x,
        minus_weight_y: slack.minus_weight_y,
    }
}

/// A trait to adapt a scalar value.
///
/// This trait is already implemented for all the unsigned and signed integers.
pub trait Value:
    Copy + Ord + Add<Output = Self> + AddAssign + Sub<Output = Self> + SubAssign
{
    fn zero() -> Self;
}
macro_rules! impl_value {
    ($($T:ty),* $(,)?) => {$(
        impl Value for $T {
            fn zero() -> Self {
                0
            }
        }
    )*}
}
impl_value! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

/// An object to represent an optimal solution of an assignment problem.
#[derive(Debug, Clone, PartialEq)]
pub struct HungarianResult<T: Value> {
    /// `match_x[x] == y` iff (x, y) is a match in the optimal solution.
    pub match_x: Vec<usize>,
    /// `match_y[y] == x` iff (x, y) is a match in the optimal solution.
    pub match_y: Vec<usize>,
    /// The left half of the optimal solution.
    pub weight_x: Vec<T>,
    /// **-1 times of** the right half of the optimal solution.
    pub minus_weight_y: Vec<T>,
}
impl<T: Value> HungarianResult<T> {
    pub fn value(&self, c: &[Vec<T>]) -> T
    where
        T: std::iter::Sum,
    {
        self.match_x
            .iter()
            .enumerate()
            .map(|(x, &y)| c[x][y])
            .sum::<T>()
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Slack<'a, T> {
    c: &'a [Vec<T>],
    pub weight_x: Vec<T>,
    pub minus_weight_y: Vec<T>,
}

impl<'a, T: Value> Slack<'a, T> {
    pub fn new(c: &'a [Vec<T>]) -> Self {
        let n = c.len();
        let weight_x = c.iter().map(|c| *c.iter().min().unwrap()).collect();
        Self {
            c,
            weight_x,
            minus_weight_y: vec![T::zero(); n],
        }
    }
    pub fn slack(&self, x: usize, y: usize) -> T {
        self.c[x][y] + self.minus_weight_y[y] - self.weight_x[x]
    }
    pub fn add(&mut self, x: usize, value: T) {
        self.weight_x[x] += value;
    }
    pub fn sub(&mut self, y: usize, value: T) {
        self.minus_weight_y[y] += value;
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{hungarian, HungarianResult},
        assert_that::{assert_that, predicates},
        rand::prelude::*,
        test_case::test_case,
    };

    fn validate(c: &[Vec<i32>], result: &HungarianResult<i32>) {
        let HungarianResult {
            match_x,
            match_y,
            weight_x,
            minus_weight_y,
        } = result;
        println!("result = {:?}", &result);
        let weight_y = minus_weight_y.iter().map(|&x| -x).collect::<Vec<_>>();
        let n = match_x.len();
        (0..n).for_each(|x| assert_eq!(match_y[match_x[x]], x));
        (0..n).for_each(|y| assert_eq!(match_x[match_y[y]], y));
        for (x, (weight_x, cx)) in weight_x.iter().zip(c.iter()).enumerate() {
            for (y, (weight_y, &cxy)) in weight_y.iter().zip(cx.iter()).enumerate() {
                if match_x[x] == y {
                    assert_eq!(weight_x + weight_y, cxy);
                }
                assert_that!(&(weight_x + weight_y), predicates::ord::le(cxy));
            }
        }
    }

    #[test_case(&[vec![4, 3, 5], vec![3, 5, 9], vec![4, 1, 4]] => 9; "yosupo judge sample")]
    fn test_hand(c: &[Vec<i32>]) -> i32 {
        test_impl(c)
    }

    #[test]
    fn test_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..7);
            let c = std::iter::repeat_with(|| {
                std::iter::repeat_with(|| rng.gen_range(-99..=99))
                    .take(n)
                    .collect::<Vec<_>>()
            })
            .take(n)
            .collect::<Vec<_>>();
            test_impl(&c);
        }
    }

    fn test_impl(c: &[Vec<i32>]) -> i32 {
        let result = hungarian(c);
        validate(c, &result);
        result.value(&c)
    }
}
