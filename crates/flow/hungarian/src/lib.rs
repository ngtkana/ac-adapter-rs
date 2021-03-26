//! Solve an assignment problem by Hungarian algorithm.
//!
//! # Example
//!
//! Basic usage:
//!
//! ```
//! use hungarian::hungarian;
//!
//! let result = hungarian(&[
//!     vec![2, 100, 10],
//!     vec![10, 100, 15],
//! ]);
//!
//! assert_eq!(result.value, 17);
//! assert_eq!(&*result.forward, vec![0, 2].as_slice());
//! assert_eq!(&*result.backward, vec![Some(0), None, Some(1)].as_slice());
//! ```
//!

use std::{
    iter::Sum,
    ops::{Add, AddAssign, Sub, SubAssign},
};

/// [See the crate level documentation](crate)
pub fn hungarian<T: Value>(cost_matrix: &[Vec<T>]) -> HungarianResult<T> {
    let h = cost_matrix.len();
    let w = cost_matrix[0].len();
    let mut m = vec![std::usize::MAX; w + 1];

    // initialize a feasible potential
    let mut all_min = T::infinity();
    let mut left = vec![T::infinity(); h].into_boxed_slice();
    for (i, x) in cost_matrix
        .iter()
        .enumerate()
        .map(|(i, v)| v.iter().map(move |&x| (i, x)))
        .flatten()
    {
        if x < all_min {
            all_min = x;
        }
        if x < left[i] {
            left[i] = x;
        }
    }
    left.iter_mut().for_each(|x| *x -= all_min);
    let mut right = vec![T::zero(); w].into_boxed_slice();

    for s in 0..h {
        // dijkstra
        let (pi, mut y) = {
            let mut used_l = vec![false; h];
            let mut used_r = vec![false; w + 1];
            let mut pi = vec![w; w];
            let mut dist = vec![T::infinity(); w];
            m[w] = s;
            let mut x0 = s;
            let mut y0 = w;
            while x0 != std::usize::MAX {
                // find y0
                let (swap, delta) = {
                    let mut swap = w;
                    used_r[y0] = true;
                    used_l[x0] = true;
                    let mut delta = T::infinity();
                    for y in (0..w).filter(|&y| !used_r[y]) {
                        let cost = cost_matrix[x0][y] + left[x0] - right[y];
                        if cost < dist[y] {
                            pi[y] = y0;
                            dist[y] = cost;
                        }
                        if dist[y] < delta {
                            swap = y;
                            delta = dist[y];
                        }
                    }
                    (swap, delta)
                };

                // update x0, y0
                y0 = swap;
                x0 = m[y0];

                // update potential
                for i in (0..h).filter(|&i| !used_l[i]) {
                    left[i] += delta;
                }
                for j in (0..w).filter(|&i| !used_r[i]) {
                    right[j] += delta;
                    dist[j] -= delta;
                }
            }
            (pi, y0)
        };
        // augmentation
        while y != w {
            m[y] = m[pi[y]];
            y = pi[y];
        }
    }
    m.pop();

    let backward = m;
    let mut forward = vec![std::usize::MAX; h].into_boxed_slice();
    let mut value = T::zero();
    for (y, &x) in backward.iter().enumerate() {
        if x != std::usize::MAX {
            forward[x] = y;
            value += cost_matrix[x][y];
        }
    }
    let backward = backward
        .into_iter()
        .map(|x| if x == std::usize::MAX { None } else { Some(x) })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    HungarianResult {
        forward,
        backward,
        left,
        right,
        value,
    }
}

/// A value object to represent the optimal solution of an assignment problem.
#[derive(Debug, Clone, PartialEq)]
pub struct HungarianResult<T: Value> {
    /// Takes the first component of a match and returns the second one.
    pub forward: Box<[usize]>,
    /// Takes the second component of a match and returns the first one.
    pub backward: Box<[Option<usize>]>,
    /// A left half of an optimal potential.
    pub left: Box<[T]>,
    /// A right half of an optimal potential.
    pub right: Box<[T]>,
    /// The value of an optimal solution.
    pub value: T,
}

/// A trait to adapt a value type to [`hungarian`]
///
/// This trait is already implemented for all the signed and unsigned integer types.
pub trait Value:
    Sized + Copy + Add<Output = Self> + AddAssign + Sub<Output = Self> + SubAssign + Sum + PartialOrd
{
    fn zero() -> Self;
    fn infinity() -> Self;
}

macro_rules! impl_value_int {
    ($($T:ident),* $(,)?) => {$(
        impl Value for $T {
            fn zero() -> Self {
                0
            }
            fn infinity() -> Self {
                std::$T::MAX
            }
        }
    )*}
}
impl_value_int! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

macro_rules! impl_value_float {
    ($($T:ident),* $(,)?) => {$(
        impl Value for $T {
            fn zero() -> Self {
                0.
            }
            fn infinity() -> Self {
                std::$T::INFINITY
            }
        }
    )*}
}
impl_value_float!(f32, f64);

#[cfg(test)]
mod tests {
    use approx::{assert_abs_diff_eq, AbsDiffEq};
    use next_permutation::permutations_for_each;

    use {
        super::{hungarian, HungarianResult, Value},
        itertools::Itertools,
        rand::distributions::uniform::SampleUniform,
        rand::{
            prelude::{Rng, StdRng},
            SeedableRng,
        },
        std::iter::repeat_with,
        std::{assert_eq, fmt::Debug, mem::swap, ops::RangeInclusive},
        test_case::test_case,
    };

    #[test_case(&[vec![4, 3, 5], vec![3, 5, 9], vec![4, 1, 4]] => (vec![2, 0, 1], 9); "yosupo sample")]
    #[test_case(&[vec![4, 3, 5], vec![3, 5, 0], vec![4, 1, 4]] => (vec![0, 2, 1], 5); "handmade")]
    fn test_hand(cost_matrix: &[Vec<u8>]) -> (Vec<usize>, u8) {
        let HungarianResult { forward, value, .. } = hungarian(cost_matrix);
        (forward.into_vec(), value)
    }

    #[test_case(5, 5, 100, true)]
    #[test_case(5, 5, 1000, false)]
    #[test_case(30, 500, 30, false)]
    fn test_rand_u32(h: usize, w: usize, iter: usize, brute: bool) {
        test_rand_impl::<i32>(h, w, iter, brute, 0..=100);
    }

    #[test_case(5, 5, 1000, false)]
    fn test_rand_i32(h: usize, w: usize, iter: usize, brute: bool) {
        test_rand_impl::<i32>(h, w, iter, brute, -100..=100);
    }

    #[test_case(5, 5, 1000, false)]
    fn test_rand_f64(h: usize, w: usize, iter: usize, brute: bool) {
        test_rand_impl::<f64>(h, w, iter, brute, -100.0..=100.);
    }

    fn test_rand_impl<T: Value + Debug + Epsilon + SampleUniform>(
        h: usize,
        w: usize,
        iter: usize,
        brute: bool,
        value_range: RangeInclusive<T>,
    ) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            let mut h = rng.gen_range(1..=h);
            let mut w = rng.gen_range(1..=w);
            if h > w {
                swap(&mut h, &mut w);
            }
            let cost_matrix = repeat_with(|| {
                repeat_with(|| rng.gen_range(value_range.clone()))
                    .take(w)
                    .collect_vec()
            })
            .take(h)
            .collect_vec();
            let result = hungarian(&cost_matrix);
            if brute {
                compare_with_brute(&cost_matrix, &result);
            }
            validate(&cost_matrix, &result);
        }
    }

    fn validate<T: Value + Debug + Epsilon>(cost_matrix: &[Vec<T>], result: &HungarianResult<T>) {
        let h = cost_matrix.len();
        let w = cost_matrix[0].len();
        let HungarianResult {
            left,
            right,
            forward,
            backward,
            value,
        } = result;

        // partial 1 on 1 correspondence
        assert_eq!(backward.iter().filter(|&x| x.is_some()).count(), h);
        for i in 0..h {
            assert_eq!(i, backward[forward[i]].unwrap());
        }
        for j in 0..w {
            if let Some(i) = backward[j] {
                assert_eq!(j, forward[i]);
            }
        }

        // feasibility
        for (i, j, x) in cost_matrix
            .iter()
            .enumerate()
            .map(|(i, v)| v.iter().enumerate().map(move |(j, &x)| (i, j, x)))
            .flatten()
        {
            assert!(
                right[j] <= x + left[i] + T::epsilon(),
                "left[{i}] = {left:?}, right[{j}] = {right:?}, cost_matrix[{i}][{j}] = {cost:?}",
                i = i,
                left = left[i],
                j = j,
                right = right[j],
                cost = x,
            );
        }

        // saturation
        for (i, &j) in forward.iter().enumerate() {
            assert_abs_diff_eq!(
                cost_matrix[i][j],
                right[j] - left[i],
                epsilon = T::epsilon()
            );
        }

        // value is correct
        assert_abs_diff_eq!(
            *value,
            forward
                .iter()
                .enumerate()
                .map(|(i, &j)| cost_matrix[i][j])
                .sum::<T>(),
            epsilon = T::epsilon()
        );
    }

    fn compare_with_brute<T: Value + Debug>(cost_matrix: &[Vec<T>], result: &HungarianResult<T>) {
        let h = cost_matrix.len();
        let w = cost_matrix[0].len();
        let mut value = T::infinity();
        permutations_for_each((0..w).collect_vec(), |v| {
            let now = calculate_score(cost_matrix, v[..h].iter().copied());
            if now < value {
                value = now;
            }
        });
        assert_eq!(value, result.value);
    }

    fn calculate_score<T: Value + Debug>(
        cost_matrix: &[Vec<T>],
        perm: impl IntoIterator<Item = usize>,
    ) -> T {
        perm.into_iter()
            .enumerate()
            .map(|(i, j)| cost_matrix[i][j])
            .sum::<T>()
    }

    trait Epsilon: AbsDiffEq<Epsilon = Self> {
        fn epsilon() -> Self;
    }
    macro_rules! impl_epsilon_int {
        ($($T:ident),* $(,)?) => {$(
            impl Epsilon for $T {
                fn epsilon() -> Self {
                    0
                }
            }
        )*}
    }
    impl_epsilon_int! {
        u8, u16, u32, u64, usize,
        i8, i16, i32, i64, isize,
    }
    macro_rules! impl_epsilon_float {
        ($($T:ident),* $(,)?) => {$(
            impl Epsilon for $T {
                fn epsilon() -> Self {
                    1e-5
                }
            }
        )*}
    }
    impl_epsilon_float!(f32, f64);
}
