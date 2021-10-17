//! 二分探索をします。
//!
//!
//! # バリエーション
//!
//! * ループ回数固定バージョン: [`binary_search_floating_by_count`]
//! * 絶対誤差指定バージョン: [`binary_search_floating_by_absolute_eps`]

use std::ops::{Add, Div};

/// ループ回数固定バージョン
///
/// # Requirements
///
/// ```[ignore]
/// lower.is_finite()
///     && upper.is_finite()
///     && !is_upper(lower)
///     && is_upper(upper)
/// ```
///
/// # Returns
///
/// ```[ignore]
/// !is_upper(x)
///     && is_upper(y)
///     && (lower..upper).contains(&x)
/// ```
///
/// が成り立ち、かつ `y - x` が `upper - lower` の 2 ^ { count } 分の 1
/// 倍程度であるものを返します。
///
/// # Examples
///
/// 10 回回してみましょう。
///
/// ```
/// use binary_search_floating::binary_search_floating_by_count;
///
/// assert_eq!(
///     binary_search_floating_by_count(0.0, 256.0, |x| 42.0 <= x, 10),
///     [41.75, 42.0]
/// );
/// ```
///
pub fn binary_search_floating_by_count<T: Float>(
    mut lower: T,
    mut upper: T,
    is_upper: impl Fn(T) -> bool,
    count: usize,
) -> [T; 2] {
    debug_assert!(lower.is_finite() && upper.is_finite());
    debug_assert!(lower < upper);
    debug_assert!(!is_upper(lower) && is_upper(upper));
    for _ in 0..count {
        let mid = (lower + upper) / T::two();
        *(if is_upper(mid) {
            &mut upper
        } else {
            &mut lower
        }) = mid;
    }
    [lower, upper]
}

/// 絶対誤差指定バージョン
///
/// # Requirements
///
/// ```[ignore]
/// lower.is_finite()
///     && upper.is_finite()
///     && lower <= upper
///     && !is_upper(lower)
///     && is_upper(upper)
///     && T::zero() < eps && (eps / lower.abs().max(upper.abs()) != T::zero()))
/// ```
///
/// 最後のが成り立たないと、いくら回しても終了しないのでこまりますね。
///
///
///
/// # Returns
///
/// ```[ignore]
/// !is_upper(x)
///     && is_upper(y)
///     && (lower..upper).contains(&x)
///     && (y - x) <= eps
/// ```
///
/// が成り立ち、かつ 2 ^ { count } (y - x) ≒ upper - lower となる `[x, y]` を返します。
///
///
/// # Examples
///
/// 誤差 0.25 以下になるまで回してみましょう。
///
/// ```
/// use binary_search_floating::binary_search_floating_by_absolute_eps;
///
/// assert_eq!(
///     binary_search_floating_by_absolute_eps(0.0, 256.0, |x| 42.0 <= x, 0.25),
///     [41.75, 42.0]
/// );
/// ```
pub fn binary_search_floating_by_absolute_eps<T: Float>(
    mut lower: T,
    mut upper: T,
    is_upper: impl Fn(T) -> bool,
    eps: T,
) -> [T; 2] {
    debug_assert!(lower.is_finite() && upper.is_finite());
    debug_assert!(lower < upper);
    debug_assert!(!is_upper(lower) && is_upper(upper));
    debug_assert!(T::zero() < eps && (eps / lower.abs().max(upper.abs()) != T::zero()));
    while lower + eps < upper {
        let mid = (lower + upper) / T::two();
        *(if is_upper(mid) {
            &mut upper
        } else {
            &mut lower
        }) = mid;
    }
    [lower, upper]
}

/// [`binary_search_floating_by_count`] の引数型のためのトレイトです。全ての整数型に実装されています。
pub trait Float: Add<Output = Self> + Div<Output = Self> + PartialOrd + Copy {
    /// `0.0`
    fn zero() -> Self;
    /// `2.0`
    fn two() -> Self;
    /// `Self` の同名メソッド
    fn max(self, other: Self) -> Self;
    /// `Self` の同名メソッド
    fn abs(self) -> Self;
    /// `Self` の同名メソッド
    fn is_finite(self) -> bool;
}

macro_rules! impl_float {
    ($($T:ty),*) => {$(
        impl Float for $T {
            fn zero() -> Self {
                0.0
            }
            fn two() -> Self {
                2.0
            }
            fn max(self, other: Self) -> Self {
                self.max(other)
            }
            fn abs(self) -> Self {
                self.abs()
            }
            fn is_finite(self) -> bool {
                self.is_finite()
            }
        }
    )*};
}

impl_float! { f32, f64 }

#[cfg(test)]
mod tests {
    use crate::{binary_search_floating_by_absolute_eps, Float};
    use assert_impl::assert_impl;
    use rand::{prelude::StdRng, Rng, SeedableRng};

    // すべての浮動小数点数型は、Float トレイトを実装します。
    #[test]
    fn test_assert_impl_float() {
        assert_impl!(Float: f32, f64);
    }

    #[test]
    fn test_binary_search_floating_by_eps() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..10_000 {
            const EPS: f64 = 1e-5;
            let start = rng.gen_range(-100.0..=100.0 - 3.0 * EPS);
            let end = rng.gen_range(2.0f64.mul_add(EPS, start)..=100.0);
            let lower_bound = rng.gen_range(start + EPS..=end - EPS);
            let eps = rng.gen_range(EPS.ln()..=((end - start) / 2.0).ln()).exp();
            let [start, end] =
                binary_search_floating_by_absolute_eps(start, end, |x| lower_bound <= x, eps);
            assert!(start < lower_bound);
            assert!(lower_bound <= end);
            assert!((end - start) <= eps);
        }
    }
}
