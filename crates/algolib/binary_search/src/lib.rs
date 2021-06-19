//! 二分探索をします。
//!
//! 正確な仕様は関数のドキュメントを見ましょう！
//!
//! * 整数バージョン: [`binary_search_intger`]
//! * 浮動小数点数バージョン: [`binary_search_floating`]
//!
//!
//! # Examples
//!
//! ## 整数
//!
//! 差が 1 になるまで回ります。
//!
//! ```
//! use binary_search::binary_search_intger;
//!
//! assert_eq!(binary_search_intger(-10, 10, |x| 4 <= x), [3, 4]);
//! assert_eq!(binary_search_intger(-10, 10, |x| -4 <= x), [-5, -4]);
//! ```
//!
//! ## 浮動小数点数
//!
//! ループが固定回数です。この場合 18 回です。
//!
//! ```
//! use binary_search::binary_search_floating;
//!
//! assert_eq!(
//!     binary_search_floating(0.0, 65536.0, |x| 42.0 <= x, 18),
//!     [41.75, 42.0]
//! );
//! ```
//!

use std::ops::{Add, Div};

/// 整数で二分探索をします。
///
/// # Requirements
///
/// ```[ignore]
/// !is_upper(lower) && is_upper(upper)
/// ```
///
/// が成り立つこと。
///
///
/// # Returns
///
/// ```[ignore]
/// !is_upper(x)
///     && is_upper(y)
///     && x + 1 == y
///     && (lower..upper).contains(&x)
/// ```
///
/// を満たす `[x, y]` を返します。
///
pub fn binary_search_intger<T: Int>(
    mut lower: T,
    mut upper: T,
    is_upper: impl Fn(T) -> bool,
) -> [T; 2] {
    debug_assert!(lower < upper);
    while lower + T::one() != upper {
        let mid = lower.midpoint_sorted(upper);
        *(if is_upper(mid) {
            &mut upper
        } else {
            &mut lower
        }) = mid;
    }
    [lower, upper]
}

/// 浮動小数点数で二分探索をします。
///
/// # Requirements
///
/// ```[ignore]
/// !is_upper(lower) && is_upper(upper)
/// ```
///
/// が成り立つこと。
///
///
/// # Returns
///
/// ```[ignore]
/// !is_upper(x)
///     && is_upper(y)
///     && (lower..upper).contains(&x)
/// ```
///
/// が成り立ち、かつ 2 ^ { count } (y - x) ≒ upper - lower となる `[x, y]` を返します。
///
pub fn binary_search_floating<T: Float>(
    mut lower: T,
    mut upper: T,
    is_upper: impl Fn(T) -> bool,
    count: usize,
) -> [T; 2] {
    debug_assert!(lower < upper);
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

/// [`binary_search_intger`] の引数型のためのトレイトです。全ての整数型に実装されています。
pub trait Int: Add<Output = Self> + Ord + Copy {
    /// 数学的な `floor((self + upper)/2)` と厳密に等しいものを計算します。
    fn midpoint_sorted(self, upper: Self) -> Self;
    /// `1`
    fn one() -> Self;
}

/// [`binary_search_floating`] の引数型のためのトレイトです。全ての整数型に実装されています。
pub trait Float: Add<Output = Self> + Div<Output = Self> + PartialOrd + Copy {
    /// `2`
    fn two() -> Self;
}

macro_rules! impl_int {
    ($(($Unsigned:ty, $Signed:ty),)*) => {$(
        impl Int for $Unsigned {
            fn midpoint_sorted(self, upper: Self) -> Self {
                self + (upper - self) / 2
            }
            fn one() -> Self {
                1
            }
        }
        impl Int for $Signed {
            fn midpoint_sorted(self, upper: Self) -> Self {
                self + ((upper.wrapping_sub(self) as $Unsigned) / 2) as $Signed
            }
            fn one() -> Self {
                1
            }
        }
    )*};
}

impl_int! {
    (u8, i8),
    (u16, i16),
    (u32, i32),
    (u64, i64),
    (u128, i128),
    (usize, isize),
}

macro_rules! impl_float {
    ($($T:ty),*) => {$(
        impl Float for $T {
            fn two() -> Self {
                2.0
            }
        }
    )*};
}

impl_float! { f32, f64 }

#[cfg(test)]
mod tests {
    use crate::{binary_search_floating, binary_search_intger, Float, Int};
    use assert_impl::assert_impl;
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use randtools::NonEmptySubRange;
    use std::ops::Range;

    // すべての整数型は、Int トレイトを実装します。
    #[test]
    fn test_assert_impl_int() {
        assert_impl!(
            Int: u8,
            u16,
            u32,
            u64,
            u128,
            usize,
            i8,
            i16,
            i32,
            i64,
            i128,
            isize,
        );
    }

    // すべての浮動小数点数型は、Float トレイトを実装します。
    #[test]
    fn test_assert_impl_float() {
        assert_impl!(Float: f32, f64);
    }

    // `u8` 型の `midpoint_sorted` が正確に floor ( (x + y) / 2 ) に一致することを、
    // 全探索で確かめます。
    #[test]
    fn test_midpoint_sorted_u8() {
        use std::u8::{MAX, MIN};
        for x in MIN..=MAX {
            for y in x..=MAX {
                let result = Int::midpoint_sorted(x, y);
                let expected = (x as u16 + y as u16).div_euclid(2) as u8;
                assert_eq!(result, expected);
            }
        }
    }

    // `i8` 型の `midpoint_sorted` が正確に floor ( (x + y) / 2 ) に一致することを、
    // 全探索で確かめます。
    #[test]
    fn test_midpoint_sorted_i8() {
        use std::i8::{MAX, MIN};
        for x in MIN..=MAX {
            for y in x..=MAX {
                let result = Int::midpoint_sorted(x, y);
                let expected = (x as i16 + y as i16).div_euclid(2) as i8;
                assert_eq!(result, expected);
            }
        }
    }

    // `usize` 型の `binary_search_intger` が正しく二分探索をすることを、
    // ランダムテストで確かめます。
    #[test]
    fn test_binary_search_integer() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..10_000 {
            let Range { start, end } = rng.sample(NonEmptySubRange(0..std::usize::MAX as usize));
            let lower_bound = rng.gen_range(start + 1..=end);
            let [start, end] = binary_search_intger(start, end, |x| lower_bound <= x);
            assert_eq!(start, lower_bound - 1);
            assert_eq!(end, lower_bound);
        }
    }

    // `usize` 型の `binary_search_floating` が正しく二分探索をすることを、
    // ランダムテストで確かめます。
    #[test]
    fn test_binary_search_floating() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..10_000 {
            const EPS: f64 = 1e-5;
            let start = rng.gen_range(-100.0..=100.0 - 3.0 * EPS);
            let end = rng.gen_range(start + 2.0 * EPS..=100.0);
            let lower_bound = rng.gen_range(start + EPS..=end - EPS);
            let [start, end] = binary_search_floating(start, end, |x| lower_bound <= x, 200);
            assert!(start < lower_bound);
            assert!(lower_bound <= end);
            assert!((end - start) <= EPS);
        }
    }
}
