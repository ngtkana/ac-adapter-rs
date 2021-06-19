//! 黄金分割探索をします。
//!
//! 次の 2 つの関数のお好きな方をどうぞです。
//!
//! * 関数で射影: [`golden_section_search_integer`]
//! * スライスで射影: [`golden_section_search_slice`]
//!
//!
//! # Examples
//!
//! 配列 `a` の argmin を探します。詳しい仕様は [`golden_section_search_integer`] をご覧ください。
//!
//! ```
//! use golden_section_search::golden_section_search_slice;
//!
//! let a = [9, 6, 5, 2, 0, 0, 4, 6, 6, 9];
//! let result = golden_section_search_slice(&a);
//! let expected = 4;
//! assert_eq!(result, expected);
//! ```
//!
//!
//! # Tutorial
//!
//! これの `i` を返します。
//!
//! ```[ignore]
//!                   i
//!  greater or eqal  │    less
//!                   │
//! ┌───┬───┬───┬───┬───┬───┬───┬───┬───┬───┐
//! │ 9 │ 6 │ 5 │ 2 │ 0 │ 0 │ 4 │ 6 │ 6 │ 9 │
//! └───┴───┴───┴───┴───┴───┴───┴───┴───┴───┘
//! ```
//!
//!
//! [`golden_section_search_integer`] では [`Ord`] を要求していますが、実際には `less`
//! が推移的であるだけで大丈夫です
//!
//!

use std::{fmt::Debug, ops::Add};

const INVPHI: f64 = 0.61803398874989484820458683436563811772030917980576286213545;

/// スライス上で黄金分割探索をします。細かい仕様は [`golden_section_search_integer`] と同じです。
pub fn golden_section_search_slice<T: Ord>(a: &[T]) -> usize {
    assert!(!a.is_empty());
    golden_section_search_integer(0, a.len() - 1, |i| &a[i])
}

/// 関数により黄金分割探索をします。
///
/// # Requirements
///
/// * `lower <= upper`
/// * `lower..=upper` 内の任意の `j` に対して、`f(j)` がパニックしない
/// * 次をみたす `i` が存在する
///
/// ```[ignore]
/// (lower..upper).contains(&i)
///     && (lower..i).all(|j| f(j) > f(j + 1))
///     && (i..upper).all(|j| f(j) <= f(j + 1))
/// ```
///
///
/// # Returns
///
/// Requirements 内で定義された `i` は、唯一なので、これを返します。
///
pub fn golden_section_search_integer<T: Int, U: Ord>(lower: T, upper: T, f: impl Fn(T) -> U) -> T {
    debug_assert!(lower <= upper);
    if lower == upper {
        return lower;
    }
    if lower + T::one() == upper {
        let value_left = f(lower);
        let value_right = f(upper);
        return if value_left <= value_right {
            lower
        } else {
            upper
        };
    }
    let mut keys = interpolate_init([lower, upper]);
    let mut values = [f(keys[0]), f(keys[1]), f(keys[2]), f(keys[3])];
    while keys[1] < keys[2] {
        if values[1] <= values[2] {
            interpolate_left_integer(&mut keys);
            values[1..].rotate_right(1);
            values[1] = f(keys[1]);
        } else {
            interpolate_right_integer(&mut keys);
            values[..=2].rotate_left(1);
            values[2] = f(keys[2]);
        }
    }
    debug_assert_eq!(keys[0] + T::one(), keys[1]);
    debug_assert_eq!(keys[0] + T::one(), keys[2]);
    debug_assert_eq!(keys[0] + T::one() + T::one(), keys[3]);
    if values[0] <= values[1] {
        keys[0]
    } else if values[1] <= values[3] {
        keys[1]
    } else {
        keys[3]
    }
}

/// [`golden_section_search_integer`] の引数型のためのトレイトです。全ての整数型に実装されています。
pub trait Int: Add<Output = Self> + Debug + Ord + Copy {
    /// 数学的な `floor((self + upper)/2)` と厳密に等しいものを計算します。
    fn midpoint_sorted(self, upper: Self) -> Self;
    /// `1`
    fn one() -> Self;
    fn as_f64(self) -> f64;
    fn f64_as(x: f64) -> Self;
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
            fn as_f64(self) -> f64 {
                self as f64
            }
            fn f64_as(x: f64) -> Self {
                x as $Unsigned
            }
        }
        impl Int for $Signed {
            fn midpoint_sorted(self, upper: Self) -> Self {
                self + ((upper.wrapping_sub(self) as $Unsigned) / 2) as $Signed
            }
            fn one() -> Self {
                1
            }
            fn as_f64(self) -> f64 {
                self as f64
            }
            fn f64_as(x: f64) -> Self {
                x as $Signed
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

fn interpolate_init<T: Int>(keys: [T; 2]) -> [T; 4] {
    let x = T::f64_as(((keys[0].as_f64() + keys[1].as_f64() * INVPHI) * INVPHI).round());
    let y = T::f64_as(((x.as_f64() + keys[1].as_f64() * INVPHI) * INVPHI).round());
    [keys[0], x, y, keys[1]]
}

fn interpolate_left_integer<T: Int>(keys: &mut [T; 4]) {
    keys[3] = keys[2];
    keys[2] = keys[1];
    keys[1] = T::f64_as((((keys[0].as_f64() * INVPHI) + keys[1].as_f64()) * INVPHI).round());
}

fn interpolate_right_integer<T: Int>(keys: &mut [T; 4]) {
    debug_assert!(keys[0] < keys[1]);
    debug_assert!(keys[1] < keys[2]);
    debug_assert!(keys[2] < keys[3]);
    keys[0] = keys[1];
    keys[1] = keys[2];
    keys[2] = T::f64_as((((keys[3].as_f64() * INVPHI) + keys[2].as_f64()) * INVPHI).round());
}

#[cfg(test)]
mod tests {
    use {
        super::{
            golden_section_search_integer, golden_section_search_slice, interpolate_init,
            interpolate_left_integer, interpolate_right_integer, Int,
        },
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::NonEmptySubRange,
        std::{iter::repeat_with, ops::Range},
        test_case::test_case,
    };

    ////////////////////////////////////////////////////////////////////////////////
    // 探索のテスト
    ////////////////////////////////////////////////////////////////////////////////

    // 要件を満たすランダムなスライスで黄金分割探索
    #[test]
    fn test_golden_section_search_slice() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=5);
            let expected = rng.gen_range(0..n);
            let left1 = repeat_with(|| rng.gen_range(1..=10))
                .take(expected)
                .collect::<Vec<_>>();
            let right1 = repeat_with(|| rng.gen_range(0..10))
                .take(n - 1 - expected)
                .collect::<Vec<_>>();
            let mut a = vec![0; n];
            a[expected] = 0;
            for (i, &x) in left1.iter().enumerate() {
                a[expected - i - 1] = a[expected - i] + x;
            }
            for (i, &x) in right1.iter().enumerate() {
                a[expected + i + 1] = a[expected + i] + x;
            }
            let result = golden_section_search_slice(&a);
            validate(0..n - 1, result, |i| a[i]);
            assert_eq!(expected, result);
        }
    }

    // 短いスライスで黄金分割探索
    #[test]
    fn test_golden_section_search_small_slice() {
        // one
        {
            let result = golden_section_search_slice(&[0]);
            let expected = 0;
            assert_eq!(result, expected);
        }
        // two
        for x in 0..2 {
            for y in 0..2 {
                let result = golden_section_search_slice(&[x, y]);
                let expected = if x <= y { 0 } else { 1 };
                assert_eq!(result, expected);
            }
        }
    }

    // 二次関数で黄金分割探索
    #[test]
    fn test_golden_section_search_quadratic_function() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let Range { start, end } = rng.sample(NonEmptySubRange(0..20));
            let xmin = -10 + start as i32;
            let xmax = -10 + end as i32;
            let a = rng.gen_range(0..=3);
            let b = rng.gen_range(-5..=5);
            let c = rng.gen_range(-30..=30);
            let f = |x: i32| a * x * x + b * x + c;
            let result = golden_section_search_integer(xmin, xmax, f);
            let expected = (xmin..xmax).find(|&i| f(i) <= f(i + 1)).unwrap_or(xmax);
            assert_eq!(result, expected);
            validate(xmin..xmax, result, f);
        }
    }

    fn validate<T: Int, U: Ord>(
        lower_upper_minus_one: impl IntoIterator<Item = T>,
        result: T,
        f: impl Fn(T) -> U,
    ) {
        assert!(lower_upper_minus_one.into_iter().all(|i| {
            if i < result {
                f(i) > f(i + T::one())
            } else {
                f(i) <= f(i + T::one())
            }
        }));
    }

    ////////////////////////////////////////////////////////////////////////////////
    // 内部実装のテスト
    ////////////////////////////////////////////////////////////////////////////////

    // 状態フィボナッチのときに次もフィボナッチになっていること
    #[test]
    fn test_interpolate_fibonacci() {
        const FIBONACCI_LEN: usize = 10;
        const FIBONACCI: [u32; FIBONACCI_LEN] = [1, 1, 2, 3, 5, 8, 13, 21, 34, 55];
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..5 {
            for fib in FIBONACCI.windows(4) {
                let start = rng.gen_range(0..100);
                let keys = interpolate_init([start, start + fib[3]]);
                assert_eq!(
                    keys,
                    [start, start + fib[1], start + fib[2], start + fib[3]]
                );
                {
                    let mut keys = keys;
                    interpolate_left_integer(&mut keys);
                    assert_eq!(
                        keys,
                        [start, start + fib[0], start + fib[1], start + fib[2]]
                    );
                }
                {
                    let mut keys = keys;
                    interpolate_right_integer(&mut keys);
                    assert_eq!(
                        keys,
                        [
                            start + fib[1],
                            start + fib[1] + fib[0],
                            start + fib[1] + fib[1],
                            start + fib[1] + fib[2]
                        ]
                    );
                }
            }
        }
    }

    // 状態の初期化の結果の、小さい場合
    #[test_case(1 => [0, 0, 0, 1])]
    #[test_case(2 => [0, 1, 1, 2])]
    #[test_case(3 => [0, 1, 2, 3])]
    #[test_case(4 => [0, 2, 3, 4])]
    #[test_case(5 => [0, 2, 3, 5])]
    #[test_case(6 => [0, 2, 4, 6])]
    #[test_case(7 => [0, 3, 5, 7])]
    #[test_case(8 => [0, 3, 5, 8])]
    #[test_case(9 => [0, 3, 5, 9])]
    #[test_case(10 => [0, 4, 6, 10])]
    #[test_case(11 => [0, 4, 7, 11])]
    #[test_case(12 => [0, 5, 8, 12])]
    #[test_case(13 => [0, 5, 8, 13])]
    fn test_interpolate_init_small(width: u32) -> [u32; 4] {
        interpolate_init([0, width])
    }

    // ランダムに状態遷移して、最終状態が [0, 1, 1, 2] みたいになっていること
    #[test]
    fn test_repeated_interpolate() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            for width in 3..=20 {
                let start = rng.gen_range(0..100);
                let end = start + width;
                let mut keys = interpolate_init([start, end]);
                while keys[1] < keys[2] {
                    if rng.gen_ratio(1, 2) {
                        interpolate_left_integer(&mut keys);
                    } else {
                        interpolate_right_integer(&mut keys);
                    }
                }
                assert_eq!(keys[0] + 1, keys[1]);
                assert_eq!(keys[0] + 1, keys[2]);
                assert_eq!(keys[0] + 2, keys[3]);
            }
        }
    }
}
