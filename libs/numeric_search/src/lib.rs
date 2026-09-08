//! 単調述語 $f$ に対する二分探索・指数探索。整数・浮動小数点数に対応。
//!
//! 探索範囲 $[L, R]$（$\neg f(L) \land f(R)$）が既知なら二分探索で $O(\log(R - L))$ で境界を求める。
//! 範囲が未知の場合は指数探索で $1, 2, 4, \ldots$ と倍々に範囲を広げてから二分探索に切り替えることで、
//! 求める境界までの距離に応じた出力依存の計算量で境界を求める。
//!
//! # 仕様
//!
//! $f$ は単調（ある値を境に `false` から `true` に変わる）であることが前提。
//!
//! - [`binary_search_unsigned`][], [`binary_search_signed`][]: 範囲 $[L, R]$（$\neg f(L) \land f(R)$）が既知の場合に、$\neg f(x-1) \land f(x)$ を満たす $x$ を返す
//! - [`exp_search_unsigned`][], [`exp_search_signed`][]: 範囲が未知の場合。$f$ が恒真でなければ $\neg f(x-1) \land f(x)$ を満たす $x$ を `Some` で返し、恒真なら `None`
//! - [`exp_search_float`][]: 浮動小数点数版。$\neg f(\mathrm{prev}(x)) \land f(x)$（$\mathrm{prev}(x)$ は $x$ の一つ前の浮動小数点数）を満たす正規化数 $x$ を返し、存在しなければ `INFINITY`/`NEG_INFINITY` を返す
//!
//! # 例
//!
//! ```
//! use numeric_search::exp_search_unsigned;
//! assert_eq!(exp_search_unsigned(|x: u32| 6 <= x), Some(6));
//! assert_eq!(exp_search_unsigned(|_: u32| false), None);
//! ```
//!
//! # 計算量
//!
//! - [`binary_search_unsigned`][], [`binary_search_signed`][]: $O(\log(R - L))$
//! - [`exp_search_unsigned`][], [`exp_search_signed`][], [`exp_search_float`][]: 境界までの距離を $d$ として $O(\log d)$

use std::fmt::Debug;
use std::mem::size_of;
use std::ops::Add;
use std::ops::BitAnd;
use std::ops::BitOr;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Shl;
use std::ops::Shr;
use std::ops::Sub;

/// 浮動小数点数を表すトレイト（`f32`, `f64` に実装）。
pub trait Float:
    Sized
    + Copy
    + PartialOrd
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
{
    /// $0$
    const ZERO: Self;
    /// $1$
    const ONE: Self;
    /// $\infty$
    const INFINITY: Self;
    /// $-\infty$
    const NEG_INFINITY: Self;
    /// $x \mapsto \sqrt x$
    fn sqrt(self) -> Self;
}
impl Float for f32 {
    const INFINITY: Self = f32::INFINITY;
    const NEG_INFINITY: Self = f32::NEG_INFINITY;
    const ONE: Self = 1.0;
    const ZERO: Self = 0.0;

    fn sqrt(self) -> Self {
        self.sqrt()
    }
}
impl Float for f64 {
    const INFINITY: Self = f64::INFINITY;
    const NEG_INFINITY: Self = f64::NEG_INFINITY;
    const ONE: Self = 1.0;
    const ZERO: Self = 0.0;

    fn sqrt(self) -> Self {
        self.sqrt()
    }
}

/// 浮動小数点数上で指数探索を行う。
///
/// 単調述語 $f: \mathbb{R} \to \mathrm{bool}$ に対し、$\neg f(\mathrm{prev}(x)) \land f(x)$
/// を満たす正規化数 $x$（$\mathrm{prev}(x)$ は $x$ の一つ前の浮動小数点数）を返す。
/// そのような $x$ が `-T::MAX.sqrt()..=T::MAX.sqrt()` の範囲に存在しなければ
/// `T::INFINITY` または `T::NEG_INFINITY` を返す。
///
/// # 例
///
/// ```
/// # use numeric_search::exp_search_float;
/// assert_eq!(exp_search_float(|x| 2.5 <= x), 2.5);
/// assert_eq!(exp_search_float(|x| -2.5 <= x), -2.5);
/// ```
pub fn exp_search_float<T: Float>(mut f: impl FnMut(T) -> bool) -> T {
    let mut lower;
    let mut upper;
    if f(T::ZERO) {
        if f(-T::ONE) {
            lower = -T::ONE - T::ONE;
            upper = -T::ONE;
            while f(lower) {
                upper = lower;
                lower = -lower * lower;
                if lower == T::NEG_INFINITY {
                    return T::NEG_INFINITY;
                }
            }
        } else {
            lower = -T::ONE;
            upper = -T::ONE / (T::ONE + T::ONE);
            while !f(upper) {
                lower = upper;
                upper = -upper * upper;
                if upper == T::ZERO {
                    return T::ZERO;
                }
            }
        }
        while lower < upper + upper {
            let mid = lower * (upper / lower).sqrt();
            if f(mid) {
                upper = mid;
            } else {
                lower = mid;
            }
        }
        debug_assert_eq!(lower, upper + upper);
    } else {
        if f(T::ONE) {
            lower = T::ONE / (T::ONE + T::ONE);
            upper = T::ONE;
            while f(lower) {
                upper = lower;
                lower = lower * lower;
            }
        } else {
            lower = T::ONE;
            upper = T::ONE + T::ONE;
            while !f(upper) {
                lower = upper;
                upper = upper * upper;
                if upper == T::INFINITY {
                    return T::INFINITY;
                }
            }
        }
        while lower + lower < upper {
            let mid = lower * (upper / lower).sqrt();
            if f(mid) {
                upper = mid;
            } else {
                lower = mid;
            }
        }
        debug_assert_eq!(lower + lower, upper);
    }
    loop {
        let mid = lower + (upper - lower) / (T::ONE + T::ONE);
        if lower == mid || mid == upper {
            return upper;
        }
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
}

/// 符号なし整数を表すトレイト。
pub trait Unsigned:
    Sized
    + Copy
    + PartialOrd
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Shr<usize, Output = Self>
    + Shl<usize, Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
{
    /// $0$
    const ZERO: Self;
    /// $1$
    const ONE: Self;
}
macro_rules! impl_unsigned {
    ($($ty:ty),*) => {$(
        impl Unsigned for $ty {
            const ZERO: Self = 0;
            const ONE: Self = 1;
        }
    )*};
}
impl_unsigned! { u8, u16, u32, u64, u128, usize }

/// 符号なし整数上で指数探索を行う。
///
/// 単調述語 $f: \mathbb{N} \to \mathrm{bool}$（$f$ は恒真でない）に対し、
/// $\neg f(x-1) \land f(x)$ を満たす $x$ を `Some` で返す（$f(-1)$ は `false` とみなす）。
/// $f$ が恒真の場合は `None` を返す。
///
/// # 例
///
/// ```
/// # use numeric_search::exp_search_unsigned;
/// assert_eq!(exp_search_unsigned(|x: u32| 6 <= x), Some(6));
/// assert_eq!(exp_search_unsigned(|_: u32| false), None);
/// assert_eq!(exp_search_unsigned(|_: u32| true), Some(0));
/// ```
pub fn exp_search_unsigned<T: Unsigned>(mut f: impl FnMut(T) -> bool) -> Option<T> {
    if f(T::ZERO) {
        return Some(T::ZERO);
    }
    let mut lower = T::ZERO;
    let mut upper = T::ONE;
    while !f(upper) {
        lower = upper;
        if upper >> (size_of::<T>() * 8 - 1) & T::ONE == T::ZERO {
            upper = upper + upper;
        } else if upper & T::ONE == T::ONE {
            return None;
        } else {
            upper = upper >> 1 | T::ONE << (size_of::<T>() * 8 - 1);
        }
    }
    Some(binary_search_unsigned(lower, upper, f))
}

/// 符号なし整数上で二分探索を行う。
///
/// 単調述語 $f: [L, R] \to \mathrm{bool}$（$\neg f(L) \land f(R)$）に対し、
/// $\neg f(x-1) \land f(x)$ を満たす $x \in [L, R]$ を返す。
///
/// # 例
///
/// ```
/// # use numeric_search::binary_search_unsigned;
/// assert_eq!(binary_search_unsigned(10_u32, 20, |x| 200 <= x * x), 15);
/// ```
pub fn binary_search_unsigned<T: Unsigned>(
    mut lower: T,
    mut upper: T,
    mut f: impl FnMut(T) -> bool,
) -> T {
    assert!(lower < upper);
    assert!(!f(lower) && f(upper));
    while lower + T::ONE != upper {
        let mid = lower + (upper - lower) / (T::ONE + T::ONE);
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
    upper
}

/// 符号付き整数を表すトレイト。
pub trait Signed:
    Sized
    + Copy
    + PartialOrd
    + Debug
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Neg<Output = Self>
    + Shr<usize, Output = Self>
    + Shl<usize, Output = Self>
    + BitAnd<Output = Self>
    + BitOr<Output = Self>
{
    const ZERO: Self;
    const ONE: Self;
    const MIN: Self;
    const MAX: Self;
}
macro_rules! impl_signed {
    ($($ty:ident),*) => {$(
        impl Signed for $ty {
            const ZERO: Self = 0;
            const ONE: Self = 1;
            const MIN: Self = $ty::MIN;
            const MAX: Self = $ty::MAX;
        }
    )*};
}
impl_signed! { i8, i16, i32, i64, i128 }

/// 符号付き整数上で指数探索を行う。
///
/// 単調述語 $f: \mathbb{Z} \to \mathrm{bool}$（$f$ は恒真でない）に対し、
/// $\neg f(x-1) \land f(x)$ を満たす $x$ を `Some` で返す（$f(\mathtt{MIN}-1)$ は `false` とみなす）。
/// $f$ が恒真の場合は `None` を返す。
///
/// # 例
///
/// ```
/// # use numeric_search::exp_search_signed;
/// assert_eq!(exp_search_signed(|x| 6 <= x), Some(6));
/// assert_eq!(exp_search_signed(|_: i32| false), None);
/// assert_eq!(exp_search_signed(|_: i32| true), Some(i32::MIN));
/// ```
pub fn exp_search_signed<T: Signed>(mut f: impl FnMut(T) -> bool) -> Option<T> {
    let mut lower;
    let mut upper;
    if f(T::ZERO) {
        lower = -T::ONE;
        upper = T::ZERO;
        while f(lower) {
            upper = lower;
            if lower == T::MIN {
                return Some(T::MIN);
            }
            lower = lower + lower;
        }
    } else {
        lower = T::ZERO;
        upper = T::ONE;
        while !f(upper) {
            lower = upper;
            if upper >> (size_of::<T>() * 8 - 2) & T::ONE == T::ZERO {
                upper = upper + upper;
            } else if upper == T::MAX {
                return None;
            } else {
                upper = upper >> 1 | T::ONE << (size_of::<T>() * 8 - 2);
            }
        }
    }
    while lower + T::ONE != upper {
        let mid = lower + (upper - lower) / (T::ONE + T::ONE);
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
    Some(upper)
}

/// 符号付き整数上で二分探索を行う。
///
/// 単調述語 $f: [L, R] \to \mathrm{bool}$（$\neg f(L) \land f(R)$）に対し、
/// $\neg f(x-1) \land f(x)$ を満たす $x \in [L, R]$ を返す。
///
/// # 例
///
/// ```
/// # use numeric_search::binary_search_signed;
/// assert_eq!(binary_search_signed(-10_i32, 20, |x| 5 <= x), 5);
/// ```
pub fn binary_search_signed<T: Signed>(
    mut lower: T,
    mut upper: T,
    mut f: impl FnMut(T) -> bool,
) -> T {
    assert!(lower < upper);
    assert!(!f(lower) && f(upper));
    while lower + T::ONE != upper {
        let mid = if lower <= T::ZERO && T::ZERO <= upper {
            (lower + upper) / (T::ONE + T::ONE)
        } else {
            lower + (upper - lower) / (T::ONE + T::ONE)
        };
        if f(mid) {
            upper = mid;
        } else {
            lower = mid;
        }
    }
    upper
}

#[cfg(test)]
mod tests {
    #![allow(clippy::float_cmp)]
    use super::*;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::HashMap;
    use std::mem::swap;

    #[test]
    fn test_exponential_search_f64() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let expected: f64 = if rng.gen_bool(0.5) { 1.0 } else { -1.0 }
                * 2_f64.powf(rng.gen_range(-512.0..512.0));
            let mut count = 0;
            let result = exp_search_float(|x| {
                count += 1;
                expected <= x
            });
            assert!(count <= 72);
            assert_eq!(result, expected);
        }

        for &(threshold, expected) in &[
            // Succeeds
            (0.0, 0.0),
            (-0.0, 0.0),
            (f64::INFINITY, f64::INFINITY),
            (f64::NEG_INFINITY, f64::NEG_INFINITY),
            (f64::EPSILON, f64::EPSILON),
            (f64::MAX.sqrt(), f64::MAX.sqrt()),
            (-f64::MAX.sqrt(), -f64::MAX.sqrt()),
            (f64::MIN_POSITIVE, f64::MIN_POSITIVE),
            (-f64::MIN_POSITIVE, -f64::MIN_POSITIVE),
            // Fails
            (f64::MAX.sqrt() * 1.000_000_000_001, f64::INFINITY),
            (-f64::MAX.sqrt() * 1.000_000_000_001, f64::NEG_INFINITY),
        ] {
            let result = exp_search_float(|x| threshold <= x);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_exponential_search_f32() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let expected: f32 =
                if rng.gen_bool(0.5) { 1.0 } else { -1.0 } * 2_f32.powf(rng.gen_range(-63.0..63.0));
            let mut count = 0;
            let result = exp_search_float(|x| {
                count += 1;
                expected <= x
            });
            assert!(count <= 72);
            assert_eq!(result, expected);
        }

        for &(threshold, expected) in &[
            // Succeeds
            (0.0, 0.0),
            (-0.0, 0.0),
            (f32::INFINITY, f32::INFINITY),
            (f32::NEG_INFINITY, f32::NEG_INFINITY),
            (f32::EPSILON, f32::EPSILON),
            (f32::MAX.sqrt(), f32::MAX.sqrt()),
            (-f32::MAX.sqrt(), -f32::MAX.sqrt()),
            (f32::MIN_POSITIVE, f32::MIN_POSITIVE),
            (-f32::MIN_POSITIVE, -f32::MIN_POSITIVE),
            // Fails
            (f32::MAX.sqrt() * 1.000_001, f32::INFINITY),
            (-f32::MAX.sqrt() * 1.000_001, f32::NEG_INFINITY),
        ] {
            let result = exp_search_float(|x| threshold <= x);
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_exponential_search_u8() {
        for expected in 0..=255_u8 {
            let result = exp_search_unsigned(|x| expected <= x);
            assert_eq!(result, Some(expected));
        }
        let result = exp_search_unsigned(|_| false);
        assert_eq!(result, None::<u8>);
    }

    #[test]
    fn test_binary_search_u8() {
        for expected in 1..=255_u8 {
            let result = binary_search_unsigned(0, 255, |x| expected <= x);
            assert_eq!(result, expected);
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let mut lower = rng.gen_range(0..255);
            let mut upper = rng.gen_range(0..=255);
            if lower >= upper {
                swap(&mut lower, &mut upper);
                upper += 1;
            }
            let mut memo = HashMap::<u8, bool>::from_iter(vec![(lower, false), (upper, true)]);
            let f = |x| *memo.entry(x).or_insert_with(|| rng.gen_bool(0.5));
            let result = binary_search_unsigned(lower, upper, f);
            assert!((lower + 1..=upper).contains(&result));
            assert!(memo[&result]);
            assert!(!memo[&(result - 1)]);
        }
    }

    #[test]
    fn test_exponential_search_i8() {
        for expected in -128..=127_i8 {
            let result = exp_search_signed(|x| expected <= x);
            assert_eq!(result, Some(expected));
        }
        let result = exp_search_signed(|_| false);
        assert_eq!(result, None::<i8>);
    }

    #[test]
    fn test_binary_search_i8() {
        for expected in -127..=127_i8 {
            let result = binary_search_signed(-128, 127, |x| expected <= x);
            assert_eq!(result, expected);
        }

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let mut lower = rng.gen_range(-128..127);
            let mut upper = rng.gen_range(-128..=127);
            if lower >= upper {
                swap(&mut lower, &mut upper);
                upper += 1;
            }
            let mut memo = HashMap::<i8, bool>::from_iter(vec![(lower, false), (upper, true)]);
            let f = |x| *memo.entry(x).or_insert_with(|| rng.gen_bool(0.5));
            let result = binary_search_signed(lower, upper, f);
            assert!((lower + 1..=upper).contains(&result));
            assert!(memo[&result]);
            assert!(!memo[&(result - 1)]);
        }
    }
}
