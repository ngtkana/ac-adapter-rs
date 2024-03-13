//! 黄金分割探索をします。
//!
//! 次の 2 つの関数のお好きな方をどうぞです。
//!
//!
//! # 共通仕様
//!
//! 引数名 `lower`, `upper`
//! は、お名前に反して、別に逆でも動きます。ただ、このセクションでは説明のため `lower <= upper`
//! であるとします。
//!
//!
//! ## Requirements
//!
//! 入力 `lower`, `upper`, `f` は次の要件を満たす必要があります。
//!
//! * （浮動小数点数のときのみ）`lower.is_finite() && upper.is_finite()`
//! * 関数 `f` が区間 [`lower`, `upper`] 内のすべての値でパニックしないこと
//! * 関数 `f` は凸である必要はなく、次を満たす `x` が存在すること
//!     * `f` は区間 [`lower`, `x`] で狭義単調減少
//!     * `f` は区間 [`x`, `upper`] で広義単調増加
//!
//!
//! ## Returns
//!
//! Requirements 内の `x`
//! は唯一なので、それに「そこそこ近いもの」を返します。探索の打ち切りの仕方のバリエーションでいくつかの関数があります。
//!
//! * 浮動小数点数
//!     * 回数指定バージョン: [`gss_by_count`]
//!     * 絶対誤差指定バージョン: [`gss_by_absolute_eps`]
//! * 整数
//!     * 普通バージョン: [`gss_integer`]
//!     * スライス添字バージョン: [`gss_on_slice`]

use std::fmt::Debug;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Sub;

/// スライスの添字バージョン。正確な値を返します。
pub fn gss_on_slice<T: PartialOrd + Debug>(a: &[T]) -> usize {
    assert!(!a.is_empty());
    gss_integer(0, a.len() - 1, |i| &a[i])
}

/// 整数バージョン。正確な値を返します。
pub fn gss_integer<T: Int + Golden, U: PartialOrd + Debug>(
    lower: T,
    upper: T,
    f: impl Fn(T) -> U,
) -> T {
    if lower == upper {
        return lower;
    }
    if lower + T::one() == upper {
        let value_left = f(lower);
        let value_right = f(upper);
        return if value_left <= value_right { lower } else { upper };
    }
    let kv = gss_base(lower, upper, f, |x, y| x != y);
    debug_assert_eq!(kv[0].0 + T::one(), kv[1].0);
    debug_assert_eq!(kv[0].0 + T::one(), kv[2].0);
    debug_assert_eq!(kv[0].0 + T::one() + T::one(), kv[3].0);
    if kv[0].1 <= kv[1].1 {
        kv[0].0
    } else if kv[1].1 <= kv[3].1 {
        kv[1].0
    } else {
        kv[3].0
    }
}

/// 回数指定バージョン。`count` 回イテレートします。
pub fn gss_by_count<T: Float + Golden, U: PartialOrd + Debug>(
    lower: T,
    upper: T,
    f: impl Fn(T) -> U,
    count: usize,
) -> T {
    debug_assert!(lower.is_finite());
    debug_assert!(upper.is_finite());
    let mut i = 0;
    gss_base(lower, upper, f, |_, _| {
        i += 1;
        i != count
    })[1]
        .0
}

/// 絶対誤差指定バージョン。真の答えとの差が `eps` 以内になる保証ができるまでイテレートします。
///
/// # 追加要件
///
/// `T::zero() < eps && eps / lower.abs().max(upper.abs()) != T::zero()`
pub fn gss_by_absolute_eps<T: Float + Golden, U: PartialOrd + Debug>(
    lower: T,
    upper: T,
    f: impl Fn(T) -> U,
    eps: T,
) -> T {
    debug_assert!(lower.is_finite());
    debug_assert!(upper.is_finite());
    debug_assert!(T::zero() < eps && eps / lower.abs().max(upper.abs()) != T::zero());
    let eps = eps * T::INVPHI * T::INVPHI;
    gss_base(lower, upper, f, |x, y| eps < (y - x).abs())[1].0
}

// 黄金分割探索の共通部分
fn gss_base<T: Golden + Debug, U: PartialOrd + Debug>(
    lower: T,
    upper: T,
    f: impl Fn(T) -> U,
    mut continue_condition: impl FnMut(T, T) -> bool,
) -> [(T, U); 4] {
    let left = lower.golden_sect(upper);
    let right = left.golden_sect(upper);
    let mut kv = [
        (lower, f(lower)),
        (left, f(left)),
        (right, f(right)),
        (upper, f(upper)),
    ];
    while continue_condition(kv[1].0, kv[2].0) {
        if kv[1].1 <= kv[2].1 {
            kv.swap(2, 3);
            kv.swap(1, 2);
            kv[1].0 = kv[2].0.golden_sect(kv[0].0);
            kv[1].1 = f(kv[1].0);
        } else {
            kv.swap(0, 1);
            kv.swap(1, 2);
            kv[2].0 = kv[1].0.golden_sect(kv[3].0);
            kv[2].1 = f(kv[2].0);
        }
    }
    kv
}

/// 黄金分割をする関数 [`golden_sect`](Self::golden_sect)
/// を提供します。すべての整数型、浮動小数点型に実装されています。
pub trait Golden:
    Add<Output = Self> + Mul<Output = Self> + Div<Output = Self> + Debug + PartialOrd + Copy
{
    /// `self` と `other` を φ:1 で内分します。整数の場合は近い方に丸めます。
    fn golden_sect(self, other: Self) -> Self;
}

/// [`gss_integer`] の引数型のためのトレイトです。全ての整数型に実装されています。
pub trait Int: Add<Output = Self> + Debug + PartialOrd + Copy {
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
        impl Golden for $Unsigned {
            fn golden_sect(self, other: Self) -> Self {
                Self::f64_as((other.as_f64().mul_add(f64::INVPHI, self.as_f64()) * f64::INVPHI).round())
            }
        }
        impl Golden for $Signed {
            fn golden_sect(self, other: Self) -> Self {
                Self::f64_as((other.as_f64().mul_add(f64::INVPHI, self.as_f64()) * f64::INVPHI).round())
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

/// [`gss_by_count`] の引数型のためのトレイトです。全ての整数型に実装されています。
pub trait Float:
    Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Debug
    + PartialOrd
    + Copy
{
    /// 1 / φ = 0.6180339887498949
    const INVPHI: Self;
    /// 0.0
    fn zero() -> Self;
    /// 2.0
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
            #[allow(clippy::excessive_precision)]
            const INVPHI: Self = 0.618_033_988_749_894_9;
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
        impl Golden for $T {
            fn golden_sect(self, other: Self) -> Self {
                other.mul_add(Self::INVPHI, self) * Self::INVPHI
            }
        }
    )*};
}

impl_float! { f32, f64 }

#[cfg(test)]
mod tests {
    use super::gss_by_absolute_eps;
    use super::gss_by_count;
    use super::gss_integer;
    use super::gss_on_slice;
    use super::Float;
    use super::Golden;
    use super::Int;
    use approx::assert_abs_diff_eq;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use randtools::NonEmptySubRange;
    use std::iter::repeat_with;
    use std::mem::swap;
    use std::ops::Range;
    use test_case::test_case;

    #[test_case(3, 0 => 2)]
    #[test_case(0, 3 => 1)]
    fn test_near_mid(x: u32, y: u32) -> u32 {
        x.golden_sect(y)
    }

    ////////////////////////////////////////////////////////////////////////////////
    // 内部実装
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_golden_sect() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let x0 = rng.gen_range(-10.0..=10.0);
            let x3 = rng.gen_range(-10.0..=10.0);
            let x1 = x0.golden_sect(x3);
            if x0 < x3 {
                assert!(x0 < x1);
                assert!(x1 < x3);
            }
            if x0 > x3 {
                assert!(x0 > x1);
                assert!(x1 > x3);
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // 整数
    ////////////////////////////////////////////////////////////////////////////////

    // 要件を満たすランダムなスライスで黄金分割探索
    #[test]
    fn test_gss_slice() {
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
            println!("a = {:?}", &a);
            let result = gss_on_slice(&a);
            valudate_int(0..n - 1, result, |i| a[i]);
            assert_eq!(expected, result);
        }
    }

    // 二次関数で黄金分割探索
    #[test]
    fn test_gss_quadratic_function() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let Range { start, end } = rng.sample(NonEmptySubRange(0..20));
            let xmin = -10 + start as i32;
            let xmax = -10 + end as i32;
            let a = rng.gen_range(0..=3);
            let b = rng.gen_range(-5..=5);
            let c = rng.gen_range(-30..=30);
            let f = |x: i32| a * x * x + b * x + c;
            let result = gss_integer(xmin, xmax, f);
            validate(xmin..xmax, result, f);
        }
    }

    fn validate<T: Int, U: PartialOrd>(
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

    fn valudate_int<T: Int, U: PartialOrd>(
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
    // 浮動小数点数
    ////////////////////////////////////////////////////////////////////////////////

    // 二次関数で黄金分割探索（回数指定バージョン）
    #[test]
    fn test_gss_quadratic_function_by_count() {
        const EPS: f64 = 1e-5;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let mut start = rng.gen_range(-10.0..=10.0);
            let mut end = rng.gen_range(-10.0..=10.0);
            if start > end {
                swap(&mut start, &mut end);
            }
            let xmin = -10.0 + start;
            let xmax = -10.0 + end;
            let a = rng.gen_range(1.0..=3.0);
            let b = rng.gen_range(-5.0..=5.0);
            let c = rng.gen_range(-30.0..=30.0);
            let f = |x: f64| (a * x).mul_add(x, b * x) + c;
            let count = rng.gen_range(1..2);
            let result = gss_by_count(xmin, xmax, f, count);
            let expected = vec![xmin, -b / (2.0 * a), xmax]
                .into_iter()
                .filter(|&x| (xmin..=xmax).contains(&x))
                .min_by(|&x, &y| f(x).partial_cmp(&f(y)).unwrap())
                .unwrap();
            assert_abs_diff_eq!(
                result,
                expected,
                epsilon = (xmax - xmin).mul_add(f64::INVPHI.powf(count as f64), EPS)
            );
        }
    }

    // 二次関数で黄金分割探索（絶対誤差指定バージョン）
    #[test]
    fn test_gss_quadratic_function_by_absolute_eps() {
        const EPS: f64 = 1e-5;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let mut start: f64 = rng.gen_range(-10.0..=10.0);
            let mut end = rng.gen_range(-10.0..=10.0);
            if start > end {
                swap(&mut start, &mut end);
            }
            let xmin = -10.0 + start;
            let xmax = -10.0 + end;
            let a = rng.gen_range(1.0..=3.0);
            let b = rng.gen_range(-5.0..=5.0);
            let c = rng.gen_range(-30.0..=30.0);
            let f = |x: f64| (a * x).mul_add(x, b * x) + c;
            let eps = rng.gen_range(EPS.ln()..=((xmax - xmin) / 2.0).ln()).exp();
            let result = gss_by_absolute_eps(xmin, xmax, f, eps);
            let expected = vec![xmin, -b / (2.0 * a), xmax]
                .into_iter()
                .filter(|&x| (xmin..=xmax).contains(&x))
                .min_by(|&x, &y| f(x).partial_cmp(&f(y)).unwrap())
                .unwrap();
            assert_abs_diff_eq!(result, expected, epsilon = eps);
        }
    }
}
