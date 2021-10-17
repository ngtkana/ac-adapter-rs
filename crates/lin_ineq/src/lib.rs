//! 一次不等式を解きます。
//!
//! CAUTION: [`Interval`] は [`PartialEq`], [`Hash`]
//! を実装していません。なぜなら空区間を表す状態が一意的ではないからです。
//!
//! 関数とのやり取りは、[`Interval`] 型を使います。これは `[T; 2]` の透明なラッパーです。
//! - [`Interval`] 型は [`Mul`],[`Product`] を実装しており、これは [`Interval::intersection`] を呼びだします。
//! - [`full()`](Interval::full), [`contains()`](Interval::contains)
//! といった便利なメソッドがあります。
//!
//! 一次不等式を解く関数には次のものがあります。
//!
//! | お名前            | 愛称      | 形                |
//! | -                 | -         | -                 |
//! | [`solve`]         | 基本形    | ax <= b           |
//! | [`solve_squeeze`] | 挟み撃ち形| l <= ax + b <= r  |
//!
//!
//! # 例
//!
//!
//! ## 基本形 ax <= b
//!
//! ```
//! # use {
//! #     lin_ineq::solve,
//! #     std::i64::MIN,
//! # };
//! let sol = solve(2, 10); // 2x <= 10
//! assert_eq!(sol.0, [MIN, 5]); // x <= 5
//! ```
//!
//! ## 挟み撃ち形 l <= ax + b <= r
//!
//! ```
//! # use {
//! #     lin_ineq::{solve_squeeze, Interval},
//! #     std::i64::MIN,
//! # };
//! let sol = solve_squeeze(3, 1, Interval([-5, 5])); // -5 <= 3x + 1 <= 5
//! assert_eq!(sol.0, [-2, 1]); // -2 <= x <= 1
//! ```
//!

use std::{
    cmp::Ordering,
    fmt::Debug,
    iter::Product,
    ops::{Mul, Neg, Sub},
};

////////////////////////////////////////////////////////////////////////////////
// 整数
////////////////////////////////////////////////////////////////////////////////
/// 符号付き整数です。
pub trait Signed: Sized + Copy + Ord + Neg<Output = Self> + Sub<Output = Self> {
    const MIN: Self;
    const MAX: Self;
    const ZERO: Self;
    fn div_euclid(self, rhs: Self) -> Self;
}
macro_rules! impl_signed {
    ($($T:ident),*) => {$(
        impl Signed for $T {
            const MIN: Self = std::$T::MIN;
            const MAX: Self = std::$T::MAX;
            const ZERO: Self = 0;
            fn div_euclid(self, rhs: Self) -> Self {
                self.div_euclid(rhs)
            }
        }
    )*}
}
impl_signed! { i8, i16, i32, i64, i128, isize }

////////////////////////////////////////////////////////////////////////////////
// 関数
////////////////////////////////////////////////////////////////////////////////
/// 基本形 ax <= b
pub fn solve<T: Signed>(a: T, b: T) -> Interval<T> {
    Interval(match a.cmp(&T::ZERO) {
        Ordering::Greater => [T::MIN, b.div_euclid(a)],
        Ordering::Less => [-b.div_euclid(-a), T::MAX],
        Ordering::Equal => {
            if T::ZERO <= b {
                [T::MIN, T::MAX]
            } else {
                [T::MAX, T::MIN]
            }
        }
    })
}

/// 挟み撃ち形 l <= ax + b <= r
///
/// ただし、`y = Interval([l, r])` とします。
///
///
/// # CAUTION: 空区間について
///
/// 戻り値が空区間であっても、標準形とは限りません。
///
/// ```
/// # use lin_ineq::{solve_squeeze, Interval};
/// let sol = solve_squeeze(3, 0, Interval([1, 2])); // 1 <= 3x <= 2
/// assert_eq!(sol.0, [1, 0]); // 1 <= x <= 0 （標準形でない空区間）
/// ```
pub fn solve_squeeze<T: Signed>(a: T, b: T, y: Interval<T>) -> Interval<T> {
    let Interval(y) = y;
    Interval(if y[0] > y[1] {
        [T::MAX, T::MIN]
    } else {
        match a.cmp(&T::ZERO) {
            Ordering::Greater => [-(b - y[0]).div_euclid(a), (y[1] - b).div_euclid(a)],
            Ordering::Less => [(y[1] - b).div_euclid(a), (b - y[0]).div_euclid(-a)],
            Ordering::Equal => {
                if y[0] <= b && b <= y[1] {
                    [T::MIN, T::MAX]
                } else {
                    [T::MAX, T::MIN]
                }
            }
        }
    })
}

////////////////////////////////////////////////////////////////////////////////
// Interval
////////////////////////////////////////////////////////////////////////////////
/// 閉区間を表す、`[T; 2]` の透明なラッパーです。
///
/// # CAUTION: 空区間について
///
/// 空区間のとき、中身は `l > r` を満たすなかでどれを取っているのかは
/// 保証されていません。それに関連して、
/// - [`PartialEq`], [`Hash`] を実装していません。
/// - [`empty()`](Self::empty) の戻り値は必ず `[MAX, MIN]`（以下、標準形と呼びます。） です。
/// - [`normalize()`](Self::normalize) を使うと空区間はかならず標準形です。
/// - [`intersection()`](Self::intersection) により生じる空区間は標準形とは限りません。
/// と同じ形になります。
///
///
/// # 手動で実装されたトレイトについて
///
/// - [`Debug`](→ [`method.fmt`](struct.Interval.html#method.fmt)) : human readable に出力します。
/// - [`Mul`](→ [`method.mul`](struct.Interval.html#method.mul)) : 交叉を計算します。
/// - [`Product`](→ [`method.product`](struct.Interval.html#method.product)) : 交叉を計算します。
///
#[derive(Clone, Copy)]
pub struct Interval<T>(pub [T; 2]);
impl<T: Signed> Interval<T> {
    /// 表している区間に入っているかどうかを判定します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use lin_ineq::Interval;
    /// assert_eq!(Interval([-10, 10]).contains(-20), false);
    /// assert_eq!(Interval([-10, 10]).contains(-10),  true);
    /// assert_eq!(Interval([-10, 10]).contains(  0),  true);
    /// assert_eq!(Interval([-10, 10]).contains( 10),  true);
    /// assert_eq!(Interval([-10, 10]).contains( 20), false);
    /// ```
    pub fn contains(self, x: T) -> bool {
        (self.0[0]..=self.0[1]).contains(&x)
    }
    /// 区間の交差を計算します。
    ///
    /// 具体的には下限の max と上限の min を計算します。特に、結果が空区間のときに
    /// 戻り値が標準形となるとは限りません。
    ///
    /// # Examples
    ///
    /// ```
    /// # use lin_ineq::Interval;
    /// assert_eq!(Interval([-10, 10]).intersection(Interval([-5, 15])).0, [-5, 10]);
    /// ```
    pub fn intersection(self, rhs: Self) -> Self {
        Self([self.0[0].max(rhs.0[0]), self.0[1].min(rhs.0[1])])
    }
    /// 全区間を返します。具体的には、`[MIN, MAX]` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use lin_ineq::Interval;
    /// # use std::i64::{MIN, MAX};
    /// assert_eq!(Interval::<i64>::full().0, [MIN, MAX]);
    /// ```
    pub fn full() -> Self {
        Self([T::MIN, T::MAX])
    }
    /// 標準形の空区間を返します。具体的には、`[MAX, MIN]` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use lin_ineq::Interval;
    /// # use std::i64::{MIN, MAX};
    /// assert_eq!(Interval::<i64>::empty().0, [MAX, MIN]);
    /// ```
    pub fn empty() -> Self {
        Self([T::MAX, T::MIN])
    }
    /// 空区間であるかどうかを判定します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use lin_ineq::Interval;
    /// assert_eq!(Interval([0,  10]).is_empty(), false);
    /// assert_eq!(Interval([0,   0]).is_empty(), false);
    /// assert_eq!(Interval([0, -10]).is_empty(),  true);
    /// ```
    pub fn is_empty(self) -> bool {
        self.0[0] > self.0[1]
    }
    /// 空区間ならば標準形を、そうでないならばそのまま返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use lin_ineq::Interval;
    /// # use std::i64::{MIN, MAX};
    /// assert_eq!(Interval([0,  10]).normalize().0, [0, 10]);
    /// assert_eq!(Interval([0,   0]).normalize().0, [0,  0]);
    /// assert_eq!(Interval([0, -10]).normalize().0, [MAX, MIN]);
    /// ```
    pub fn normalize(self) -> Self {
        if self.is_empty() {
            Self::empty()
        } else {
            self
        }
    }
}
impl<T: Signed> Mul for Interval<T> {
    type Output = Self;
    /// [`intersection()`](Self::intersection) を呼び出します。
    fn mul(self, rhs: Self) -> Self::Output {
        self.intersection(rhs)
    }
}
impl<'a, T: Signed> Mul<&'a Self> for Interval<T> {
    type Output = Self;
    /// [`intersection()`](Self::intersection) を呼び出します。
    fn mul(self, rhs: &'a Self) -> Self::Output {
        self.intersection(*rhs)
    }
}
impl<'a, T: Signed> Mul<Interval<T>> for &'a Interval<T> {
    type Output = Interval<T>;
    /// [`intersection()`](Interval::intersection) を呼び出します。
    fn mul(self, rhs: Interval<T>) -> Self::Output {
        self.intersection(rhs)
    }
}
impl<'a, T: Signed> Mul for &'a Interval<T> {
    type Output = Interval<T>;
    /// [`intersection()`](Interval::intersection) を呼び出します。
    fn mul(self, rhs: Self) -> Self::Output {
        self.intersection(*rhs)
    }
}
impl<T: Signed> Product for Interval<T> {
    /// [`intersection()`](Self::intersection) で畳み込みます。
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::full(), Self::mul)
    }
}
impl<'a, T: 'a + Signed> Product<&'a Self> for Interval<T> {
    /// [`intersection()`](Self::intersection) で畳み込みます。
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::full(), Self::mul)
    }
}

////////////////////////////////////////////////////////////////////////////////
// Debug
////////////////////////////////////////////////////////////////////////////////
impl<T: Debug + Signed> Debug for Interval<T> {
    /// [`Interval`] 型のオブジェクトを human readable な形でフォーマットします。
    ///
    /// そういうのでなくて中身が見たいんですよという皆様は `self.0` で直接ご覧いただけるとです
    ///
    /// # 仕様
    ///
    /// `self = Interval([l, r])` とすると、
    ///
    /// - `l > r` のとき、`"Empty"`
    /// - そうでないとき、`[l, r]` が
    ///     - `[MIN, MAX]` のとき `"Full"`
    ///     - `[MIN, r]` のとき `"Le(r)"`
    ///     - `[l, MAX]` のとき `"Ge(l)"`
    ///     - `[l, r]` のとき `"Finite(l, r)"`
    ///
    /// とフォーマットします。
    ///
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        #[derive(Debug)]
        enum Human<T> {
            Full,
            Empty,
            Le(T),
            Ge(T),
            Finite(T, T),
        }
        let [l, r] = self.0;
        if l > r {
            Human::Empty
        } else {
            match [l == T::MIN, r == T::MAX] {
                [true, true] => Human::Full,
                [true, false] => Human::Le(r),
                [false, true] => Human::Ge(l),
                [false, false] => Human::Finite(l, r),
            }
        }
        .fmt(f)
    }
}

////////////////////////////////////////////////////////////////////////////////
// テスト
////////////////////////////////////////////////////////////////////////////////
#[cfg(test)]
mod tests {
    use {
        super::{solve, solve_squeeze, Interval, Signed},
        assert_impl::assert_impl,
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::{
            i64::{MAX, MIN},
            iter::repeat_with,
        },
    };

    ////////////////////////////////////////////////////////////////////////////////
    // assert_impl
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_impl() {
        assert_impl!(Signed: i8, i16, i32, i64, i128, isize);
        assert_impl!(!Signed: u8, u16, u32, u64, u128, usize);
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Interval のメソッドのテスト
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_contains() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let a = Interval([rng.gen_range(-9..=9), rng.gen_range(-9..=9)]);
            let x = rng.gen_range(-10..=10);
            assert_eq!(a.contains(x), (a.0[0]..=a.0[1]).contains(&x));
        }
    }

    #[test]
    fn test_intersection() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let a = Interval([rng.gen_range(-9..=9), rng.gen_range(-9..=9)]);
            let b = Interval([rng.gen_range(-9..=9), rng.gen_range(-9..=9)]);
            let c = a.intersection(b);
            for x in -10..=10 {
                assert_eq!(c.contains(x), a.contains(x) && b.contains(x));
            }
        }
    }

    #[test]
    fn test_full() {
        assert_eq!(Interval::<i64>::full().0, [MIN, MAX]);
    }

    #[test]
    fn test_empty() {
        assert_eq!(Interval::<i64>::empty().0, [MAX, MIN]);
    }

    #[test]
    fn test_is_empty() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let a = Interval([rng.gen_range(-9..=9), rng.gen_range(-9..=9)]);
            let expected = (-10..=10).all(|x| !a.contains(x));
            assert_eq!(a.is_empty(), expected);
        }
    }

    #[test]
    fn test_is_normalize() {
        assert_eq!(Interval([3, -3]).0, [3, -3]);
        assert_eq!(Interval([3, -3]).normalize().0, Interval::empty().0);
    }

    #[test]
    fn test_debug() {
        fn debug(x: Interval<i64>) -> String {
            format!("{:?}", x)
        }
        assert_eq!(debug(Interval([0, 2])).as_str(), "Finite(0, 2)");
        assert_eq!(debug(Interval([0, MAX])).as_str(), "Ge(0)");
        assert_eq!(debug(Interval([MIN, 2])).as_str(), "Le(2)");
        assert_eq!(debug(Interval([MIN, MAX])).as_str(), "Full");
        assert_eq!(debug(Interval([MAX, MIN])).as_str(), "Empty");
        assert_eq!(debug(Interval([2, 0])).as_str(), "Empty");
    }

    #[test]
    fn test_product() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(0..10);
            let a = repeat_with(|| Interval([rng.gen_range(-99..=99), rng.gen_range(-99..=99)]))
                .take(n)
                .collect_vec();
            let b = a.iter().product::<Interval<i64>>();
            for x in -10..=10 {
                assert_eq!(b.contains(x), a.iter().all(|a| a.contains(x)));
            }
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // 解く系関数のテスト
    ////////////////////////////////////////////////////////////////////////////////
    #[test]
    fn test_solve() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let a = rng.gen_range(-9..=9);
            let b = rng.gen_range(-9..=9);
            let sol = solve(a, b);
            for x in -200..=200 {
                assert_eq!(sol.contains(x), a * x <= b, "x = {}", x);
            }
        }
    }

    #[test]
    fn test_solve_squeeze() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let a = rng.gen_range(-9..=9);
            let b = rng.gen_range(-9..=9);
            let y_min = rng.gen_range(-100..=100);
            let y_max = rng.gen_range(-100..=100);
            let sol = solve_squeeze(a, b, Interval([y_min, y_max]));
            for x in -200..=200 {
                assert_eq!(
                    sol.contains(x),
                    (y_min..=y_max).contains(&(a * x + b)),
                    "x = {}",
                    x
                )
            }
        }
    }
}
