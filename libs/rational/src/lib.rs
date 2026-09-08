//! 符号付き整数を分子・分母とする既約有理数 $\frac{p}{q}$ の四則演算・比較・パース。
//!
//! `Rational<T>` は常に既約な状態（分子・分母が互いに素、分母が正）を保つ。
//! 構築時とすべての演算結果で分子・分母の $\gcd$ を取って約分し、符号を分母側に正規化する。
//! この不変条件のおかげで、等号・大小比較は通分せず交差乗算 $ad$ と $bc$ の比較だけで判定できる。
//!
//! # 仕様
//!
//! - 型: `Rational<T>`（`T` は [`Signed`] を実装する符号付き整数。標準では `i8`〜`i128`, `isize`）
//! - 生成: [`Rational::new`]`(num, den)`: $\mathrm{den} \neq 0$ が前提、既約分数に正規化
//! - パース: `"p/q"` または `"p"`（分母省略時は $1$）を [`FromStr`] で読み込み
//! - 演算: `+`, `-`, `*`, `/`（$0$ 除算は panic）, 単項 `-`, [`Sum`], [`Product`]
//! - 比較: `==`, `<`, `>` など（[`Ord`] を実装）
//! - 変換: [`Rational::decompose`] で `[分子, 分母]`、[`Rational::into_f64`] で近似値
//!
//! # 例
//!
//! ```
//! use rational::Rational;
//!
//! let x = Rational::new(2, 4);
//! assert_eq!(x.decompose(), [1, 2]); // 2/4 は 1/2 に約分
//!
//! let y: Rational<i32> = "1/3".parse().unwrap();
//! assert_eq!(x + y, Rational::new(5, 6)); // 1/2 + 1/3 = 5/6
//! assert!(y < x); // 1/3 < 1/2
//! ```
//!
//! # 計算量
//!
//! - 各演算（`+`, `-`, `*`, `/`, 比較, パース）: $O(\log(\min(|p|, |q|)))$（$\gcd$ 計算が支配的）

use std::cmp::Ord;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::hash::Hash;
use std::iter::Product;
use std::iter::Sum;
use std::mem::swap;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::RemAssign;
use std::ops::Sub;
use std::ops::SubAssign;
use std::str::FromStr;

/// 既約有理数 $\frac{p}{q}$（$T$ は符号付き整数）。
///
/// 分子・分母は常に約分済みで、分母は正に正規化されている。
///
/// # 例
///
/// ```
/// use rational::Rational;
///
/// let x = Rational::new(3, 6);
/// assert_eq!(x.decompose(), [1, 2]); // 3/6 = 1/2
/// ```
#[derive(Clone, Default, Copy)]
pub struct Rational<T: Signed>(T, T);
impl<T: Signed> Rational<T> {
    /// 分子 `num`, 分母 `den` から既約有理数を構築する。
    ///
    /// $g = \gcd(|\mathrm{num}|, |\mathrm{den}|)$ で約分し、符号を分母側に集約して分母を正にする。
    /// 以降の比較・演算はこの正規化（分母が正）に依存する。
    ///
    /// # 仕様
    ///
    /// - `den` $= 0$ のとき panic
    ///
    /// # 例
    ///
    /// ```
    /// use rational::Rational;
    ///
    /// assert_eq!(Rational::new(2, 4), Rational::new(-1, -2)); // どちらも 1/2 に正規化
    /// assert_eq!(Rational::new(1, -2).decompose(), [-1, 2]); // 符号は分子に集約
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(\log(\min(|\mathrm{num}|, |\mathrm{den}|)))$
    pub fn new(num: T, den: T) -> Self {
        assert_ne!(den, T::zero(), "分母 0 はだめです。: {:?}/{:?}", &num, &den);
        let g = gcd(num, den).generic_abs() * den.generic_signum();
        Self(num / g, den / g)
    }

    /// 既約分数の `[分子, 分母]` を返す。分母は正。
    ///
    /// # 例
    ///
    /// ```
    /// use rational::Rational;
    ///
    /// assert_eq!(Rational::new(4, 6).decompose(), [2, 3]);
    /// ```
    pub fn decompose(self) -> [T; 2] {
        [self.0, self.1]
    }

    /// $f64$ 近似値 $\mathrm{num} / \mathrm{den}$ を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use rational::Rational;
    ///
    /// assert_eq!(Rational::new(1, 4).into_f64(), 0.25);
    /// ```
    pub fn into_f64(self) -> f64
    where
        f64: From<T>,
    {
        f64::from(self.0) / f64::from(self.1)
    }
}
/// 交差乗算 $ad = bc$ で等価性を判定する（$\mathrm{self} = a/b$, $\mathrm{other} = c/d$）。
///
/// 分母が常に正に正規化されているため、通分せずこの判定だけで等価性が定まる。
impl<T: Signed> PartialEq for Rational<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 * other.1 == self.1 * other.0
    }
}
/// [`PartialEq`] が全順序と整合する同値関係であることを示すマーカー実装。
impl<T: Signed> Eq for Rational<T> {}
/// 交差乗算 $ad$ と $bc$ の比較で大小を判定する（$\mathrm{self} = a/b$, $\mathrm{other} = c/d$）。
///
/// 分母が常に正なので、符号反転の補正なしに交差乗算の比較がそのまま大小関係になる。
impl<T: Signed> Ord for Rational<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0 * other.1).cmp(&(self.1 * other.0))
    }
}
/// [`Ord::cmp`] の結果をそのまま返す。
impl<T: Signed> PartialOrd for Rational<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
/// 分母が $1$ なら `"num"`、そうでなければ `"num/den"` の形式で表示する。
///
/// # 例
///
/// ```
/// use rational::Rational;
///
/// assert_eq!(format!("{:?}", Rational::new(4, 2)), "2");
/// assert_eq!(format!("{:?}", Rational::new(1, 2)), "1/2");
/// ```
impl<T: Signed> Debug for Rational<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.1 == T::one() {
            write!(f, "{:?}", self.0)
        } else {
            write!(f, "{:?}/{:?}", self.0, self.1)
        }
    }
}
/// `"p/q"` または `"p"`（分母省略時は $1$）の形式の文字列をパースする。
///
/// # 仕様
///
/// - 空文字列は panic
/// - `"/"` が 2 個以上ある文字列は panic
/// - 分子・分母それぞれの数値パースに失敗した場合は `T::Err` を返す
///
/// # 例
///
/// ```
/// use rational::Rational;
///
/// let x: Rational<i32> = "3/6".parse().unwrap();
/// assert_eq!(x, Rational::new(1, 2));
///
/// let y: Rational<i32> = "5".parse().unwrap();
/// assert_eq!(y, Rational::new(5, 1));
/// ```
impl<T: Signed> FromStr for Rational<T> {
    type Err = T::Err;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut s = s.split('/');
        let num = match s.next() {
            None => panic!("空文字列は Rational 型にパースできません。"),
            Some(x) => x.parse::<T>()?,
        };
        let den = match s.next() {
            None => T::one(),
            Some(x) => x.parse()?,
        };
        assert!(
            s.next().is_none(),
            "\"/\" が 2 つ以上ある文字列は Rational にパースできません。"
        );
        Ok(Self::new(num, den))
    }
}
/// $\frac{a}{b} + \frac{c}{d} = \frac{ad + bc}{bd}$ を計算し、既約分数に正規化する。
impl<T: Signed> AddAssign for Rational<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = Self::new(self.0 * rhs.1 + self.1 * rhs.0, self.1 * rhs.1);
    }
}
/// $\frac{a}{b} - \frac{c}{d} = \frac{ad - bc}{bd}$ を計算し、既約分数に正規化する。
impl<T: Signed> SubAssign for Rational<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = Self::new(self.0 * rhs.1 - self.1 * rhs.0, self.1 * rhs.1);
    }
}
/// $\frac{a}{b} \times \frac{c}{d} = \frac{ac}{bd}$ を計算し、既約分数に正規化する。
impl<T: Signed> MulAssign for Rational<T> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = Self::new(self.0 * rhs.0, self.1 * rhs.1);
    }
}
/// $\frac{a}{b} \div \frac{c}{d} = \frac{ad}{bc}$ を計算し、既約分数に正規化する。
///
/// # 仕様
///
/// - `rhs` の分子が $0$（すなわち `rhs` $= 0$）のとき panic
impl<T: Signed> DivAssign for Rational<T> {
    fn div_assign(&mut self, rhs: Self) {
        assert_ne!(
            rhs.0,
            T::zero(),
            "有理数の 0 除算はだめです。: self = {self:?}, rhs = {rhs:?}"
        );
        *self = Self::new(self.0 * rhs.1, self.1 * rhs.0);
    }
}
/// $-\frac{a}{b} = \frac{-a}{b}$ を返す。
impl<T: Signed> Neg for Rational<T> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0, self.1)
    }
}
/// $0$ を単位元として畳み込み和を計算する。
impl<T: Signed> Sum for Rational<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self(T::zero(), T::one()), Add::add)
    }
}
/// $1$ を単位元として畳み込み積を計算する。
impl<T: Signed> Product for Rational<T> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self(T::one(), T::one()), Mul::mul)
    }
}
/// $0$ を単位元として畳み込み和を計算する（参照イテレータ版）。
impl<'a, T: 'a + Signed> Sum<&'a Self> for Rational<T> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self(T::zero(), T::one()), Add::add)
    }
}
/// $1$ を単位元として畳み込み積を計算する（参照イテレータ版）。
impl<'a, T: 'a + Signed> Product<&'a Self> for Rational<T> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self(T::one(), T::one()), Mul::mul)
    }
}

/// [`Rational`] の分子・分母として使える符号付き整数を表すトレイト。
///
/// 標準では `i8`, `i16`, `i32`, `i64`, `i128`, `isize` に実装済み。
pub trait Signed:
    Sized
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + Rem<Output = Self>
    + RemAssign
    + Neg<Output = Self>
    + FromStr
    + Debug
    + Copy
    + Clone
    + Hash
    + PartialEq
    + Eq
    + PartialOrd
    + Ord
{
    /// 加法単位元 $0$。
    fn zero() -> Self;
    /// 乗法単位元 $1$。
    fn one() -> Self;
    /// 絶対値 $|x|$。
    fn generic_abs(self) -> Self;
    /// 符号 $\operatorname{sgn}(x) \in \{-1, 0, 1\}$。
    fn generic_signum(self) -> Self;
}
macro_rules! impl_signed {
    ($($T:ty),* $(,)?) => {$(
        impl Signed for $T {
            fn zero() -> Self { 0 }
            fn one() -> Self { 1 }
            fn generic_abs(self) -> Self { self.abs() }
            fn generic_signum(self) -> Self { self.signum() }
        }
    )*}
}
impl_signed! { i8, i16, i32, i64, i128, isize }

macro_rules! forward_ops {
    ($(($trait:ident, $method_assign:ident, $method:ident),)*) => {$(
        impl<M: Signed> $trait for Rational<M> {
            type Output = Self;
            fn $method(mut self, rhs: Self) -> Self {
                self.$method_assign(rhs);
                self
            }
        }
        impl<'a, T: Signed> $trait<Rational<T>> for &'a Rational<T> {
            type Output = Rational<T>;
            fn $method(self, other: Rational<T>) -> Self::Output {
                $trait::$method(*self, other)
            }
        }

        impl<'a, T: Signed> $trait<&'a Rational<T>> for Rational<T> {
            type Output = Self;
            fn $method(self, other: &Self) -> Self::Output {
                $trait::$method(self, *other)
            }
        }

        impl<'a, T: Signed> $trait<&'a Rational<T>> for &'a Rational<T> {
            type Output = Rational<T>;
            fn $method(self, other: &Rational<T>) -> Self::Output {
                $trait::$method(*self, *other)
            }
        }
    )*};
}
forward_ops! {
    (Add, add_assign, add),
    (Sub, sub_assign, sub),
    (Mul, mul_assign, mul),
    (Div, div_assign, div),
}

fn gcd<T: Signed>(mut x: T, mut y: T) -> T {
    if x < y {
        swap(&mut x, &mut y);
    }
    while y != T::zero() {
        x %= y;
        swap(&mut x, &mut y);
    }
    x
}

#[cfg(test)]
mod tests {
    use super::Rational;
    use approx::assert_abs_diff_eq;
    use ordered_float::OrderedFloat;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter::repeat_with;

    #[test]
    fn test_add() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let (x, xf64) = gen_rational_and_f64(&mut rng);
            let (y, yf64) = gen_rational_and_f64(&mut rng);
            let z = x + y;
            let zf64 = xf64 + yf64;
            println!("{x:?} + {y:?} = {z:?} ({xf64:.3} + {yf64:.3} = {zf64:.3})");
            assert_abs_diff_eq!(z.into_f64(), zf64, epsilon = 1e-6);
        }
    }

    #[test]
    fn test_sub() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let (x, xf64) = gen_rational_and_f64(&mut rng);
            let (y, yf64) = gen_rational_and_f64(&mut rng);
            let z = x - y;
            let zf64 = xf64 - yf64;
            println!("{x:?} - {y:?} = {z:?} ({xf64:.3} - {yf64:.3} = {zf64:.3})");
            assert_abs_diff_eq!(z.into_f64(), zf64, epsilon = 1e-6);
        }
    }

    #[test]
    fn test_mul() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let (x, xf64) = gen_rational_and_f64(&mut rng);
            let (y, yf64) = gen_rational_and_f64(&mut rng);
            let z = x * y;
            let zf64 = xf64 * yf64;
            println!("{x:?} * {y:?} = {z:?} ({xf64:.3} * {yf64:.3} = {zf64:.3})");
            assert_abs_diff_eq!(z.into_f64(), zf64, epsilon = 1e-6);
        }
    }

    #[test]
    fn test_div() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let (x, xf64) = gen_rational_and_f64(&mut rng);
            let (y, yf64) = gen_nonzero_rational_and_f64(&mut rng);
            let z = x / y;
            let zf64 = xf64 / yf64;
            println!("{x:?} / {y:?} = {z:?} ({xf64:.3} / {yf64:.3} = {zf64:.3})");
            assert_abs_diff_eq!(z.into_f64(), zf64, epsilon = 1e-6);
        }
    }

    #[test]
    fn test_neg() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let (x, xf64) = gen_rational_and_f64(&mut rng);
            let y = -x;
            let yf64 = -xf64;
            println!("neg({x:?})  = -{y:?} (neg({xf64:.3}) = {yf64:.3})");
            assert_abs_diff_eq!(y.into_f64(), yf64, epsilon = 1e-6);
        }
    }

    #[test]
    fn test_ord() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let (x, xf64) = gen_rational_and_f64(&mut rng);
            let (y, yf64) = gen_rational_and_f64(&mut rng);
            let z = x.cmp(&y);
            let zf64 = OrderedFloat(xf64).cmp(&OrderedFloat(yf64));
            println!("cmp({x:?}, {y:?}) = {z:?} (cmp({xf64:.3}, {yf64:.3}) = {zf64:?})");
            assert_eq!(z, zf64);
        }
    }

    #[test]
    fn test_sum() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..5);
            let (a, af64) = repeat_with(|| gen_rational_and_f64(&mut rng))
                .take(n)
                .unzip::<_, _, Vec<_>, Vec<_>>();
            let res = a.iter().sum::<Rational<_>>();
            let res_copied = a.iter().copied().sum::<Rational<_>>();
            let resf64 = af64.iter().sum::<f64>();
            assert_abs_diff_eq!(res.into_f64(), resf64, epsilon = 1e-6);
            assert_abs_diff_eq!(res_copied.into_f64(), resf64, epsilon = 1e-6);
        }
    }

    #[test]
    fn test_product() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..5);
            let (a, af64) = repeat_with(|| gen_rational_and_f64(&mut rng))
                .take(n)
                .unzip::<_, _, Vec<_>, Vec<_>>();
            let res = a.iter().product::<Rational<_>>();
            let res_copied = a.iter().copied().product::<Rational<_>>();
            let resf64 = af64.iter().product::<f64>();
            assert_abs_diff_eq!(res.into_f64(), resf64, epsilon = 1e-6);
            assert_abs_diff_eq!(res_copied.into_f64(), resf64, epsilon = 1e-6);
        }
    }

    fn gen_rational_and_f64(rng: &mut StdRng) -> (Rational<i32>, f64) {
        let num = rng.gen_range(-6..=6);
        let mut den = rng.gen_range(-6..6);
        if 0 <= den {
            den += 1;
        }
        (Rational::new(num, den), f64::from(num) / f64::from(den))
    }
    fn gen_nonzero_rational_and_f64(rng: &mut StdRng) -> (Rational<i32>, f64) {
        let mut num = rng.gen_range(-6..6);
        if 0 <= num {
            num += 1;
        }
        let mut den = rng.gen_range(-6..6);
        if 0 <= den {
            den += 1;
        }
        (Rational::new(num, den), f64::from(num) / f64::from(den))
    }
}
