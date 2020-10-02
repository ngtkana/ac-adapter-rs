#![warn(missing_docs)]
//! 有限体ライブラリです。
//!
//! # 構築
//!
//! [`new`] で構築できます。便利関数 [`frac`] で分数からも構築できます。
//!
//! ```
//! use fp::*;
//! let _ = F998244353::new(4); // 4 （整数から）
//! let _ = F998244353::frac(4, 3); // 4 / 3 （分数から）
//! ```
//!
//! # 取り出し
//!
//! [`into_inner`] で取り出せます。（`.0` で取り出せないのは、`0 <= self.0 && self.0 < Mod::VALUE`
//! の条件を勝手に壊されると困るからです。）
//!
//! ```
//! use fp::*;
//! let x = F998244353::new(4);
//! assert_eq!(x.into_inner(), 4);
//! ```
//!
//! # トレイト実装
//!
//! - 演算系 : [`Add`], [`AddAssign`], [`Sub`], [`SubAssign`], [`Mul`], [`MulAssign`], [`Div`],
//! [`DivAssign`], [`Neg`]
//! - [`iter`] 系 : [`Sum`], [`Product`]
//! - [`type_traits`] 系 : [`Zero`], [`One`]
//! - [`cmp`] 系: [`PartialEq`], [`Eq`]
//! - [`fmt`] 系: [`Debug`], [`Display`]
//!
//!
//! # その他計算関数
//!
//! [`inv`], [`pow`] があります。
//!
//! ```
//! use fp::*;
//! assert_eq!(F998244353::new(2).pow(3), F998244353::new(8));
//! assert_eq!(F998244353::new(2).inv(), F998244353::new(499122177));
//! ```
//!
//! # 新しい `Mod` の作りかた
//!
//! [`F998244353`] の定義はこのようになっております。導出している 5 つのトレイトはすべて
//! [`Modable`] が継承しているため、必須となっております。
//!
//! ```
//! use fp::*;
//! use type_traits::*;
//! #[derive(Debug, Clone, Copy, PartialEq, Eq)]
//! pub struct Mod998244353 {}
//! pub type F998244353 = Fp<Mod998244353>;
//! impl Constant for Mod998244353 {
//!     type Output = i64;
//!     const VALUE: i64 = 998_244_353;
//! }
//! ```
//!
//! [`new`]: struct.Fp.html#method.new
//! [`frac`]: struct.Fp.html#method.frac
//! [`into_inner`]: struct.Fp.html#method.into_inner
//! [`inv`]: struct.Fp.html#method.inv
//! [`pow`]: struct.Fp.html#method.pow
//! [`F998244353`]: struct.F998244353.html
//! [`Modable`]: trait.Modable.html
//!
//! [`type_traits`]: ../type_traits/index.html
//! [`Zero`]: ../type_traits/trait.Zero.html
//! [`One`]: ../type_traits/trait.One.html
//!
//! [`fmt`]: https://doc.rust-lang.org/std/fmt/index.html
//! [`cmp`]: https://doc.rust-lang.org/std/cmp/index.html
//! [`iter`]: https://doc.rust-lang.org/std/iter/index.html
//! [`Add`]: https://doc.rust-lang.org/std/ops/trait.Add.html
//! [`Sub`]: https://doc.rust-lang.org/std/ops/trait.Sub.html
//! [`Mul`]: https://doc.rust-lang.org/std/ops/trait.Mul.html
//! [`Div`]: https://doc.rust-lang.org/std/ops/trait.Div.html
//! [`Neg`]: https://doc.rust-lang.org/std/ops/trait.Neg.html
//! [`AddAssign`]: https://doc.rust-lang.org/std/ops/trait.AddAssign.html
//! [`SubAssign`]: https://doc.rust-lang.org/std/ops/trait.SubAssign.html
//! [`MulAssign`]: https://doc.rust-lang.org/std/ops/trait.MulAssign.html
//! [`DivAssign`]: https://doc.rust-lang.org/std/ops/trait.DivAssign.html
//! [`Sum`]: https://doc.rust-lang.org/std/iter/trait.Sum.html
//! [`Product`]: https://doc.rust-lang.org/std/iter/trait.Product.html
//! [`PartialEq`]: https://doc.rust-lang.org/std/cmp/trait.PartialEq.html
//! [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
//! [`Debug`]: https://doc.rust-lang.org/std/fmt/trait.Debug.html
//! [`Display`]: https://doc.rust-lang.org/std/fmt/trait.Display.html
pub use aliases::*;
use std::{cmp, fmt, iter, mem, ops::*};
use type_traits::*;

mod arith;

/// `Vec<Fp<_>>` を作ります。
#[macro_export]
macro_rules! fp_vec {
    () => (
        Vec::<$crate::Fp<_>>::new()
    );
    ($elem:expr; $n:expr) => (
        vec![$crate::Fp::new($elem); $n]
    );
    ($($x:expr),+ $(,)?) => (
        vec![$($crate::Fp::new($x),)+];
    );
}

/// 有限体ライブラリ本体です。
///
/// 詳しくは[モジュールレベルドキュメント](index.html)をご覧ください。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fp<Mod: Modable>(Mod::Output);

impl<Mod: Modable> Fp<Mod>
where
    Mod::Output: Value,
{
    /// 整数から構築します。
    pub fn new(src: Mod::Output) -> Self {
        Self(Self::normalize(src))
    }

    /// 分数から構築します。
    pub fn frac(num: Mod::Output, den: Mod::Output) -> Self {
        Self::new(num) / Self::new(den)
    }

    /// 中身にキャストします。
    pub fn into_inner(self) -> Mod::Output {
        self.0
    }

    /// Mod 逆元を返します。[`Div`](https://doc.rust-lang.org/std/ops/trait.Div.html) からも呼ばれています。
    #[allow(clippy::many_single_char_names)]
    pub fn inv(self) -> Self {
        assert_ne!(
            self.into_inner(),
            Mod::Output::zero(),
            "さては 0 の逆元を取ろうとしていますね？"
        );
        let mut x = self.into_inner();
        let mut y = Mod::VALUE;
        let mut u = Mod::Output::one();
        let mut v = Mod::Output::zero();
        while x != Mod::Output::zero() {
            let q = y / x;
            y -= q * x;
            v -= q * u;
            mem::swap(&mut x, &mut y);
            mem::swap(&mut u, &mut v);
        }
        assert!(
            x == Mod::Output::zero()
                && y == Mod::Output::one()
                && (u == Mod::VALUE || u == -Mod::VALUE)
                && (-Mod::VALUE < v && v < Mod::VALUE)
        );
        Self(Self::normalize_from_the_top(v))
    }

    /// 塁乗をします。
    pub fn pow(mut self, mut p: u64) -> Self {
        let mut ans = Self::one();
        while p != 0 {
            if p % 2 == 1 {
                ans *= self;
            }
            self *= self;
            p /= 2;
        }
        ans
    }

    fn normalize(src: Mod::Output) -> Mod::Output {
        Self::normalize_from_the_top(src % Mod::VALUE)
    }

    fn normalize_from_the_bottom(src: Mod::Output) -> Mod::Output {
        if Mod::VALUE <= src {
            src - Mod::VALUE
        } else {
            src
        }
    }

    fn normalize_from_the_top(src: Mod::Output) -> Mod::Output {
        if src < Mod::Output::zero() {
            src + Mod::VALUE
        } else {
            src
        }
    }
}

impl<Mod: Modable> Zero for Fp<Mod>
where
    Mod::Output: Value,
{
    fn zero() -> Fp<Mod> {
        Fp::new(Mod::Output::zero())
    }
}
impl<Mod: Modable> One for Fp<Mod>
where
    Mod::Output: Value,
{
    fn one() -> Fp<Mod> {
        Fp::new(Mod::Output::one())
    }
}

impl<Mod: Modable> iter::Sum<Fp<Mod>> for Fp<Mod>
where
    Mod::Output: Value,
{
    fn sum<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = Fp<Mod>>,
    {
        iter.fold(Fp::zero(), Add::add)
    }
}

impl<'a, Mod: 'a + Modable> iter::Sum<&'a Fp<Mod>> for Fp<Mod>
where
    Mod::Output: Value,
{
    fn sum<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = &'a Fp<Mod>>,
    {
        iter.fold(Fp::zero(), Add::add)
    }
}

impl<Mod: Modable> iter::Product<Fp<Mod>> for Fp<Mod>
where
    Mod::Output: Value,
{
    fn product<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = Fp<Mod>>,
    {
        iter.fold(Self::one(), Mul::mul)
    }
}

impl<'a, Mod: 'a + Modable> iter::Product<&'a Fp<Mod>> for Fp<Mod>
where
    Mod::Output: Value,
{
    fn product<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = &'a Fp<Mod>>,
    {
        iter.fold(Self::one(), Mul::mul)
    }
}

impl<Mod: Modable> fmt::Display for Fp<Mod>
where
    Mod::Output: Value,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

/// `Mod` が満たすべき性質をまとめた型です。
pub trait Modable: Constant + Clone + fmt::Debug + cmp::PartialEq + cmp::Eq {}
impl<Mod: Constant + Clone + fmt::Debug + cmp::PartialEq + cmp::Eq> Modable for Mod {}

/// `<Mod as Constant>::Output` が満たすべき性質をまとめた型です。
///
/// TODO: 共通トレイトを全列挙して `Int` のようなお名前にて、
/// [`type_traits`](../type_traits/index.html) に移動したいです。
pub trait Value:
    Sized
    + Clone
    + Copy
    + Ring
    + fmt::Debug
    + fmt::Display
    + cmp::PartialOrd
    + cmp::Ord
    + cmp::Eq
    + Div<Output = Self>
    + Rem<Output = Self>
    + Neg<Output = Self>
    + DivAssign
    + RemAssign
{
}

macro_rules! impl_value {
    ($($type:ty,)*) => { $(impl Value for $type {})* };
}

impl_value! { i8, i16, i32, i64, i128, isize, }

mod aliases {
    use super::Fp;
    use type_traits::Constant;

    /// [`F1000000007`](aliases/struct.F1000000007.html) の中身です。
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Mod1000000007 {}
    /// [`Fp`](struct.Fp.html) の mod 1,000,000,007 特殊化です。
    pub type F1000000007 = Fp<Mod1000000007>;
    impl Constant for Mod1000000007 {
        type Output = i64;
        const VALUE: i64 = 1_000_000_007;
    }

    /// [`F998244353`](aliases/struct.F998244353.html) の中身です。
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct Mod998244353 {}
    /// [`Fp`](struct.Fp.html) の mod 998,244,353 特殊化です。
    pub type F998244353 = Fp<Mod998244353>;
    impl Constant for Mod998244353 {
        type Output = i64;
        const VALUE: i64 = 998_244_353;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_impl::assert_impl;
    use test_case::test_case;
    use type_traits::define_constant;

    define_constant! { type Mod97: i16 = 97; }
    type F97 = Fp<Mod97>;

    #[test]
    fn test_trait_implementations() {
        assert_impl!(fmt::Debug: F97);
        assert_impl!(fmt::Display: F97);
        assert_impl!(Clone: F97);
        assert_impl!(Copy: F97);
        assert_impl!(PartialEq: F97);
        assert_impl!(cmp::PartialEq: F97);
        assert_impl!(cmp::Eq: F97);
        assert_impl!(!cmp::PartialOrd: F97);
        assert_impl!(!cmp::Ord: F97);
        assert_impl!(Zero: F97);
        assert_impl!(One: F97);
        assert_impl!(Ring: F97);
    }

    #[test]
    fn test_binary_ops() {
        // Add
        assert_eq!(F97::new(4) + F97::new(3), F97::new(7));
        assert_eq!(F97::new(30) + F97::new(70), F97::new(3));

        // Sub
        assert_eq!(F97::new(13) - F97::new(6), F97::new(7));
        assert_eq!(F97::new(6) - F97::new(13), F97::new(90));

        // Mul
        assert_eq!(F97::new(3) * F97::new(4), F97::new(12));
        assert_eq!(F97::new(30) * F97::new(4), F97::new(23));

        // Div
        assert_eq!(F97::new(72) / F97::new(6), F97::new(12));
        assert_eq!(F97::new(1) / F97::new(2), F97::new(49));
    }

    #[test]
    fn test_binary_op_assign() {
        let mut x = F97::new(42);

        // AddAssign
        x += F97::new(1);
        assert_eq!(x, F97::new(43));

        // SubAssign
        x -= F97::new(2);
        assert_eq!(x, F97::new(41));

        // MulAssign
        x *= F97::new(2);
        assert_eq!(x, F97::new(82));

        // DivAssign
        x /= F97::new(41);
        assert_eq!(x, F97::new(2));
    }

    #[test]
    fn test_neg() {
        // neg
        assert_eq!(-F97::new(0), F97::new(0));
        assert_eq!(-F97::new(1), F97::new(96));
    }

    #[test]
    fn test_ref_ops() {
        // add(&, *), add(*, &), add(&, &)
        assert_eq!(&F97::new(1) + F97::new(1), F97::new(2));
        assert_eq!(F97::new(1) + &F97::new(1), F97::new(2));
        assert_eq!(&F97::new(1) + &F97::new(1), F97::new(2));

        // sub(&, *), sub(*, &), sub(&, &)
        assert_eq!(&F97::new(1) - F97::new(1), F97::new(0));
        assert_eq!(F97::new(1) - &F97::new(1), F97::new(0));
        assert_eq!(&F97::new(1) - &F97::new(1), F97::new(0));

        // mul(&, *), mul(*, &), mul(&, &)
        assert_eq!(&F97::new(1) * F97::new(1), F97::new(1));
        assert_eq!(F97::new(1) * &F97::new(1), F97::new(1));
        assert_eq!(&F97::new(1) * &F97::new(1), F97::new(1));

        // div(&, *), div(*, &), div(&, &)
        assert_eq!(&F97::new(1) / F97::new(1), F97::new(1));
        assert_eq!(F97::new(1) / &F97::new(1), F97::new(1));
        assert_eq!(&F97::new(1) / &F97::new(1), F97::new(1));

        // neg(&)
        assert_eq!(-&F97::new(1), F97::new(96));
    }

    #[test_case(7, 0 => 1)]
    #[test_case(7, 1 => 7)]
    #[test_case(7, 2 => 49)]
    #[test_case(7, 3 => 343 % 97)]
    #[test_case(7, 4 => 2401 % 97)]
    fn test_pow(a: i16, b: u64) -> i16 {
        F97::new(a).pow(b).into_inner()
    }

    #[test]
    fn test_sum() {
        // Sum<Fp<_>>
        assert_eq!(fp_vec![2, 3].into_iter().sum::<F97>(), F97::new(5));

        // Sum<&Fp<_>>
        assert_eq!(fp_vec![2, 3].iter().sum::<F97>(), F97::new(5));
    }

    #[test]
    fn test_product() {
        // Product<Fp<_>>
        assert_eq!(
            vec![F97::new(2), F97::new(3)].into_iter().product::<F97>(),
            F97::new(6)
        );

        // Product<&Fp<_>>
        assert_eq!(
            vec![F97::new(2), F97::new(3)].iter().product::<F97>(),
            F97::new(6)
        );
    }
}
