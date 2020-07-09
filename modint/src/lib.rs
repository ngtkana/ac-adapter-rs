#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! [`Modint`] 型を提供します。
//!
//! [`Modint`]: struct.Modint.html

/// [`Modint`] の中に入れる数値型が実装していないといけないトレイトをまとめました。
///
/// どうやら普通の符号付き整数型ならば大丈夫そうですね。
///
/// いかがでしたでしょうか？（真顔）
///
/// [`Modint`]: struct.Modint.html
pub trait ModValue:
    std::ops::Add<Output = Self>
    + std::ops::Sub<Output = Self>
    + std::ops::Mul<Output = Self>
    + std::ops::Div<Output = Self>
    + std::ops::Rem<Output = Self>
    + std::ops::AddAssign
    + std::ops::SubAssign
    + std::ops::MulAssign
    + std::ops::DivAssign
    + std::ops::RemAssign
    + std::ops::Neg
    + std::cmp::Ord
    + Clone
    + Copy
    + Sized
    + std::fmt::Debug
    + std::fmt::Display
{
}

impl<
        Value: std::ops::Add<Output = Self>
            + std::ops::Sub<Output = Self>
            + std::ops::Mul<Output = Self>
            + std::ops::Div<Output = Self>
            + std::ops::Rem<Output = Self>
            + std::ops::AddAssign
            + std::ops::SubAssign
            + std::ops::MulAssign
            + std::ops::DivAssign
            + std::ops::RemAssign
            + std::ops::Neg
            + std::cmp::Ord
            + Clone
            + Copy
            + Sized
            + std::fmt::Debug
            + std::fmt::Display,
    > ModValue for Value
{
}

/// [`Modint`] の型引数になるために実装すべきトレイトです。
///
/// [`Modint`]: struct.Modint.html
pub trait ModInfo {
    /// 中身の型です。
    type Value: ModValue;

    /// mod の値を返します。
    fn modulus() -> Self::Value;

    /// 0 を返します。
    fn zero() -> Self::Value;

    /// 1 を返します。
    fn one() -> Self::Value;
}

/// 自動で mod を取ってくれる整数型です。
///
/// 型引数は、トレイト [`ModInfo`] を実装している必要があります。
///
/// # Examples
///
/// [`from_value`] によって、`Modint<Mod>` が作れます。
/// 逆に、[`value`] によって、中身がとれます。
///
/// ```
/// use modint::Mint100000007;
/// type Mint = Mint100000007;
///
/// let x: Mint = Mint::from_value(2);
///
/// assert_eq!(x.value(), 2);
/// ```
///
/// 四則演算ができます。
///
/// ```
/// use modint::Mint100000007;
/// type Mint = Mint100000007;
///
/// let x: Mint = Mint::from_value(6);
/// let y: Mint = Mint::from_value(2);
///
/// assert_eq!((x + y).value(), 8);
/// assert_eq!((x - y).value(), 4);
/// assert_eq!((x * y).value(), 12);
/// assert_eq!((x / y).value(), 3);
/// ```
///
/// [`pow`] もあります。
///
/// ```
/// use modint::Mint100000007;
/// type Mint = Mint100000007;
///
/// let x: Mint = Mint::from_value(6);
/// assert_eq!(x.pow(3).value(), 216);
/// ```
///
/// [`value`]: #method.value
/// [`from_value`]: #method.from_value
/// [`pow`]: #method.pow

#[derive(Clone, Copy, Debug)]
pub struct Modint<Mod: ModInfo>(Mod::Value);

impl<Mod: ModInfo> Modint<Mod> {
    #[inline]
    #[allow(dead_code)]
    fn is_within_the_range(x: Mod::Value) -> bool {
        Mod::zero() <= x && x < Mod::modulus()
    }

    #[inline]
    #[allow(dead_code)]
    fn normalize(x: Mod::Value) -> Mod::Value {
        if Self::is_within_the_range(x) {
            x
        } else {
            let x = x % Mod::modulus();
            if x < Mod::zero() {
                x + Mod::modulus()
            } else {
                x
            }
        }
    }

    /// 0 を構築します。
    #[allow(dead_code)]
    pub fn zero() -> Self {
        Self(Mod::zero())
    }

    /// 1 を構築します。
    #[allow(dead_code)]
    pub fn one() -> Self {
        Self(Mod::one())
    }

    /// mod の値を取得します。
    #[allow(dead_code)]
    pub fn modulus() -> Mod::Value {
        Mod::modulus()
    }

    /// 0 であるときに `true` を返します。
    #[allow(dead_code)]
    pub fn is_zero(&self) -> bool {
        self.value() == Mod::zero()
    }

    /// 構築します。
    #[allow(dead_code)]
    pub fn from_value(x: Mod::Value) -> Self {
        Self(Self::normalize(x))
    }

    /// 中身の値を取得します。
    #[allow(dead_code)]
    pub fn value(&self) -> Mod::Value {
        self.0
    }

    /// mod 逆元を計算します。
    #[allow(dead_code)]
    pub fn inv(&self) -> Self {
        if self.is_zero() {
            panic!("inv(0)");
        }
        Self(Self::raw_inv(self.value()))
    }

    /// ユークリッドの互除法を用いて、pow を計算します。
    #[allow(dead_code)]
    pub fn pow(&self, b: u64) -> Self {
        Self(Self::raw_pow(self.value(), b))
    }

    fn raw_add(x: Mod::Value, y: Mod::Value) -> Mod::Value {
        let z = x + y;
        if Mod::modulus() <= z {
            z - Mod::modulus()
        } else {
            z
        }
    }

    fn raw_sub(x: Mod::Value, y: Mod::Value) -> Mod::Value {
        let z = x - y;
        if z < Mod::zero() {
            z + Mod::modulus()
        } else {
            z
        }
    }

    fn raw_neg(x: Mod::Value) -> Mod::Value {
        if x == Mod::zero() {
            Mod::zero()
        } else {
            Mod::modulus() - x
        }
    }

    fn raw_mul(x: Mod::Value, y: Mod::Value) -> Mod::Value {
        x * y % Mod::modulus()
    }

    fn raw_div(x: Mod::Value, y: Mod::Value) -> Mod::Value {
        Self::raw_mul(x, Self::raw_inv(y))
    }

    fn raw_inv(mut x: Mod::Value) -> Mod::Value {
        let mut y = Mod::modulus();
        let mut u = Mod::one();
        let mut v = Mod::zero();
        while x != Mod::zero() {
            let q = y / x;
            y -= x * q;
            v -= u * q;
            std::mem::swap(&mut x, &mut y);
            std::mem::swap(&mut u, &mut v);
        }
        if v < Mod::zero() {
            v + Mod::modulus()
        } else {
            v
        }
    }

    fn raw_pow(mut a: Mod::Value, mut b: u64) -> Mod::Value {
        let mut x = Mod::one();
        while 0 < b {
            if b % 2 == 1 {
                x = Self::raw_mul(x, a);
            }
            a = Self::raw_mul(a, a);
            b /= 2
        }
        x
    }
}

macro_rules! impl_biop {
    (
        $(
            $biop_trait: ident::$biop_fn: ident,
            $biop_assign_trait: ident::$biop_assign_fn: ident,
            $biop_impl: ident;
        )*
    ) => {
        $(
            impl<Mod: ModInfo> std::ops::$biop_trait for Modint<Mod> {
                type Output = Self;
                fn $biop_fn(self, rhs: Self) -> Self::Output {
                    Modint(Self::$biop_impl(self.value(), rhs.value()))
                }
            }
            impl<Mod: ModInfo> std::ops::$biop_assign_trait for Modint<Mod>
            where
                Self: Copy
            {
                fn $biop_assign_fn(&mut self, rhs: Self) {
                    use std::ops::$biop_trait;
                    *self = Modint::$biop_fn(*self, rhs)
                }
            }
        )*
    };
}

impl_biop! {
    Add::add, AddAssign::add_assign, raw_add;
    Sub::sub, SubAssign::sub_assign, raw_sub;
    Mul::mul, MulAssign::mul_assign, raw_mul;
    Div::div, DivAssign::div_assign, raw_div;
}

impl<Mod: ModInfo> std::ops::Neg for Modint<Mod> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self(Self::raw_neg(self.value()))
    }
}

impl<Mod: ModInfo> std::fmt::Display for Modint<Mod> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

/// Modint 型を定義するためのマクロです。
///
/// # Examples
///
/// ```
/// use modint::{define_modint, ModInfo, Modint};
///
/// define_modint! {
///     struct Mint(Minfo(1_000_000_007; i64));
/// }
///
/// let x = Mint::from_value(1);
/// let y = Mint::from_value(2);
/// let z = x / y;
/// assert_eq!(z.value(), 500_000_004);
/// ```
#[macro_export]
macro_rules! define_modint {
    (
        struct $modint: ident ($modinfo: ident ($modvalue: expr; $modty: ty));
    ) => {
        #[allow(dead_code)]
        #[derive(Clone, Copy, Debug)]
        pub struct $modinfo {}
        impl ModInfo for $modinfo {
            type Value = $modty;
            fn modulus() -> Self::Value {
                $modvalue
            }
            fn zero() -> Self::Value {
                0
            }
            fn one() -> Self::Value {
                1
            }
        }
        type $modint = Modint<$modinfo>;
    };
}

/// Mod = 1000000007 なる ModInfo です。
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub struct Mod100000007 {}

impl ModInfo for Mod100000007 {
    type Value = i64;
    fn modulus() -> Self::Value {
        1000000007
    }
    fn zero() -> Self::Value {
        0
    }
    fn one() -> Self::Value {
        1
    }
}

/// Mod = 1000000007 なる Modint です。
pub type Mint100000007 = Modint<Mod100000007>;

/// Mod = 998244353 なる ModInfo です。
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub struct Mod998244353 {}

impl ModInfo for Mod998244353 {
    type Value = i64;
    fn modulus() -> Self::Value {
        998244353
    }
    fn zero() -> Self::Value {
        0
    }
    fn one() -> Self::Value {
        1
    }
}

/// Mod = 998244353 なる Modint です。
pub type Mint998244353 = Modint<Mod998244353>;

#[cfg(test)]
mod tests {
    use super::*;

    define_modint! {
        struct Mint17(Modinfo17(17; i64));
    }

    #[test]
    fn test_addition() {
        let x: Mint17 = Mint17::from_value(12);
        let y: Mint17 = Mint17::from_value(14);
        assert_eq!((x + y).value(), 9);
    }

    #[test]
    fn test_subtraction() {
        let x: Mint17 = Mint17::from_value(12);
        let y: Mint17 = Mint17::from_value(14);
        assert_eq!((x - y).value(), 15);
    }

    #[test]
    fn test_multiplication() {
        let x: Mint17 = Mint17::from_value(4);
        let y: Mint17 = Mint17::from_value(5);
        assert_eq!((x * y).value(), 3);
    }

    #[test]
    fn test_division() {
        let x: Mint17 = Mint17::from_value(3);
        let y: Mint17 = Mint17::from_value(5);
        assert_eq!((x / y).value(), 4);
    }

    #[test]
    fn test_inverse() {
        let x: Mint17 = Mint17::from_value(3);
        assert_eq!(x.inv().value(), 6);
    }

    #[test]
    #[should_panic]
    fn test_inverse_of_zero() {
        let x: Mint17 = Mint17::from_value(0);
        x.inv();
    }

    #[test]
    fn test_autonomalization_greater() {
        let x: Mint17 = Mint17::from_value(20);
        assert_eq!(x.inv().value(), 6);
    }

    #[test]
    fn test_autonomalization_less() {
        let x: Mint17 = Mint17::from_value(-14);
        assert_eq!(x.inv().value(), 6);
    }

    #[test]
    fn test_pow() {
        let x: Mint17 = Mint17::from_value(3);
        assert_eq!(x.pow(3).value(), 10);
    }

    #[test]
    fn test_display() {
        let x: Mint17 = Mint17::from_value(-14);
        println!("x = {}", x);
    }
}
