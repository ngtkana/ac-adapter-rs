#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! [`Mint`] 型を提供します。
//!
//! [`Mint`]: struct.Mint.html

/// [`Mint`] の中に入れる数値型が実装していないといけないトレイトをまとめました。
///
/// どうやら普通の符号付き整数型ならば大丈夫そうですね。
///
/// いかがでしたでしょうか？（真顔）
///
/// [`Mint`]: struct.Mint.html
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

/// mod に関数情報を [`Mint`] に伝えるための型引数だッピ！
///
/// [`Mint`]: struct.Mint.html
pub trait Minfo: Clone + Copy + std::fmt::Debug {
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
/// 型引数は、トレイト [`Minfo`] を実装している必要があります。
///
/// # Examples
///
/// [`from_value`] によって、`Mint<Mod>` が作れます。
/// 逆に、[`value`] によって、中身がとれます。
///
/// ```
/// use modint::Mint1000000007;
/// type Mint = Mint1000000007;
///
/// let x: Mint = Mint::from_value(2);
///
/// assert_eq!(x.value(), 2);
/// ```
///
/// 四則演算ができます。
///
/// ```
/// use modint::Mint1000000007;
/// type Mint = Mint1000000007;
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
/// [`value`]: #method.value
/// [`from_value`]: #method.from_value
/// [`Minfo`]:trait.Minfo.html

#[derive(Clone, Copy, Debug)]
pub struct Mint<Mod: Minfo>(Mod::Value);

impl<Mod: Minfo> Mint<Mod> {
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
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::Mint998244353;
    /// type Mint = Mint998244353;
    ///
    /// let x = Mint::zero();
    /// assert_eq!(x.value(), 0);
    /// ```
    #[allow(dead_code)]
    pub fn zero() -> Self {
        Self(Mod::zero())
    }

    /// 1 を構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::Mint998244353;
    /// type Mint = Mint998244353;
    ///
    /// let x = Mint::one();
    /// assert_eq!(x.value(), 1);
    /// ```
    #[allow(dead_code)]
    pub fn one() -> Self {
        Self(Mod::one())
    }

    /// mod を取得します。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::Mint998244353;
    /// type Mint = Mint998244353;
    ///
    /// let x = Mint::modulus();
    /// assert_eq!(x, 998244353);
    /// ```
    #[allow(dead_code)]
    pub fn modulus() -> Mod::Value {
        Mod::modulus()
    }

    /// 0 であるときに `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::Mint998244353;
    /// type Mint = Mint998244353;
    ///
    /// let x = Mint::zero();
    /// assert!(x.is_zero());
    ///
    /// let x = Mint::one();
    /// assert!(!x.is_zero());
    /// ```
    #[allow(dead_code)]
    pub fn is_zero(&self) -> bool {
        self.value() == Mod::zero()
    }

    /// 構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::Mint998244353;
    /// type Mint = Mint998244353;
    ///
    /// let x = Mint::from_value(4);
    /// ```
    #[allow(dead_code)]
    pub fn from_value(x: Mod::Value) -> Self {
        Self(Self::normalize(x))
    }

    /// 中身を取得します。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::Mint998244353;
    /// type Mint = Mint998244353;
    ///
    /// let x = Mint::from_value(4);
    /// assert_eq!(x.value(), 4);
    /// ```
    #[allow(dead_code)]
    pub fn value(&self) -> Mod::Value {
        self.0
    }

    /// mod 逆元を計算します。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::Mint998244353;
    /// type Mint = Mint998244353;
    ///
    /// let x = Mint::from_value(2);
    /// assert_eq!(x.inv().value(), 499122177);
    /// ```
    #[allow(dead_code)]
    pub fn inv(&self) -> Self {
        if self.is_zero() {
            panic!("inv(0)");
        }
        Self(Self::raw_inv(self.value()))
    }

    /// ユークリッドの互除法を用いて、pow を計算します。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    ///
    /// let x = Mint17::from_value(2);
    /// assert_eq!(x.pow(6).value(), 64 % 17);
    /// ```
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

    #[allow(clippy::many_single_char_names)]
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
        Self::normalize(v)
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
            impl<Mod: Minfo> std::ops::$biop_trait for Mint<Mod> {
                type Output = Self;
                fn $biop_fn(self, rhs: Self) -> Self::Output {
                    Mint(Self::$biop_impl(self.value(), rhs.value()))
                }
            }
            impl<Mod: Minfo> std::ops::$biop_assign_trait for Mint<Mod>
            where
                Self: Copy
            {
                fn $biop_assign_fn(&mut self, rhs: Self) {
                    use std::ops::$biop_trait;
                    *self = Mint::$biop_fn(*self, rhs)
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

impl<Mod: Minfo> std::ops::Neg for Mint<Mod> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        Self(Self::raw_neg(self.value()))
    }
}

impl<Mod: Minfo> std::cmp::PartialEq for Mint<Mod> {
    /// 中身をそのまま 比較です。
    /// 構築時に normalize され、それ以降も normalized な状態に保たれますから、
    /// 結局あまりを比較しているのと同じことになります。
    ///
    /// # Example
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    ///
    /// assert_eq!(Mint17::from_value(3), Mint::from_value(-31));
    /// assert_eq!(Mint17::from_value(3), Mint::from_value(-14));
    /// assert_eq!(Mint17::from_value(3), Mint::from_value(3));
    /// assert_eq!(Mint17::from_value(3), Mint::from_value(20));
    /// assert_eq!(Mint17::from_value(3), Mint::from_value(37));
    ///
    /// assert_ne!(Mint17::from_value(3), Mint::from_value(31));
    /// assert_ne!(Mint17::from_value(3), Mint::from_value(14));
    /// assert_ne!(Mint17::from_value(3), Mint::from_value(-3));
    /// assert_ne!(Mint17::from_value(3), Mint::from_value(-20));
    /// assert_ne!(Mint17::from_value(3), Mint::from_value(-37));
    /// ```
    fn eq(&self, other: &Self) -> bool {
        self.value().eq(&other.value())
    }
}
impl<Mod: Minfo> std::cmp::Eq for Mint<Mod> {}

impl<Mod: Minfo> std::fmt::Display for Mint<Mod> {
    /// 中身をそのまま Display です。
    ///
    /// # Example
    ///
    /// ```
    /// println!("{}", modint::Mint998244353::from_value(42));
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}

impl<Mod: Minfo> std::iter::Sum<Self> for Mint<Mod> {
    /// 総和を取ります。
    ///
    /// # Example
    ///
    /// ```
    /// use modint::{define_mint, Minfo, Mint};
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    /// assert_eq!(
    ///     vec![
    ///         Mint17::from_value(2),
    ///         Mint17::from_value(4),
    ///         Mint17::from_value(6),
    ///         Mint17::from_value(8),
    ///     ]
    ///     .into_iter()
    ///     .sum::<Mint17>(),
    ///     Mint17::from_value(3)
    /// );
    /// ```
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Mint::zero(), |acc, x| acc + x)
    }
}

impl<Mod: Minfo> std::iter::Product<Self> for Mint<Mod> {
    /// 総積を取ります。
    ///
    /// # Example
    ///
    /// ```
    /// use modint::{define_mint, Minfo, Mint};
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    /// assert_eq!(
    ///     vec![
    ///         Mint17::from_value(1),
    ///         Mint17::from_value(2),
    ///         Mint17::from_value(3),
    ///         Mint17::from_value(4),
    ///     ]
    ///     .into_iter()
    ///     .product::<Mint17>(),
    ///     Mint17::from_value(7)
    /// );
    /// ```
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Mint::one(), |acc, x| acc * x)
    }
}

/// 階乗とその逆元を前計算するマシーンです。
#[allow(dead_code)]
pub struct Factorial<Mod: Minfo> {
    normal: Vec<Mint<Mod>>,
    inverted: Vec<Mint<Mod>>,
}

#[allow(dead_code)]
impl<Mod: Minfo> Factorial<Mod>
where
    Mod::Value: std::convert::TryFrom<usize, Error = std::num::TryFromIntError>,
{
    /// サイズを指定して初期化です。
    /// 最大値は一つ小さくなりますから、注意です。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo, Factorial};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    /// let fact = Factorial::<Minfo17>::new(16);
    /// ```
    pub fn new(n: usize) -> Self {
        use std::convert::TryFrom;
        let mut normal = vec![Mint::one(); n];
        for i in 1..n {
            normal[i] = normal[i - 1] * Mint::from_value(Mod::Value::try_from(i).unwrap());
        }
        let mut inverted = vec![Mint::one(); n];
        inverted[n - 1] = normal[n - 1].inv();
        for i in (1..n).rev() {
            inverted[i - 1] = inverted[i] * Mint::from_value(Mod::Value::try_from(i).unwrap());
        }
        Self { normal, inverted }
    }
}

#[allow(dead_code)]
impl<Mod: Minfo> Factorial<Mod> {
    /// 階乗の逆元を取得します。
    ///
    /// 逆元でなくて普通の階乗は、[`implementations`] をご覧いただけると幸いです。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo, Factorial};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    ///
    /// let fact = Factorial::<Minfo17>::new(17);
    ///
    /// for i in 0..17 {
    ///     assert_eq!(fact[i] * fact.inverted(i), Mint17::one());
    /// }
    /// ```
    ///
    /// [`implementations`]: #implementations
    ///
    pub fn inverted(&self, i: usize) -> Mint<Mod> {
        self.inverted[i]
    }
}

#[allow(dead_code)]
impl<Mod: Minfo, I: std::slice::SliceIndex<[Mint<Mod>]>> std::ops::Index<I> for Factorial<Mod> {
    type Output = I::Output;

    /// Index でも取ることができます。
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo, Factorial};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    ///
    /// let fact = Factorial::<Minfo17>::new(17);
    ///
    /// assert_eq!(fact[0], Mint17::from_value(1));
    /// assert_eq!(fact[1], Mint17::from_value(1));
    /// assert_eq!(fact[2], Mint17::from_value(2));
    /// assert_eq!(fact[3], Mint17::from_value(6));
    /// assert_eq!(fact[4], Mint17::from_value(24 % 17));
    /// assert_eq!(fact[5], Mint17::from_value(120 % 17));
    /// ```
    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        &self.normal[index]
    }
}

/// 二重階乗とその逆元を前計算するマシーンです。
#[allow(dead_code)]
pub struct DoubleFactorial<Mod: Minfo> {
    normal: Vec<Mint<Mod>>,
    inverted: Vec<Mint<Mod>>,
}

#[allow(dead_code)]
impl<Mod: Minfo> DoubleFactorial<Mod>
where
    Mod::Value: std::convert::TryFrom<usize, Error = std::num::TryFromIntError>,
{
    /// サイズを指定して初期化です。
    /// 最大値は一つ小さくなりますから、注意です。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo, DoubleFactorial};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    /// let fact = DoubleFactorial::<Minfo17>::new(16);
    /// ```
    pub fn new(n: usize) -> Self {
        use std::convert::TryFrom;
        let mut normal = vec![Mint::one(); n];
        for i in 2..n {
            normal[i] = normal[i - 2] * Mint::from_value(Mod::Value::try_from(i).unwrap());
        }
        let mut inverted = vec![Mint::one(); n];
        inverted[n - 1] = normal[n - 1].inv();
        inverted[n - 2] = normal[n - 2].inv();
        for i in (2..n).rev() {
            inverted[i - 2] = inverted[i] * Mint::from_value(Mod::Value::try_from(i).unwrap());
        }
        Self { normal, inverted }
    }
}

#[allow(dead_code)]
impl<Mod: Minfo> DoubleFactorial<Mod> {
    /// 二重階乗の逆元を取得します。
    ///
    /// 逆元でなくて普通の二重階乗は、[`implementations`] をご覧いただけると幸いです。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo, DoubleFactorial};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    ///
    /// let fact = DoubleFactorial::<Minfo17>::new(17);
    ///
    /// for i in 0..17 {
    ///     assert_eq!(fact[i] * fact.inverted(i), Mint17::one());
    /// }
    /// ```
    ///
    /// [`implementations`]: #implementations
    ///
    pub fn inverted(&self, i: usize) -> Mint<Mod> {
        self.inverted[i]
    }
}

#[allow(dead_code)]
impl<Mod: Minfo, I: std::slice::SliceIndex<[Mint<Mod>]>> std::ops::Index<I>
    for DoubleFactorial<Mod>
{
    type Output = I::Output;

    /// Index でも取ることができます。
    ///
    /// ```
    /// use modint::{define_mint, Mint, Minfo, DoubleFactorial};
    ///
    /// define_mint! {
    ///     struct Mint17(Minfo17(17; i16));
    /// }
    ///
    /// let fact = DoubleFactorial::<Minfo17>::new(17);
    ///
    /// assert_eq!(fact[0], Mint17::from_value(1));
    /// assert_eq!(fact[1], Mint17::from_value(1));
    /// assert_eq!(fact[2], Mint17::from_value(2));
    /// assert_eq!(fact[3], Mint17::from_value(3));
    /// assert_eq!(fact[4], Mint17::from_value(8));
    /// assert_eq!(fact[5], Mint17::from_value(15));
    /// ```
    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        &self.normal[index]
    }
}

/// Mint 型を定義するためのマクロです。
///
/// # Examples
///
/// ```
/// use modint::{define_mint, Minfo, Mint};
///
/// define_mint! {
///     struct Mint17(Minfo17(17; i64));
/// }
///
/// let x = Mint17::from_value(1);
/// let y = Mint17::from_value(2);
/// let z = x / y;
/// assert_eq!(z.value(), 9);
/// ```
#[macro_export]
macro_rules! define_mint {
    (
        struct $modint: ident ($modinfo: ident ($modvalue: expr; $modty: ty));
    ) => {
        #[allow(dead_code)]
        #[derive(Clone, Copy, Debug)]
        pub struct $modinfo {}
        impl Minfo for $modinfo {
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
        type $modint = Mint<$modinfo>;
    };
}

/// Mod = 1000000007 なる Minfo です。
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub struct Minfo1000000007 {}

impl Minfo for Minfo1000000007 {
    type Value = i64;
    fn modulus() -> Self::Value {
        1_000_000_007
    }
    fn zero() -> Self::Value {
        0
    }
    fn one() -> Self::Value {
        1
    }
}

/// Mod = 1000000007 なる Mint です。
#[allow(dead_code)]
pub type Mint1000000007 = Mint<Minfo1000000007>;

/// Mod = 998244353 なる Minfo です。
#[allow(dead_code)]
#[derive(Clone, Copy, Debug)]
pub struct Minfo998244353 {}

impl Minfo for Minfo998244353 {
    type Value = i64;
    fn modulus() -> Self::Value {
        998_244_353
    }
    fn zero() -> Self::Value {
        0
    }
    fn one() -> Self::Value {
        1
    }
}

/// Mod = 998244353 なる Mint です。
#[allow(dead_code)]
pub type Mint998244353 = Mint<Minfo998244353>;

#[cfg(test)]
mod tests {
    use super::*;

    define_mint! {
        struct Mint17(Minfo17(17; i16));
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
