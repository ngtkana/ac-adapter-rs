#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! 新しい `modint` です。
//! 今回は中身を [`i64`] に固定しました。
//!
//! # How to use
//!
//! [`Mint998244353`], [`Mint100000007`] なるプリセットがありますから、それを使いましょう。
//! 値の構築は、
//! - [`from_i64`], [`Mint::from_frac`], [`Mint::from_pow`] メソッド
//! - [`From`] トレイト
//! - [`mint`], [`from_frac`], [`from_pow`] マクロ
//! で行うことができます。
//!
//! 標準ライブラリの [`ops`], [`cmp`], [`fmt`] に対応していて、複合代入、[`neg`] を含む四則演算、
//! [`Eq`], [`Ord`] による等値・比較演算、[`Debug`], [`Display`] によるフォーマットができます。
//! また [`pow`] もできます。
//!
//! ```
//! use modint::{Mint998244353, mint};
//! type Mint = modint::Mint998244353;
//! let x = Mint::from_i64(6);  // from_i64 メソッドによる構築です。
//! let y: Mint = 3.into();     // From トレイトによる構築です。
//! let z = mint!(2);           // マクロによる構築です。ここでは Mint998244353 が構築されます。
//!
//! // 四則演算ができます。
//! assert_eq!(x + y, mint!(9));
//! assert_eq!(x - y, mint!(3));
//! assert_eq!(x * y, mint!(18));
//! assert_eq!(x / y, mint!(2));
//!
//! // neg, pow もできます。
//! assert_eq!(-x, mint!(998_244_347));
//! assert_eq!(x.pow(3), mint!(216));
//!
//! // 複合代入ができます。
//! let mut x = mint!(10);
//! x += mint!(10);
//! assert_eq!(x, mint!(20));
//! x -= mint!(15);
//! assert_eq!(x, mint!(5));
//! x *= mint!(8);
//! assert_eq!(x, mint!(40));
//! x /= mint!(5);
//! assert_eq!(x, mint!(8));
//! ```
//!
//! # auto modding
//!
//! 薄々お気づきかもしれないのですが、自動であまりをとります。
//! 998244353 の暗算は厳しいですから、5 くらいにしておきましょう。
//!
//! ```
//! use modint::{mint, ModTrait, ModValue};
//!
//! #[derive(Debug, Clone, Copy)]
//! struct Mod5 {}
//! impl ModTrait for Mod5 {
//!     fn modulus() -> ModValue {
//!         5
//!     }
//! }
//! type Mint = modint::Mint<Mod5>;
//!
//! assert_eq!(mint!(3) + mint!(3), mint!(1));
//! assert_eq!(mint!(1) - mint!(3), mint!(3));
//! assert_eq!(mint!(3) * mint!(3), mint!(4));
//! assert_eq!(mint!(1) / mint!(2), mint!(3));
//! assert_eq!(mint!(3).pow(1375890638712), mint!(1));  // 暗算が得意です！
//! ```
//!
//! # construction macros
//!
//! 値の構築のために、多彩なマクロを用意しています。
//! 名前解決まわりでとても注意が必要ですから、詳しくは [`mint`] をご覧いただけるとです。
//! おそらく競プロ以外でやるととても怒られます。
//!
//! ```
//! use modint::{mint, from_frac, from_pow, Mint998244353};
//! type Mint = Mint998244353;  // 実はこれが本質です。
//!
//! assert_eq!(from_frac!(6, 2), mint!(3));
//! assert_eq!(from_pow!(3, 4), mint!(81));
//! ```
//!
//! # precalculations
//!
//! [`Factorial`] を使うと、階乗前計算ができます。
//! さらに階乗の逆元、下方階乗冪、二項係数の計算もできます。
//!
//! ```
//! use modint::{mint, Mint998244353, Mod998244353, Factorial};
//! let fact = Factorial::<Mod998244353>::with_len(20);
//! type Mint = Mint998244353;
//!
//! assert_eq!(fact[4], mint!(24));                     // 階乗です。
//! assert_eq!(fact.inv(5), mint!(120).inv());          // 階乗の逆元です。
//! assert_eq!(fact.falling(8, 3), mint!(8 * 7 * 6));   // 下方階乗冪です。
//! assert_eq!(fact.binom(8, 3), mint!(56));            // 二項係数です。
//! ```
//!
//! # formatting
//!
//! [`Debug`] と [`Display`] を実装しています。
//!
//! [`Debug`] は、ありそうな有理数をサジェストしてくれます。
//!
//! ```
//! use modint::{from_frac, Mint998244353};
//! type Mint = Mint998244353;
//! let num = 5;
//! let den = 12;
//! let x = from_frac!(num, den);
//! assert_eq!(format!("{:?}", x), format!("Mint(\"{}/{}\")", num, den),);
//! ```
//!
//!
//! # sum / product
//!
//! [`Sum`] と [`Product`] も実装済みです。
//!
//! ```
//! use modint::{mint, Mint998244353};
//! type Mint = Mint998244353;
//! assert_eq!([mint!(3), mint!(2), mint!(7)].iter().sum::<Mint>(), mint!(12));
//! assert_eq!([mint!(3), mint!(2), mint!(7)].iter().product::<Mint>(), mint!(42));
//! ```
//!
//!
//! [`Mint998244353`]: type.Mint998244353.html
//! [`Mint100000007`]: type.Mint100000007.html
//!
//! [`Factorial`]: macro.Factorial.html
//! [`mint`]: macro.mint.html
//! [`from_frac`]: macro.from_frac.html
//! [`from_pow`]: macro.from_pow.html
//!
//! [`pow`]: struct.Mint.html#method.pow
//! [`from_i64`]: struct.Mint.html#method.from_i64
//! [`Mint::from_frac`]: struct.Mint.html#method.from_frac
//! [`Mint::from_pow`]: struct.Mint.html#method.from_pow
//!
//! [`From`]: struct.Mint.html#impl-From<i64>
//! [`Debug`]: struct.Mint.html#impl-Debug
//! [`Display`]: struct.Mint.html#impl-Display
//! [`Eq`]: struct.Mint.html#impl-Eq
//! [`Ord`]: struct.Mint.html#impl-Ord
//! [`Sum`]: struct.Mint.html#impl-Sum<Mint<Mod>>
//! [`Product`]: struct.Mint.html#impl-Product<Mint<Mod>>
//! [`neg`]: struct.Mint.html#impl-Neg
//!
//! [`i64`]: https://doc.rust-lang.org/stable/std/primitive.i64.html
//! [`ops`]: https://doc.rust-lang.org/stable/std/ops/
//! [`cmp`]: https://doc.rust-lang.org/stable/std/cmp/
//! [`fmt`]: https://doc.rust-lang.org/stable/std/fmt/

use std::{
    cmp::{Eq, Ord, Ordering, PartialEq, PartialOrd},
    fmt::{Debug, Display},
    iter::{Product, Sum},
    mem::swap,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

/// [`i64`] のことです。
///
/// ジェネリック型引数にしても良かったのですが、よく考えると [`i64`]
/// 以外で使うことともなさそうですから、固定してしまいました。
///
/// [`i64`]: https://doc.rust-lang.org/stable/std/primitive.i64.html
pub type ModValue = i64;

#[derive(Debug, Clone, Copy)]
struct Rational {
    num: ModValue,
    den: ModValue,
}

#[allow(clippy::many_single_char_names)]
fn red(r: i64, p: i64) -> (i64, i64, i64) {
    if r.abs() <= 10000 {
        return (r, 1, 0);
    }
    let mut nxt_r = p % r;
    let mut q = p / r;
    if 2 * nxt_r >= r {
        nxt_r -= r;
        q += 1;
    }
    if 2 * nxt_r <= -r {
        nxt_r += r;
        q -= 1;
    }
    let (x, z, y) = red(nxt_r, r);
    (x, y - q * z, z)
}

/// 本体です。
#[derive(Clone, Copy)]
pub struct Mint<Mod: ModTrait>(ModValue, std::marker::PhantomData<Mod>);

impl<Mod: ModTrait> Mint<Mod> {
    fn from_value_unchecked(value: ModValue) -> Self {
        Self(value, std::marker::PhantomData)
    }
    fn normalize(value: ModValue) -> ModValue {
        let value = value % Mod::modulus();
        if 0 <= value {
            value
        } else {
            value + Mod::modulus()
        }
    }
    fn guess(&self) -> Rational {
        let (mut num, mut den, _) = red(self.0, Mod::modulus());
        if den < 0 {
            num = -num;
            den = -den;
        }
        Rational { num, den }
    }
    /// 値を構築します。
    ///
    /// # Examples
    /// ```
    /// type Mint = modint::Mint998244353;
    /// let x = Mint::from_i64(2);
    /// ```
    pub fn from_i64(value: ModValue) -> Self {
        Self::from_value_unchecked(Self::normalize(value))
    }
    /// 分子と分母から、値を構築します。
    ///
    /// # Examples
    /// ```
    /// type Mint = modint::Mint998244353;
    /// let x = Mint::from_i64(2);
    /// ```
    pub fn from_frac(num: ModValue, den: ModValue) -> Self {
        Self::from_i64(num) / Self::from_i64(den)
    }
    /// 0
    ///
    /// # Examples
    /// ```
    /// type Mint = modint::Mint998244353;
    /// let x = Mint::zero();
    /// ```
    pub fn zero() -> Self {
        Self::from_value_unchecked(0)
    }
    /// 1
    ///
    /// # Examples
    /// ```
    /// type Mint = modint::Mint998244353;
    /// let x = Mint::one();
    /// ```
    pub fn one() -> Self {
        Self::from_value_unchecked(1)
    }
    /// 逆数を計算します。
    ///
    /// # Examples
    /// ```
    /// type Mint = modint::Mint998244353;
    /// for i in 1..30 {
    ///     let x = Mint::from_i64(i);
    ///     let y = x.inv();
    ///     assert_eq!(x * y, Mint::one());
    /// }
    /// ```
    #[allow(clippy::many_single_char_names)]
    pub fn inv(self) -> Self {
        assert_ne!(
            self,
            Self::zero(),
            "attempted to take the inverse of zero mint"
        );
        let mut x = self.0;
        let mut y = Mod::modulus();
        let mut u = 1;
        let mut v = 0;
        while x != 0 {
            let q = y / x;
            y -= q * x;
            v -= q * u;
            swap(&mut x, &mut y);
            swap(&mut u, &mut v);
        }
        assert!(x == 0 && y == 1 && u.abs() == Mod::modulus() && v.abs() < Mod::modulus());
        Self::from_value_unchecked(if v < 0 { v + Mod::modulus() } else { v })
    }
    /// 累乗を計算します。
    ///
    /// # Examples
    /// ```
    /// use modint::{mint,Mint998244353};
    /// type Mint = Mint998244353;
    /// assert_eq!(mint!(1), mint!(7).pow(0));
    /// assert_eq!(mint!(7), mint!(7).pow(1));
    /// assert_eq!(mint!(49), mint!(7).pow(2));
    /// assert_eq!(mint!(343), mint!(7).pow(3));
    /// ```
    pub fn pow(mut self, mut p: u64) -> Self {
        let mut ans = Self::one();
        while 0 != p {
            if p % 2 == 1 {
                ans *= self;
            }
            self *= self;
            p /= 2;
        }
        ans
    }
    /// `Self::from_value(a).pow(p)` をします。
    ///
    /// # Examples
    /// ```
    /// use modint::{mint,Mint998244353};
    /// type Mint = Mint998244353;
    /// assert_eq!(mint!(1), Mint::from_pow(7, 0));
    /// assert_eq!(mint!(7), Mint::from_pow(7, 1));
    /// assert_eq!(mint!(49), Mint::from_pow(7, 2));
    /// assert_eq!(mint!(343), Mint::from_pow(7, 3));
    /// ```
    pub fn from_pow(a: ModValue, p: u64) -> Self {
        Self::from_i64(a).pow(p)
    }
}

////////////////////////////////////////////////////////////////////////////////
// fmt /////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

impl<Mod: ModTrait> Debug for Mint<Mod> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let Rational { num, den } = self.guess();
        f.debug_tuple("Mint")
            .field(&if den == 1 {
                num.to_string()
            } else {
                format!("{}/{}", num, den)
            })
            .finish()
    }
}

impl<Mod: ModTrait> Display for Mint<Mod> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

////////////////////////////////////////////////////////////////////////////////
// operators ///////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

macro_rules! forward_ref_binop {
    ($(impl $imp:ident, $method:ident)*) => {
        $(
            impl<'a, Mod: ModTrait> $imp<Mint<Mod>> for &'a Mint<Mod> {
                type Output = Mint<Mod>;

                #[inline]
                fn $method(self, other: Mint<Mod>) -> Self::Output {
                    $imp::$method(*self, other)
                }
            }

            impl<'a, Mod: ModTrait> $imp<&'a Mint<Mod>> for Mint<Mod> {
                type Output = Mint<Mod>;

                #[inline]
                fn $method(self, other: &Mint<Mod>) -> Self::Output {
                    $imp::$method(self, *other)
                }
            }

            impl<'a, Mod: ModTrait> $imp<&'a Mint<Mod>> for &'a Mint<Mod> {
                type Output = Mint<Mod>;

                #[inline]
                fn $method(self, other: &Mint<Mod>) -> Self::Output {
                    $imp::$method(*self, *other)
                }
            }
        )*
    };
}

macro_rules! forward_ref_op_assign {
    ($(impl $imp:ident, $method:ident)*) => {
        $(
            impl<'a, Mod: ModTrait> $imp<&Mint<Mod>> for Mint<Mod> {
                #[inline]
                fn $method(&mut self, other: &Mint<Mod>) {
                    $imp::$method(self, *other);
                }
            }
        )*
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<Mod: ModTrait> Add for Mint<Mod> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        let value = self.0 + rhs.0;
        Self::from_value_unchecked(if value < Mod::modulus() {
            value
        } else {
            value - Mod::modulus()
        })
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<Mod: ModTrait> Sub for Mint<Mod> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        let value = self.0 - rhs.0;
        Self::from_value_unchecked(if 0 <= value {
            value
        } else {
            value + Mod::modulus()
        })
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<Mod: ModTrait> Mul for Mint<Mod> {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::from_value_unchecked(self.0 * rhs.0 % Mod::modulus())
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<Mod: ModTrait> Div for Mint<Mod> {
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl<Mod: ModTrait> Neg for Mint<Mod> {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if self.0 == 0 {
            Self::zero()
        } else {
            Self::from_value_unchecked(Mod::modulus() - self.0)
        }
    }
}

impl<Mod: ModTrait> Neg for &Mint<Mod> {
    type Output = Mint<Mod>;

    #[inline]
    fn neg(self) -> Self::Output {
        (*self).neg()
    }
}

macro_rules! forward_assign_biop {
    ($(impl $trait: ident, $fn_assign: ident, $fn: ident)*) => {
        $(
            impl<Mod: ModTrait> $trait for Mint<Mod> {
                #[inline]
                fn $fn_assign(&mut self, rhs: Self) {
                    *self = self.$fn(rhs);
                }
            }
        )*
    };
}

forward_assign_biop! {
    impl AddAssign, add_assign, add
    impl SubAssign, sub_assign, sub
    impl MulAssign, mul_assign, mul
    impl DivAssign, div_assign, div
}

forward_ref_binop! {
    impl Add, add
    impl Sub, sub
    impl Mul, mul
    impl Div, div
}

forward_ref_op_assign! {
    impl AddAssign, add_assign
    impl SubAssign, sub_assign
    impl MulAssign, mul_assign
    impl DivAssign, div_assign
}

////////////////////////////////////////////////////////////////////////////////
// comparisons  ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

impl<Mod: ModTrait> PartialEq for Mint<Mod> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}
impl<Mod: ModTrait> Eq for Mint<Mod> {}
impl<Mod: ModTrait> Ord for Mint<Mod> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}
impl<Mod: ModTrait> PartialOrd for Mint<Mod> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

////////////////////////////////////////////////////////////////////////////////
// conversions  ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

impl<Mod: ModTrait> From<ModValue> for Mint<Mod> {
    fn from(value: ModValue) -> Self {
        Self::from_i64(value)
    }
}

impl<Mod: ModTrait> From<Mint<Mod>> for ModValue {
    fn from(mint: Mint<Mod>) -> Self {
        mint.0
    }
}

////////////////////////////////////////////////////////////////////////////////
// sum / product ///////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

impl<Mod: ModTrait> Sum for Mint<Mod> {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(Self::zero(), Add::add)
    }
}
impl<'a, Mod: 'a + ModTrait> Sum<&'a Self> for Mint<Mod> {
    fn sum<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Self>,
    {
        iter.fold(Self::zero(), Add::add)
    }
}
impl<Mod: ModTrait> Product for Mint<Mod> {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = Self>,
    {
        iter.fold(Self::one(), Mul::mul)
    }
}
impl<'a, Mod: 'a + ModTrait> Product<&'a Self> for Mint<Mod> {
    fn product<I>(iter: I) -> Self
    where
        I: Iterator<Item = &'a Self>,
    {
        iter.fold(Self::one(), Mul::mul)
    }
}

////////////////////////////////////////////////////////////////////////////////
// macros //////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// [`Mint::from_i64`] を呼びます。
///
/// # Examples
///
/// パスを指定していないため、そのとき `use` されているものが選ばれます。
///
/// ```
/// use modint::{Mint, mint, Mint100000007, Mint998244353};
/// let x: Mint998244353 = mint!(0);
/// let y: Mint100000007 = mint!(0);
/// ```
///
/// `use` していないときには、コンパイルエラーになります。
///
/// ```compile_fail
/// use modint::{mint, Mint998244353};
/// let x: Mint998244353 = mint!(0);
/// ```
///
/// `use` していても、型矯正がなければ ambiguous ですから、コンパイルエラーになります。
///
/// ```compile_fail
/// use modint::{mint, Mint, Mint998244353};
/// let x = mint!(0);
/// ```
///
/// また、これが想定した使い方なのですが、型別名をつけておくことで、それを呼ぶことができます。
/// ```
/// use modint::{mint, Mint998244353};
/// type Mint = Mint998244353;
/// let x = mint!(0);
/// ```
///
/// こういうとても邪悪な使い方もできるのですが、想定された使い方ではありません。
/// ```
/// use modint::mint;
/// struct Mint {}
/// impl Mint {
///     pub fn from_i64(name: &'static str) -> String {
///         format!("hello, {}", name)
///     }
/// }
/// assert_eq!(mint!("genius"), "hello, genius".to_string());
/// ```
///
///
/// [`Mint::from_i64`]: struct.Mint#method.from_i64
#[macro_export]
macro_rules! mint {
    ($value: expr) => {
        Mint::from_i64($value)
    };
}

/// [`Mint::from_frac`] を呼びます。
/// 使用は概ね [`mint`] と同様ですから、そちらをご覧いただけるとです。
///
/// # Examples
///
/// ```
/// use modint::{from_frac, mint, Mint998244353};
/// type Mint = Mint998244353;
/// let x = from_frac!(5, 12);
/// let y = from_frac!(12, 5);
/// assert_eq!(x * y, mint!(1));
/// ```
///
/// [`mint`]: macro.mint.html
/// [`Mint::from_frac`]: struct.Mint#method.from_frac
#[macro_export]
macro_rules! from_frac {
    ($num: expr, $den: expr) => {
        Mint::from_frac($num, $den)
    };
}

/// [`Mint::from_pow`] を呼びます。
/// 使用は概ね [`mint`] と同様ですから、そちらをご覧いただけるとです。
///
/// # Examples
///
/// ```
/// use modint::{from_pow, mint, Mint998244353};
/// type Mint = Mint998244353;
/// let x = from_pow!(5, 3);
/// assert_eq!(x, mint!(125));
/// ```
///
/// [`mint`]: macro.mint.html
/// [`Mint::from_pow`]: struct.Mint#method.from_pow
#[macro_export]
macro_rules! from_pow {
    ($a: expr, $b: expr) => {
        Mint::from_pow($a, $b)
    };
}

////////////////////////////////////////////////////////////////////////////////
// customization ///////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// mod の情報を持っています。
///
/// # How to implement this trait
///
/// [`modulus`] メソッドを実装すると良いです。
/// 注意点なのですが、このトレイトは [`Debug`], [`Clone`], [`Copy`]
/// を継承していますから、それも忘れず実装です。
///
/// ```
/// use modint::ModTrait;
/// #[derive(Debug, Clone, Copy)]
/// struct Mod17 {}
/// impl ModTrait for Mod17 {
///     fn modulus() -> i64 {
///         17
///     }
/// }
/// assert_eq!(Mod17::modulus(), 17);
/// ```
/// [`modulus`]: trait.ModTrait#tymethod.modulus
/// [`Debug`]: https://doc.rust-lang.org/stable/std/fmt/trait.Debug.html
/// [`Clone`]: https://doc.rust-lang.org/stable/std/clone/trait.Clone.html
/// [`Copy`]: https://doc.rust-lang.org/stable/std/marker/trait.Copy.html
pub trait ModTrait: Clone + Copy + Debug {
    /// mod を返します。
    fn modulus() -> ModValue;
}

////////////////////////////////////////////////////////////////////////////////
// precalculation utils ////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// 階乗の前計算をします。
///
/// # How to use
///
/// ジェネリックパラメータに若干癖があるのですが、[`Mint`] ではなくてその中身を入れます。
/// [`with_len`] で構築をして、[`index`] で取得です。
///
/// ```
/// use modint::{mint, Mod998244353, Mint998244353};
/// type Mint = Mint998244353;
/// type Factorial = modint::Factorial<modint::Mod998244353>;
///
/// let fact = Factorial::with_len(20);
/// assert_eq!(fact[3], mint!(6));                      // 階乗です。
/// assert_eq!(fact.inv(3), mint!(6).inv());            // 階乗の逆元です。
/// assert_eq!(fact.falling(8, 3), mint!(8 * 7 * 6));   // falling factorial です。
/// assert_eq!(fact.binom(8, 3), mint!(56));            // binomial coefficient です。
/// ```
///
/// [`with_len`]: struct.Factorial#method.with_len.html
/// [`Mint`]: struct.Mint.html
///
/// [`index`]: https://doc.rust-lang.org/nightly/core/ops/trait.Index.html#tymethod.index
#[derive(Debug, Clone)]
pub struct Factorial<Mod: ModTrait> {
    normal: Vec<Mint<Mod>>,
    inverse: Vec<Mint<Mod>>,
}

impl<Mod: ModTrait> Factorial<Mod> {
    /// 空ならば `true` です。
    ///
    /// # Examples
    ///
    /// ```
    /// type Factorial = modint::Factorial<modint::Mod998244353>;
    /// assert!(Factorial::with_len(0).is_empty());
    /// assert!(!Factorial::with_len(2).is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.normal.is_empty()
    }
    /// 長さを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// type Factorial = modint::Factorial<modint::Mod998244353>;
    /// assert_eq!(Factorial::with_len(0).len(), 0);
    /// assert_eq!(Factorial::with_len(2).len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.normal.len()
    }
    /// 構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// modint::Factorial::<modint::Mod998244353>::with_len(42);
    /// ```
    pub fn with_len(len: usize) -> Self {
        if len == 0 {
            Self {
                normal: Vec::new(),
                inverse: Vec::new(),
            }
        } else {
            let mut normal = vec![Mint::one(); len];
            for i in 1..len {
                normal[i] = normal[i - 1] * Mint::from_i64(i as i64);
            }
            let mut inverse = vec![normal.last().unwrap().inv(); len];
            for i in (1..len).rev() {
                inverse[i - 1] = inverse[i] * Mint::from_i64(i as i64);
            }
            Self { normal, inverse }
        }
    }
    /// 階乗の逆元を取得です。
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{mint, Factorial, Mod998244353, Mint998244353};
    /// type Mint = Mint998244353;
    /// let fact = Factorial::<Mod998244353>::with_len(20);
    /// assert_eq!(fact.inv(3), mint!(6).inv());
    /// ```
    pub fn inv(&self, i: usize) -> Mint<Mod> {
        self.inverse[i]
    }
    /// 下方階乗です。
    ///
    /// # Requirements
    ///
    /// 次のいずれかが成り立っている必要があります。
    /// 1. `p == 0`,
    /// 2. `n < p`,
    /// 3. `n < self.len()`.
    ///
    /// # Returns
    ///
    /// 1. `1`
    /// 2. `0`
    /// 3. `n * (n - 1) * ... * (n - p + 1)`
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{mint, Factorial, Mod998244353, Mint998244353};
    /// type Mint = Mint998244353;
    /// let fact = Factorial::<Mod998244353>::with_len(20);
    /// assert_eq!(fact.falling(8, 3), mint!(8 * 7 * 6));
    /// ```
    pub fn falling(&self, n: usize, p: usize) -> Mint<Mod> {
        if p == 0 {
            Mint::one()
        } else if n < p {
            Mint::zero()
        } else {
            self[n] * self.inv(n - p)
        }
    }
    /// 二項係数です。
    ///
    /// # Requirements
    ///
    /// 次のいずれかが成り立っている必要があります。
    /// 1. `p == k`,
    /// 2. `n < k`,
    /// 3. `n < self.len()`.
    ///
    /// # Returns
    ///
    /// 1. `1`
    /// 2. `0`
    /// 3. `n * (n - 1) * ... * (n - p + 1) / `
    ///
    /// # Examples
    ///
    /// ```
    /// use modint::{mint, Factorial, Mod998244353, Mint998244353};
    /// type Mint = Mint998244353;
    /// let fact = Factorial::<Mod998244353>::with_len(20);
    /// assert_eq!(fact.binom(8, 3), mint!(56));
    /// ```
    pub fn binom(&self, n: usize, k: usize) -> Mint<Mod> {
        if k == 0 {
            Mint::one()
        } else if n < k {
            Mint::zero()
        } else {
            self[n] * self.inv(n - k) * self.inv(k)
        }
    }
}

impl<Mod: ModTrait, I: std::slice::SliceIndex<[Mint<Mod>]>> std::ops::Index<I> for Factorial<Mod> {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        &self.normal[index]
    }
}

////////////////////////////////////////////////////////////////////////////////
// specializations /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////

/// よく使う mod さんです。
#[derive(Clone, Copy, Debug)]
pub struct Mod100000007 {}
/// よく使う mod さんです。
#[derive(Clone, Copy, Debug)]
pub struct Mod998244353 {}
impl ModTrait for Mod100000007 {
    fn modulus() -> ModValue {
        1_000_000_007
    }
}
impl ModTrait for Mod998244353 {
    fn modulus() -> ModValue {
        998_244_353
    }
}
/// よく使う [`Mint`] さんです。
///
/// [`Mint`]: struct.Mint.html
pub type Mint100000007 = Mint<Mod100000007>;

/// よく使う [`Mint`] さんです。
///
/// [`Mint`]: struct.Mint.html
pub type Mint998244353 = Mint<Mod998244353>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_debug_integral() {
        type Mint = Mint998244353;
        for i in 1..100 {
            let x = Mint::from_i64(i);
            assert_eq!(format!("{:?}", x), format!("Mint(\"{}\")", i));
            println!("{:?}", x);
        }
    }

    #[test]
    fn test_display_integral() {
        type Mint = Mint998244353;
        for i in 1..100 {
            let x = Mint::from_i64(i);
            assert_eq!(format!("{}", x), format!("{}", i));
            println!("{}", x);
        }
    }

    #[test]
    fn test_debug_rational() {
        fn gcd(mut x: i64, mut y: i64) -> i64 {
            if x > y {
                swap(&mut x, &mut y);
            }
            if x == 0 {
                y
            } else {
                gcd(y % x, x)
            }
        }
        type Mint = Mint998244353;
        for den in 2..20 {
            for num in (1..20).filter(|&num| gcd(num, den) == 1) {
                let x = Mint::from_frac(num, den);
                assert_eq!(format!("{:?}", x), format!("Mint(\"{}/{}\")", num, den));
                println!("{:?}", x);
            }
        }
    }

    #[test]
    fn test_display_rational() {
        fn gcd(mut x: i64, mut y: i64) -> i64 {
            if x > y {
                swap(&mut x, &mut y);
            }
            if x == 0 {
                y
            } else {
                gcd(y % x, x)
            }
        }
        type Mint = Mint998244353;
        for den in 2..20 {
            for num in (1..20).filter(|&num| gcd(num, den) == 1) {
                let x = Mint::from_frac(num, den);
                assert_eq!(format!("{}", x), format!("{}", x.0));
                println!("{}", x);
            }
        }
    }
}
