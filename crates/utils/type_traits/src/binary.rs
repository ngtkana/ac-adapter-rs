use super::{Assoc, Element, Identity, One, Peek, Zero};
use std::ops;

macro_rules! triv_wrapper {
    ($name:ident<$T:ident>) => {
        impl<$T> Peek for $name<$T>
        where
            $T: Element,
        {
            type Inner = $T;
            fn peek(&self) -> $T {
                self.0.clone()
            }
        }
    };
}

/// `ops::Add` を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Add<T>(pub T);
triv_wrapper! { Add<T> }
impl<T> Assoc for Add<T>
where
    T: ops::Add<Output = T> + Element,
{
    fn op(self, rhs: Self) -> Self {
        Add(self.0 + rhs.0)
    }
}
impl<T> Identity for Add<T>
where
    T: Zero,
{
    fn identity() -> Self {
        Add(T::zero())
    }
}

/// `ops::Mul` を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Mul<T>(pub T);
triv_wrapper! { Mul<T> }
impl<T> Assoc for Mul<T>
where
    T: ops::Mul<Output = T> + Element,
{
    fn op(self, rhs: Self) -> Self {
        Mul(self.0 * rhs.0)
    }
}
impl<T> Identity for Mul<T>
where
    T: One,
{
    fn identity() -> Self {
        Mul(T::one())
    }
}

/// 転倒数を演算として、[`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct InvertionNumber {
    zero: u64,
    one: u64,
    invertion: u64,
}
impl Peek for InvertionNumber {
    type Inner = bool;
    fn peek(&self) -> bool {
        self.try_get_bool()
            .expect("ビットでないものを peek するのはいけません！")
    }
}
impl Assoc for InvertionNumber {
    fn op(self, rhs: Self) -> Self {
        InvertionNumber {
            zero: self.zero + rhs.zero,
            one: self.one + rhs.one,
            invertion: self.invertion + self.one * rhs.zero + rhs.invertion,
        }
    }
}
impl Identity for InvertionNumber {
    fn identity() -> Self {
        InvertionNumber::new()
    }
}
impl InvertionNumber {
    /// 空文字列に対応する転倒数です。
    pub fn new() -> Self {
        InvertionNumber {
            zero: 0,
            one: 0,
            invertion: 0,
        }
    }
    /// ビットならば 0 か 1 を、そうでなければ `None` を返します。
    pub fn try_get_u8(&self) -> Option<u8> {
        self.try_get_bool().map(|b| if b { 1 } else { 0 })
    }
    /// ビットならば 0 は `false`、1 は `ture` にして、そうでなければなければ `None` を返します。
    pub fn try_get_bool(&self) -> Option<bool> {
        if *self == Self::bit_zero() {
            Some(false)
        } else if *self == Self::bit_one() {
            Some(true)
        } else {
            None
        }
    }
    /// 0 の個数を返します。
    pub fn count_zeros(&self) -> u64 {
        self.zero
    }
    /// 1 の個数を返します。
    pub fn count_ones(&self) -> u64 {
        self.one
    }
    /// 転倒数を返します。
    pub fn inversion_number(&self) -> u64 {
        self.invertion
    }
    /// ビット 0 に対応する転倒数です。
    pub fn bit_zero() -> Self {
        InvertionNumber {
            zero: 1,
            one: 0,
            invertion: 0,
        }
    }
    /// ビット 1 に対応する転倒数です。
    pub fn bit_one() -> Self {
        InvertionNumber {
            zero: 0,
            one: 1,
            invertion: 0,
        }
    }
    /// `false` ならばビット 0、`true` ならばビット 1 を構築します。
    pub fn from_bool(b: bool) -> Self {
        if b {
            Self::bit_one()
        } else {
            Self::bit_zero()
        }
    }
    /// 0 ならばビット 0、1 ならばビット 1 を構築します。
    ///
    /// # Panics
    ///
    /// 0 でも 1 でもないものを渡すとパニックです。
    pub fn from_u8(x: u8) -> Self {
        match x {
            0 => Self::bit_zero(),
            1 => Self::bit_one(),
            _ => panic!("0 でも 1 でもないものを渡すとパニックです。"),
        }
    }
}

/// [`ops::Add`], [`ops::Mul`] によるアフィン変換の合成で [`Assoc`], [`Ideneity`]
/// を実装するラッパーです。
///
/// [`ops::Add`]: http://doc.rust-lang.org/std/ops/trait.Add.html
/// [`ops::Mul`]: http://doc.rust-lang.org/std/ops/trait.Mul.html
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Affine<T> {
    /// 1 次の係数です。
    pub a: T,
    /// 0 次の係数です。
    pub b: T,
}
impl<T: Element> Peek for Affine<T> {
    type Inner = (T, T);
    fn peek(&self) -> (T, T) {
        (self.a.clone(), self.b.clone())
    }
}
impl<T> Assoc for Affine<T>
where
    T: ops::Add<Output = T> + Element,
    T: ops::Mul<Output = T> + Element,
{
    fn op(self, rhs: Self) -> Self {
        Self {
            a: self.a.clone() * rhs.a,
            b: self.b + self.a * rhs.b,
        }
    }
}
impl<T> Identity for Affine<T>
where
    T: Zero + One,
{
    fn identity() -> Self {
        Self {
            a: T::one(),
            b: T::zero(),
        }
    }
}

/// 文字列結合を演算として [`String`] に [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`String`]: http://doc.rust-lang.org/std/str/struct.String.html
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Cat(pub String);
impl Peek for Cat {
    type Inner = String;
    fn peek(&self) -> String {
        self.0.clone()
    }
}
impl Assoc for Cat {
    fn op(self, rhs: Self) -> Self {
        Cat(self.0.chars().chain(rhs.0.chars()).collect())
    }
}
impl Identity for Cat {
    fn identity() -> Self {
        Cat(String::new())
    }
}
