use super::{Assoc, Commut, Element, Identity, MaxValue, MinValue, One, OpN, Peek, Zero};
use std::ops;

/// 長さの情報を追加するラッパーです。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Len<T> {
    /// 元の長さです。
    pub len: u64,
    /// 中身です。
    pub base: T,
}
impl<T> Len<T> {
    /// 長さ 1 を付与します。
    pub fn single(base: T) -> Self {
        Len { len: 1, base }
    }
}
impl<T: Assoc> Assoc for Len<T> {
    fn op(self, rhs: Self) -> Self {
        Len {
            len: self.len + rhs.len,
            base: self.base.op(rhs.base),
        }
    }
}

/// 1 付加です。
impl<T: Peek> Peek for Option<T> {
    type Inner = Option<T::Inner>;
    fn peek(&self) -> Self::Inner {
        self.as_ref().map(T::peek)
    }
}
impl<T: Assoc> Assoc for Option<T> {
    fn op(self, rhs: Self) -> Self {
        match (self, rhs) {
            (Some(x), Some(y)) => Some(x.op(y)),
            (Some(x), None) => Some(x),
            (None, Some(y)) => Some(y),
            (None, None) => None,
        }
    }
}
impl<T: Assoc> Identity for Option<T> {
    fn identity() -> Self {
        None
    }
}

/// 直積です。
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Pair<T, U>(pub T, pub U);
impl<T: Assoc, U: Assoc> Assoc for Pair<T, U> {
    fn op(self, rhs: Self) -> Self {
        Pair(self.0.op(rhs.0), self.1.op(rhs.1))
    }
}
impl<T: Identity, U: Identity> Identity for Pair<T, U> {
    fn identity() -> Self {
        Pair(T::identity(), U::identity())
    }
}
impl<T: Commut, U: Commut> Commut for Pair<T, U> {}
impl<T: OpN, U: OpN> OpN for Pair<T, U> {
    fn op_n(self, n: u64) -> Self {
        let Pair(t, u) = self;
        Self(t.op_n(n), u.op_n(n))
    }
}

/// `ops::BitXor` を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct BitXor<T>(pub T);
triv_wrapper! { BitXor<T> }
impl<T> Assoc for BitXor<T>
where
    T: ops::BitXor<Output = T> + Element,
{
    fn op(self, rhs: Self) -> Self {
        BitXor(self.0 ^ rhs.0)
    }
}
impl<T> Identity for BitXor<T>
where
    T: ops::BitXor<Output = T> + Zero,
{
    fn identity() -> Self {
        BitXor(T::zero())
    }
}
impl<T: ops::BitXor<Output = T> + Element> Commut for BitXor<T> {}
impl<T: ops::BitXor<Output = T> + Zero> OpN for BitXor<T> {
    fn op_n(self, n: u64) -> Self {
        if n % 2 == 0 {
            Self::identity()
        } else {
            self
        }
    }
}

/// 常に左側を返すを演算で [`Assoc`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Left<T>(pub T);
triv_wrapper! { Left<T> }
impl<T: Element> Assoc for Left<T> {
    fn op(self, _rhs: Self) -> Self {
        self
    }
}

/// 常に右側を返すを演算で [`Assoc`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Right<T>(pub T);
triv_wrapper! { Right<T> }
impl<T: Element> Assoc for Right<T> {
    fn op(self, rhs: Self) -> Self {
        rhs
    }
}

/// Min を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Min<T>(pub T);
triv_wrapper! { Min<T> }
impl<T> Assoc for Min<T>
where
    T: Ord + Element,
{
    fn op(self, rhs: Self) -> Self {
        Min(self.0.min(rhs.0))
    }
}
impl<T> Identity for Min<T>
where
    T: MaxValue,
{
    fn identity() -> Self {
        Min(T::max_value())
    }
}

/// Max を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
///
/// [`Assoc`]: traits.Assoc.html
/// [`Identity`]: traits.Identity.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Max<T>(pub T);
triv_wrapper! { Max<T> }
impl<T> Assoc for Max<T>
where
    T: Ord + Element,
{
    fn op(self, rhs: Self) -> Self {
        Max(self.0.max(rhs.0))
    }
}
impl<T> Identity for Max<T>
where
    T: MinValue,
{
    fn identity() -> Self {
        Max(T::min_value())
    }
}

/// 加法を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
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

/// 乗法を演算として [`Assoc`], [`Identity`] を実装するラッパーです。
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
    /// 0 の数
    pub zero: u64,
    /// 1 の数
    pub one: u64,
    /// 転倒数
    pub invertion: u64,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[cfg(test)]
mod tests {
    use super::*;
    use assert_impl::assert_impl;

    #[test]
    fn test_option_left() {
        assert_impl!(Assoc: Left<u32>, Option<Left<u32>>);
        assert_impl!(!Identity: Left<u32>);
        assert_impl!(Identity: Option<Left<u32>>);

        assert_eq!(Left(3).op(Left(2)), Left(3));
        assert_eq!(Some(Left(3)).op(Some(Left(2))), Some(Left(3)));
        assert_eq!(None.op(Some(Left(2))), Some(Left(2)));
        assert_eq!(<Option::<Left<u32>> as Identity>::identity(), None);
    }

    #[test]
    fn test_pair() {
        assert_eq!(
            Pair(Add(3), Mul(5.)).op(Pair(Add(5), Mul(2.))),
            Pair(Add(8), Mul(10.))
        );
        assert_eq!(
            Pair::<Add<u32>, Mul<f64>>::identity(),
            Pair(Add(0), Mul(1.))
        );
    }

    #[test]
    fn test_add() {
        assert_impl!(Assoc: Add<i64>, Add<f64>);
        assert_impl!(!Assoc: Add<()>, Add<std::cmp::Reverse<i64>>);

        assert_impl!(Identity: Add<i64>, Add<f64>);
        assert_impl!(Commut: Add<i64>, Add<f64>);
        assert_impl!(OpN: Add<i64>, Add<f64>);

        assert_impl!(Ord: Add<i64>);
        assert_impl!(!Ord: Add<f64>);

        assert_eq!(Add(2).op(Add(3)), Add(5));
        assert_eq!(Add(2.).op(Add(3.)), Add(5.));
        assert_eq!(Add::<u8>::identity(), Add(0));
        assert_eq!(Add::<f32>::identity(), Add(0.));
        assert_eq!(Add(42).op_n(3), Add(126));
        assert_eq!(Add(3.).op_n(6), Add(18.));
    }

    #[test]
    fn test_mul() {
        assert_impl!(Assoc: Mul<i64>, Mul<f64>);
        assert_impl!(!Assoc: Mul<()>, Mul<std::cmp::Reverse<i64>>);

        assert_impl!(Identity: Mul<i64>, Mul<f64>);
        assert_impl!(Commut: Mul<i64>, Mul<f64>);
        assert_impl!(!OpN: Mul<i64>, Mul<f64>);

        assert_impl!(Ord: Mul<i64>);
        assert_impl!(!Ord: Mul<f64>);

        assert_eq!(Mul(2).op(Mul(3)), Mul(6));
        assert_eq!(Mul(2.).op(Mul(3.)), Mul(6.));
        assert_eq!(Mul::<u8>::identity(), Mul(1));
        assert_eq!(Mul::<f32>::identity(), Mul(1.));
    }

    #[test]
    fn test_inversion_number() {
        assert_impl!(Assoc: InvertionNumber);
        assert_impl!(Identity: InvertionNumber);
        assert_impl!(!Commut: InvertionNumber);
        assert_impl!(!OpN: InvertionNumber);
        assert_impl!(!Ord: InvertionNumber);

        assert_eq!(
            InvertionNumber::identity(),
            InvertionNumber {
                zero: 0,
                one: 0,
                invertion: 0
            }
        );
        assert_eq!(
            InvertionNumber {
                zero: 1,
                one: 2,
                invertion: 1
            }
            .op(InvertionNumber {
                zero: 3,
                one: 4,
                invertion: 1
            }),
            InvertionNumber {
                zero: 4,
                one: 6,
                invertion: 8
            }
        );
    }

    #[test]
    fn test_affine() {
        assert_impl!(Assoc: Affine<i64>, Affine<f64>);
        assert_impl!(!Assoc: Affine<()>, Affine<std::cmp::Reverse<i64>>);

        assert_impl!(Identity: Affine<i64>, Affine<f64>);
        assert_impl!(!Commut: Affine<i64>, Affine<f64>);
        assert_impl!(!OpN: Affine<i64>, Affine<f64>);

        assert_impl!(!Ord: Affine<i64>, Affine<f64>);

        assert_eq!(
            Affine { a: 2, b: 3 }.op(Affine { a: 10, b: 20 }),
            Affine { a: 20, b: 43 }
        );
        assert_eq!(
            Affine { a: 2., b: 3. }.op(Affine { a: 10., b: 20. }),
            Affine { a: 20., b: 43. }
        );
        assert_eq!(Affine::<u8>::identity(), Affine { a: 1, b: 0 });
        assert_eq!(Affine::<f32>::identity(), Affine { a: 1., b: 0. });
    }
}
