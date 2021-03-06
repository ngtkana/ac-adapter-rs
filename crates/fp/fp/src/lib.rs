//! 有限体
//!
//!
//! # 使い方
//!
//! ```
//! use fp::F998244353 as Fp;
//!
//! // 四則演算
//! assert_eq!(Fp::new(6) + Fp::new(2), Fp::new(8));
//! assert_eq!(Fp::new(6) - Fp::new(2), Fp::new(4));
//! assert_eq!(Fp::new(6) * Fp::new(2), Fp::new(12));
//! assert_eq!(Fp::new(6) / Fp::new(2), Fp::new(3));
//!
//! // pow: 指数は Into<u32> なので符号なし型なら OK
//! assert_eq!(Fp::new(6).pow(2u32), Fp::new(36));
//!
//! // recip: よく inv と呼ばれているもの
//! assert_eq!(Fp::new(2).recip(), Fp::new(499122177));
//!
//! // sum, product: 値型でも参照型でも OK
//! assert_eq!([Fp::new(2), Fp::new(3), Fp::new(4)].iter().sum::<Fp>(), Fp::new(9));
//! assert_eq!([Fp::new(2), Fp::new(3), Fp::new(4)].iter().product::<Fp>(), Fp::new(24));
//!
//! // debug: それらしい分数で表示します。
//! assert_eq!(format!("{:?}", Fp::new(4)).as_str(), "4");
//! assert_eq!(format!("{:?}", Fp::new(4).recip()).as_str(), "1/4");
//! assert_eq!(format!("{:?}", Fp::from(-4)).as_str(), "-4");
//! assert_eq!(format!("{:?}", Fp::from(-4).recip()).as_str(), "-1/4");
//! ```

use std::{
    cmp::PartialEq,
    fmt,
    hash::{Hash, Hasher},
    iter::{Product, Sum},
    marker::PhantomData,
    mem::swap,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

/// [`Fp`] の型引数
pub trait Mod: Clone + Copy + Hash {
    /// 法（2 ^ 30 未満。）
    const P: u32;
    /// -P mod 2 ^ 32（モンゴメリ乗算用）
    const K: u32;
    /// 2 ^ 64 mod P（モンゴメリ乗算用）
    const R2: u32 = ((1u128 << 64) % Self::P as u128) as _; // 2 ^ 64 mod P
}
fn reduce<M: Mod>(x: u64) -> u32 {
    ((x + M::K.wrapping_mul(x as u32) as u64 * M::P as u64) >> 32) as u32
}

/// 新しい mod を定義するためのマクロ
///
/// # 例
///
/// ```
/// use fp::{Fp, Mod, define_mod}; // Fp を use する必要あり。(procon-bundler 都合で $crate:: できず）
///
/// define_mod! {
///     (F998244353, Mod998244353, 998_244_353, 998_244_351),
///     (F1000000007, Mod1000000007, 1_000_000_007, 2_226_617_417),
///     (F1012924417, Mod1012924417, 1_012_924_417, 1_012_924_415),
///     (F924844033, Mod924844033, 924_844_033, 924_844_031),
/// }
/// ```
#[macro_export]
macro_rules! define_mod {
    ($(($Fp: ident, $Mod: ident, $mod: expr, $k: expr),)*) => {$(
        /// Mod 型
        #[derive(Clone, Debug, Default, Hash, Copy)]
        pub struct $Mod {}
        impl Mod for $Mod {
            const P: u32 = $mod;
            const K: u32 = $k;
        }
        /// 有限体
        pub type $Fp = Fp<$Mod>;
    )*}
}
define_mod! {
    (F998244353, Mod998244353, 998_244_353, 998_244_351),
    (F1000000007, Mod1000000007, 1_000_000_007, 2_226_617_417),
    (F1012924417, Mod1012924417, 1_012_924_417, 1_012_924_415),
    (F924844033, Mod924844033, 924_844_033, 924_844_031),
}

/// 有限体（型引数を取る）
#[derive(Clone, Default, Copy)]
pub struct Fp<M> {
    value: u32,
    __marker: PhantomData<M>,
}
impl<M: Mod> Fp<M> {
    /// 法
    pub const P: u32 = M::P;
    /// 新しく構築します。
    pub fn new(value: u32) -> Self {
        Fp::from_raw(reduce::<M>(value as u64 * M::R2 as u64))
    }
    /// オブジェクトの表す整数を返します。
    pub fn value(self) -> u32 {
        let x = reduce::<M>(self.value as _);
        if M::P <= x {
            x - M::P
        } else {
            x
        }
    }
    /// 逆数を返します。
    #[allow(clippy::many_single_char_names)]
    pub fn recip(self) -> Self {
        let mut x = M::P as i32;
        let mut y = self.value() as i32;
        let mut u = 0;
        let mut v = 1;
        while y != 0 {
            let q = x / y;
            x -= q * y;
            u -= q * v;
            swap(&mut x, &mut y);
            swap(&mut u, &mut v);
        }
        debug_assert_eq!(x, 1);
        if u < 0 {
            debug_assert_eq!(v, M::P as i32);
            u += v;
        }
        Self::new(u as u32)
    }
    /// 冪
    pub fn pow<T: Into<u64>>(self, exp: T) -> Self {
        let mut exp = exp.into();
        if exp == 0 {
            return Fp::new(1);
        }
        let mut base = self;
        let mut acc = Fp::new(1);
        while 1 < exp {
            if exp & 1 == 1 {
                acc *= base;
            }
            exp /= 2;
            base *= base;
        }
        acc * base
    }
    fn from_raw(value: u32) -> Self {
        Self {
            value,
            __marker: PhantomData,
        }
    }
}
fn simplify(value: i32, p: i32) -> (i32, i32, i32) {
    if value.abs() < 10_000 {
        (value, 1, 0)
    } else {
        let mut q = p.div_euclid(value);
        let mut r = p.rem_euclid(value);
        if value <= 2 * r {
            q += 1;
            r -= value;
        }
        let (num, pden, ppden) = simplify(r, value);
        let den = ppden - q * pden;
        (num, den, pden)
    }
}
macro_rules! impl_from_large_int {
    ($($T: ty), *$(,)?) => {$(
        impl<M: Mod> From<$T> for Fp<M> {
            fn from(x: $T) -> Self {
                Self::new(x.rem_euclid(M::P as _) as u32)
            }
        }
    )*}
}
impl_from_large_int! {
    u32, u64, u128, usize,
    i32, i64, i128, isize,
}
macro_rules! impl_from_small_int {
    ($($T: ty), *$(,)?) => {$(
        impl<M: Mod> From<$T> for Fp<M> {
            fn from(x: $T) -> Self {
                Self::new(x as u32)
            }
        }
    )*}
}
impl_from_small_int! {
    u8, u16,
    i8, i16,
}

impl<M: Mod> PartialEq for Fp<M> {
    fn eq(&self, other: &Self) -> bool {
        fn value<M: Mod>(fp: Fp<M>) -> u32 {
            if fp.value >= M::P {
                fp.value - M::P
            } else {
                fp.value
            }
        }
        value(*self) == value(*other)
    }
}
impl<M: Mod> Eq for Fp<M> {}
impl<M: Mod> Hash for Fp<M> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value().hash(state);
    }
}
impl<M: Mod, T: Into<Fp<M>>> AddAssign<T> for Fp<M> {
    fn add_assign(&mut self, rhs: T) {
        self.value += rhs.into().value;
        if M::P * 2 <= self.value {
            self.value -= M::P * 2;
        }
    }
}
impl<M: Mod, T: Into<Fp<M>>> SubAssign<T> for Fp<M> {
    fn sub_assign(&mut self, rhs: T) {
        let rhs = rhs.into();
        if self.value < rhs.value {
            self.value += M::P * 2;
        }
        self.value -= rhs.value;
    }
}
impl<M: Mod, T: Into<Fp<M>>> MulAssign<T> for Fp<M> {
    fn mul_assign(&mut self, rhs: T) {
        self.value = reduce::<M>(self.value as u64 * rhs.into().value as u64);
    }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl<M: Mod, T: Into<Fp<M>>> DivAssign<T> for Fp<M> {
    fn div_assign(&mut self, rhs: T) {
        *self *= rhs.into().recip();
    }
}

macro_rules! forward_ops {
    ($(($trait:ident, $method_assign:ident, $method:ident),)*) => {$(
        impl<M: Mod> $trait for Fp<M> {
            type Output = Self;
            fn $method(mut self, rhs: Self) -> Self {
                self.$method_assign(rhs);
                self
            }
        }
        impl<'a, T: Mod> $trait<Fp<T>> for &'a Fp<T> {
            type Output = Fp<T>;
            fn $method(self, other: Fp<T>) -> Self::Output {
                $trait::$method(*self, other)
            }
        }

        impl<'a, T: Mod> $trait<&'a Fp<T>> for Fp<T> {
            type Output = Fp<T>;
            fn $method(self, other: &Fp<T>) -> Self::Output {
                $trait::$method(self, *other)
            }
        }

        impl<'a, T: Mod> $trait<&'a Fp<T>> for &'a Fp<T> {
            type Output = Fp<T>;
            fn $method(self, other: &Fp<T>) -> Self::Output {
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
impl<M: Mod> Neg for Fp<M> {
    type Output = Self;
    fn neg(self) -> Self {
        Fp::from_raw(M::P * 2 - self.value)
    }
}
impl<M: Mod> Sum for Fp<M> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(0), |b, x| b + x)
    }
}
impl<M: Mod> Product for Fp<M> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(1), |b, x| b * x)
    }
}
impl<'a, M: Mod> Sum<&'a Self> for Fp<M> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Fp<M> {
        iter.fold(Self::new(0), |b, x| b + x)
    }
}
impl<'a, M: Mod> Product<&'a Self> for Fp<M> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Fp<M> {
        iter.fold(Self::new(1), |b, x| b * x)
    }
}
impl<M: Mod> fmt::Debug for Fp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let (num, den, _) = simplify(self.value() as i32, M::P as i32);
        let (num, den) = match den.signum() {
            1 => (num, den),
            -1 => (-num, -den),
            _ => unreachable!(),
        };
        if den == 1 {
            write!(f, "{}", num)
        } else {
            write!(f, "{}/{}", num, den)
        }
    }
}
impl<M: Mod> fmt::Display for Fp<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value().fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use {
        super::F998244353 as Fp,
        assert_impl::assert_impl,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::{fmt::Debug, hash::Hash},
    };

    #[test]
    fn test_impl() {
        assert_impl!(Clone: Fp);
        assert_impl!(Debug: Fp);
        assert_impl!(Default: Fp);
        assert_impl!(Hash: Fp);
        assert_impl!(PartialEq: Fp);
        assert_impl!(Copy: Fp);
        assert_impl!(Eq: Fp);
    }

    #[test]
    fn test_add() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let y = rng.gen_range(0..=std::u32::MAX);
            let expected = ((x as u64 + y as u64) % Fp::P as u64) as u32;
            let result = (Fp::new(x) + Fp::new(y)).value();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_sub() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let y = rng.gen_range(0..=std::u32::MAX);
            let expected = ((x as i64 - y as i64).rem_euclid(Fp::P as i64)) as u32;
            let result = (Fp::new(x) - Fp::new(y)).value();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_mul() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let y = rng.gen_range(0..=std::u32::MAX);
            let expected = ((x as u64 * y as u64) % Fp::P as u64) as u32;
            let result = (Fp::new(x) * Fp::new(y)).value();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_inv() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let result = Fp::new(x).recip();
            assert_eq!((result * Fp::new(x)).value(), 1);
        }
    }

    #[test]
    fn test_div() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let y = rng.gen_range(0..=std::u32::MAX);
            let result = Fp::new(x) / Fp::new(y);
            assert_eq!((result * Fp::new(y)).value(), Fp::new(x).value());
        }
    }

    #[test]
    fn test_pow() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u8::MAX);
            let y = rng.gen_range(0..128 / 8);
            dbg!(x, y);
            let expected = ((x as u128).pow(y) % Fp::P as u128) as u32;
            let result = Fp::from(x).pow(y as u64).value();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_eq() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let x0 = Fp::new(x);
            let x1 = Fp::from(x as u64 + Fp::P as u64);
            let x2 = Fp::from(x as u64 + 2 * Fp::P as u64);
            assert_eq!(x0, x1);
            assert_eq!(x0, x2);
        }
    }

    #[test]
    fn test_sum() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let y = rng.gen_range(0..=std::u32::MAX);
            let z = rng.gen_range(0..=std::u32::MAX);
            let expected = ((x as u64 + y as u64 + z as u64) % Fp::P as u64) as u32;
            let result = [Fp::new(x), Fp::new(y), Fp::new(z)]
                .iter()
                .sum::<Fp>()
                .value();
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_product() {
        assert_eq!(Fp::new(3).pow(4u32), Fp::new(81));
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let x = rng.gen_range(0..=std::u32::MAX);
            let y = rng.gen_range(0..=std::u32::MAX);
            let z = rng.gen_range(0..=std::u32::MAX);
            let expected = ((x as u128 * y as u128 * z as u128) % Fp::P as u128) as u32;
            let result = [Fp::new(x), Fp::new(y), Fp::new(z)]
                .iter()
                .product::<Fp>()
                .value();
            assert_eq!(result, expected);
        }
    }
}
