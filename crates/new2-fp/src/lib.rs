use std::{
    fmt::{Debug, Display},
    hash::Hash,
    iter::{Product, Sum},
    marker::PhantomData,
    mem::swap,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

define_fp! { pub type 1_000_000_007, M1000000007, F1000000007 }
define_fp! { pub type 998_244_353, M998244353, F998244353 } // 119 * 2 ^ 23 + 1

/// 有限体型の実装するトレイトです。
pub trait Mod {
    /// 法
    const P: u64; // ……ほう。
}

/// [`Mod`] を実装した型 `$m` と、型エイリアス `$f = Fp<$m>` を定義します。
#[macro_export]
macro_rules! define_fp {
    ($pub:vis type $mod:expr) => {
        $crate::define_fp! { $pub type $mod, F, M }
    };
    ($pub:vis type $mod:expr, $f:ident, $m:ident) => {
        $pub enum $m {}
        impl $crate::Mod for $m {
            const P: u64 = $mod;
        }
        $pub type $f = $crate::Fp<$m>;
    };
}

/// [`Fp`] 型のオブジェクトを構築します。
///
/// # 使い方
///
/// １つ式を入れると、それで [`Fp::from()`] を呼びます。
///
/// ```
/// use new2_fp::{fp, define_fp};
/// define_fp! { type 13 }
///
/// // リテラル
/// let a: F = fp!(6);
/// assert_eq!(a.value(), 6);
///
/// // 式
/// assert_eq!(fp!(2 + 3), F::new(5));
///
/// // 変数
/// let x: i16 = -3;
/// assert_eq!(fp!(x), F::new(10));
/// ```
///
/// セミコロン区切りで２つ整数を入れると、順に分子、分母とする分数を構築します。
///
/// ```
/// use new2_fp::{fp, define_fp};
/// define_fp! { type 13 }
///
/// assert_eq!(fp!(2; 3), F::new(2) / F::new(3));
/// ```
#[macro_export]
macro_rules! fp {
    ($num:expr; $den:expr) => {
        $crate::Fp::from($num) / $crate::Fp::from($den)
    };
    ($value:expr) => {
        $crate::Fp::from($value)
    };
}

pub struct Fp<M>(u64, PhantomData<fn() -> M>);
impl<M: Mod> Fp<M> {
    /// 法です。[`Mod::P`] へのショートカットです。
    ///
    /// # Example
    ///
    /// ```
    /// use new2_fp::{define_fp};
    ///
    /// define_fp! { type 7 }
    /// assert_eq!(F::P, 7);
    ///
    /// define_fp! { type 11, F11, M11 }
    /// assert_eq!(F11::P, 11);
    /// ```
    pub const P: u64 = M::P;
    pub fn new(value: u64) -> Self {
        Self(value % Self::P, PhantomData)
    }
    /// 整数に戻します。
    ///
    /// # Example
    ///
    /// ```
    /// use new2_fp::{define_fp};
    ///
    /// define_fp! { type 7 }
    /// let x = F::new(13).value();
    /// assert_eq!(x, 6);
    /// ```
    pub fn value(self) -> u64 {
        self.0
    }
    /// 逆数を返します。
    ///
    /// # Example
    ///
    /// ```
    /// use new2_fp::{define_fp, fp};
    ///
    /// define_fp! { type 7 }
    /// let x = F::new(3).inv();
    /// assert_eq!(x, fp!(5));
    /// ```
    pub fn inv(self) -> Self {
        let mut x = Self::P as i64;
        let mut y = self.0 as i64;
        let mut u = 0;
        let mut v = 1;
        while y != 0 {
            let q = x / y;
            x -= y * q;
            u -= v * q;
            swap(&mut x, &mut y);
            swap(&mut u, &mut v);
        }
        debug_assert_eq!(x, 1);
        debug_assert_eq!(v.abs(), Self::P as i64);
        debug_assert!(u.abs() < Self::P as i64);
        if u < 0 {
            u += Self::P as i64;
        }
        Self(u as u64, PhantomData)
    }
}
impl<M: Mod> Copy for Fp<M> {}
impl<M: Mod> Clone for Fp<M> {
    fn clone(&self) -> Self {
        Self(self.0, self.1)
    }
}
impl<M: Mod> PartialEq for Fp<M> {
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
impl<M: Mod> Display for Fp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        Display::fmt(&self.0, f)
    }
}
impl<M: Mod> Eq for Fp<M> {}
impl<M: Mod> Default for Fp<M> {
    fn default() -> Self {
        Self(0, PhantomData)
    }
}
impl<M: Mod> Hash for Fp<M> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}
impl<M: Mod> Debug for Fp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        pub fn berlekamp_massey_fp(a: i64, p: i64) -> [i64; 2] {
            let mut u0 = 0_i64;
            let mut v0 = 1_i64;
            let mut w0 = a * u0 + p * v0;
            let mut u1 = 1_i64;
            let mut v1 = 0_i64;
            let mut w1 = a * u1 + p * v1;
            while p <= w0 * w0 {
                let q = w0 / w1;
                u0 -= q * u1;
                v0 -= q * v1;
                w0 -= q * w1;
                swap(&mut u0, &mut u1);
                swap(&mut v0, &mut v1);
                swap(&mut w0, &mut w1);
            }
            [w0, u0]
        }
        if self.0 == 0 {
            return write!(f, "0");
        }
        let [mut num, mut den] = berlekamp_massey_fp(self.0 as i64, M::P as i64);
        if den < 0 {
            num = -num;
            den = -den;
        }
        if den == 1 {
            write!(f, "{}", num)
        } else {
            write!(f, "{}/{}", num, den)
        }
    }
}
macro_rules! impl_from_large_int {
    ($($T:ty), *$(,)?) => {$(
        impl<M: Mod> From<$T> for Fp<M> {
            fn from(x: $T) -> Self {
                Self::new(x.rem_euclid(M::P as _) as u64)
            }
        }
    )*}
}
impl_from_large_int! {
    i8, i16, i32, i64,
    u128, usize,
    i128, isize,
}
macro_rules! impl_from_small_int {
    ($($T: ty), *$(,)?) => {$(
        impl<M: Mod> From<$T> for Fp<M> {
            fn from(x: $T) -> Self {
                Self::new(x as u64)
            }
        }
    )*}
}
impl_from_small_int! {
    u8, u16, u32, u64,
}

impl<M: Mod, T: Into<Fp<M>>> AddAssign<T> for Fp<M> {
    fn add_assign(&mut self, rhs: T) {
        self.0 += rhs.into().0;
        if M::P <= self.0 {
            self.0 -= M::P;
        }
    }
}
impl<M: Mod, T: Into<Fp<M>>> SubAssign<T> for Fp<M> {
    fn sub_assign(&mut self, rhs: T) {
        let rhs = rhs.into().0;
        if self.0 < rhs {
            self.0 += M::P;
        }
        self.0 -= rhs;
    }
}
impl<M: Mod, T: Into<Fp<M>>> MulAssign<T> for Fp<M> {
    fn mul_assign(&mut self, rhs: T) {
        self.0 *= rhs.into().0;
        self.0 %= Self::P;
    }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl<M: Mod, T: Into<Fp<M>>> DivAssign<T> for Fp<M> {
    fn div_assign(&mut self, rhs: T) {
        *self *= rhs.into().inv();
    }
}
impl<M: Mod> Neg for Fp<M> {
    type Output = Fp<M>;
    fn neg(self) -> Self::Output {
        if self.0 == 0 {
            self
        } else {
            Self(Self::P - self.0, PhantomData)
        }
    }
}
impl<M: Mod> Neg for &Fp<M> {
    type Output = Fp<M>;
    fn neg(self) -> Self::Output {
        -*self
    }
}

macro_rules! forward_ops {
    ($((
        $trait:ident,
        $trait_assign:ident,
        $fn:ident,
        $fn_assign:ident$(,)?
    )),* $(,)?) => {$(
        impl<M: Mod> $trait_assign<&Fp<M>> for Fp<M> {
            fn $fn_assign(&mut self, rhs: &Fp<M>) {
                self.$fn_assign(*rhs);
            }
        }
        impl<M: Mod> $trait for Fp<M> {
            type Output = Fp<M>;
            fn $fn(mut self, rhs: Fp<M>) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }
        impl<M: Mod> $trait<&Fp<M>> for Fp<M> {
            type Output = Fp<M>;
            fn $fn(self, rhs: &Fp<M>) -> Self::Output {
                self.$fn(*rhs)
            }
        }
        impl<M: Mod> $trait<Fp<M>> for &Fp<M> {
            type Output = Fp<M>;
            fn $fn(self, rhs: Fp<M>) -> Self::Output {
                (*self).$fn(rhs)
            }
        }
        impl<M: Mod> $trait<&Fp<M>> for &Fp<M> {
            type Output = Fp<M>;
            fn $fn(self, rhs: &Fp<M>) -> Self::Output {
                (*self).$fn(*rhs)
            }
        }
    )*};
}
forward_ops! {
    (Add, AddAssign, add, add_assign),
    (Sub, SubAssign, sub, sub_assign),
    (Mul, MulAssign, mul, mul_assign),
    (Div, DivAssign, div, div_assign),
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
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new(0), |b, x| b + x)
    }
}
impl<'a, M: Mod> Product<&'a Self> for Fp<M> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new(1), |b, x| b * x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    define_fp! { type 13 }

    #[test]
    #[allow(unused_imports)]
    fn test_visibility() {
        mod internal {
            use super::*;
            define_fp! { pub type 17, F17, M17 }
        }
        use internal::{F17, M17};
        assert_eq!(F17::P, 17);
        assert_eq!(M17::P, 17);
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_add() {
        assert_eq!(F::new(6) + F::new(8), F::new(1));
        assert_eq!(F::new(6) + &F::new(8), F::new(1));
        assert_eq!(&F::new(6) + F::new(8), F::new(1));
        assert_eq!(&F::new(6) + &F::new(8), F::new(1));
        let mut a = F::new(6);
        a += Fp::new(8);
        assert_eq!(a, F::new(1));
        let mut a = F::new(6);
        a += &Fp::new(8);
        assert_eq!(a, F::new(1));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_sub() {
        assert_eq!(F::new(6) - F::new(8), F::new(11));
        assert_eq!(F::new(6) - &F::new(8), F::new(11));
        assert_eq!(&F::new(6) - F::new(8), F::new(11));
        assert_eq!(&F::new(6) - &F::new(8), F::new(11));
        let mut a = F::new(6);
        a -= Fp::new(8);
        assert_eq!(a, F::new(11));
        let mut a = F::new(6);
        a -= &Fp::new(8);
        assert_eq!(a, F::new(11));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_mul() {
        assert_eq!(F::new(6) * F::new(8), F::new(9));
        assert_eq!(F::new(6) * &F::new(8), F::new(9));
        assert_eq!(&F::new(6) * F::new(8), F::new(9));
        assert_eq!(&F::new(6) * &F::new(8), F::new(9));
        let mut a = F::new(6);
        a *= Fp::new(8);
        assert_eq!(a, F::new(9));
        let mut a = F::new(6);
        a *= &Fp::new(8);
        assert_eq!(a, F::new(9));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_div() {
        assert_eq!(F::new(6) / F::new(8), F::new(4));
        assert_eq!(F::new(6) / &F::new(8), F::new(4));
        assert_eq!(&F::new(6) / F::new(8), F::new(4));
        assert_eq!(&F::new(6) / &F::new(8), F::new(4));
        let mut a = F::new(6);
        a /= Fp::new(8);
        assert_eq!(a, F::new(4));
        let mut a = F::new(6);
        a /= &Fp::new(8);
        assert_eq!(a, F::new(4));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_neg() {
        assert_eq!(-F::new(6), F::new(7));
        assert_eq!(-&F::new(6), F::new(7));
    }

    #[test]
    fn test_sum() {
        let a: [F; 3] = [fp!(10), fp!(11), fp!(12)];
        assert_eq!(a.iter().sum::<F>(), fp!(33));
        assert_eq!(a.iter().copied().sum::<F>(), fp!(33));
    }

    #[test]
    fn test_product() {
        let a: [F; 3] = [fp!(10), fp!(11), fp!(12)];
        assert_eq!(a.iter().product::<F>(), fp!(1320));
        assert_eq!(a.iter().copied().product::<F>(), fp!(1320));
    }

    #[test]
    #[allow(clippy::op_ref)]
    fn test_fmt() {
        define_fp! { type 998244353 }
        for num in 1..100_u64 {
            for den in 1..100_u64 {
                let x: F = fp!(num; den);
                let s = format!("{:?}", x);
                if num % den == 0 {
                    let restored = s.parse::<u64>().unwrap();
                    assert_eq!(num, den * restored);
                } else {
                    let v = s.split('/').collect::<Vec<_>>();
                    assert_eq!(v.len(), 2);
                    let a = v[0].parse::<u64>().unwrap();
                    let b = v[1].parse::<u64>().unwrap();
                    assert_eq!(num * b, den * a);
                }
            }
        }
    }
}
