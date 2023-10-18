//! A library for modular arithmetic.
//! # Examples
//! ```
//! use fp::fp;
//! type Fp = fp::Fp<998244353>;
//! let a = Fp::new(3);
//! let b = Fp::new(4);
//! assert_eq!(a + b, Fp::new(7));
//! assert_eq!(a - b, Fp::new(998244352));
//! assert_eq!(a * b, Fp::new(12));
//! assert_eq!(a / b * b, Fp::new(3));
//! assert_eq!(a.pow(3), Fp::new(27));
//! ```
//!
//! ## Factorials
//! ```
//! use fp::fp;
//! use fp::Factorial;
//! let f = Factorial::<998244353>::new(10);
//! assert_eq!(f.fact(5), fp!(120));
//! assert_eq!(f.inv_fact(5), fp!(120).inv());
//! assert_eq!(f.perm(5, 3), fp!(60));
//! assert_eq!(f.comb(5, 3), fp!(10));
//! assert_eq!(f.comb_with_reputation(5, 3), fp!(35));
//! ```
//!
//! ## Convolution by Fast Fourier transform (FFT)
//! ```
//! use fp::Fp;
//! use fp::fps_mul;
//! use fp::fp;
//! let a = vec![fp!(1; mod 998244353), fp!(2), fp!(3)];
//! let b = vec![fp!(4), fp!(5), fp!(6)];
//! let c = fps_mul(&a, &b);
//! assert_eq!(c, vec![fp!(4), fp!(13), fp!(28), fp!(27), fp!(18)]);
//! ```
mod ext_gcd;
mod factorial;
mod fourier;

use ext_gcd::mod_inv;
pub use factorial::Factorial;
pub use fourier::any_mod_fps_mul;
pub use fourier::fft;
pub use fourier::fps_mul;
pub use fourier::ifft;
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
use std::ops::Sub;
use std::ops::SubAssign;

/// Constructs a new instance of [`Fp`]
/// # Examples
/// ```
/// use fp::fp;
/// use fp::Fp;
/// let a = fp!(42; mod 998244353);
/// assert_eq!(a.value(), 42);
/// ```
#[macro_export]
macro_rules! fp {
    ($value:expr) => {
        $crate::Fp::from($value)
    };
    ($value:expr; mod $p:expr) => {
        $crate::Fp::<$p>::from($value)
    };
}

/// A primitive root of unity.
pub trait PrimitiveRoot<const P: u64> {
    /// A primitive root of unity.
    const VALUE: Fp<P>;
}
impl PrimitiveRoot<998244353> for () {
    const VALUE: Fp<998244353> = Fp::new(3);
}
impl PrimitiveRoot<1012924417> for () {
    const VALUE: Fp<1012924417> = Fp::new(5);
}
impl PrimitiveRoot<924844033> for () {
    const VALUE: Fp<924844033> = Fp::new(5);
}

/// A value in $\mathbb{Fp}_p$.
/// # Requirements
/// - $P$ is odd and prime ($P \gt 2^{31}$)
/// # Invariants
/// - $0 \le \text{value} < P$
/// # Examples
/// ```
/// type Fp = fp::Fp<998244353>;
/// assert_eq!(Fp::new(3) + Fp::new(4), Fp::new(7));
/// assert_eq!(Fp::new(3) - Fp::new(4), Fp::new(998244352));
/// assert_eq!(Fp::new(3) * Fp::new(4), Fp::new(12));
/// assert_eq!(Fp::new(3) / Fp::new(4) * Fp::new(4), Fp::new(3));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Fp<const P: u64> {
    value: u64,
}
impl<const P: u64> Fp<P> {
    /// Constructs a new instance.
    /// # Requirements
    /// # Examples
    /// ```
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let a = Fp::<P>::new(42);
    /// ```
    pub const fn new(value: u64) -> Self { Self { value: value % P } }

    /// Returns the value.
    /// # Examples
    /// ```
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let a = Fp::<P>::new(42);
    /// assert_eq!(a.value(), 42);
    /// ```
    pub const fn value(self) -> u64 { self.value }

    /// Returns the multiplicative inverse.
    /// # Examples
    /// ```
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let a = Fp::<P>::new(2);
    /// assert_eq!(a.inv().value(), 499122177);
    /// ```
    pub fn inv(self) -> Self {
        Self {
            value: mod_inv::<P>(self.value),
        }
    }

    /// Returns the $n$-th power.
    /// # Examples
    /// ```
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let a = Fp::<P>::new(2);
    /// assert_eq!(a.pow(3).value(), 8);
    /// ```
    pub fn pow(self, mut exp: u64) -> Self {
        let mut result = Self::new(1);
        let mut base = self;
        while exp > 0 {
            if exp & 1 == 1 {
                result *= base;
            }
            base *= base;
            exp >>= 1;
        }
        result
    }

    /// Returns $(-1)^{\text{pow}}$.
    ///
    /// # Examples
    /// ```
    /// type Fp = fp::Fp<998244353>;
    /// assert_eq!(Fp::sign(0), Fp::from(1));
    /// assert_eq!(Fp::sign(1), Fp::from(-1));
    /// assert_eq!(Fp::sign(2), Fp::from(1));
    /// assert_eq!(Fp::sign(3), Fp::from(-1));
    /// ```
    pub fn sign(pow: usize) -> Self { Self::new(if pow % 2 == 0 { 1 } else { P - 1 }) }
}
impl<const P: u64> std::fmt::Debug for Fp<P> {
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
        if self.value == 0 {
            return write!(f, "0");
        }
        let [mut num, mut den] = berlekamp_massey_fp(self.value as i64, P as i64);
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
impl<const P: u64> std::fmt::Display for Fp<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value())
    }
}
macro_rules! impl_from_signed {
    ($($t:ty),*) => {
        $(
            impl<const P: u64> From<$t> for Fp<P> {
                fn from(x: $t) -> Self {
                    if x < 0 {
                        -Self::new((P as i64 - x as i64) as u64)
                    } else {
                        Self::new(x as u64)
                    }
                }
            }
        )*
    };
}
impl_from_signed!(i8, i16, i32, i64, i128, isize);
macro_rules! impl_from_unsigned {
    ($($t:ty),*) => {
        $(
            impl<const P: u64> From<$t> for Fp<P> {
                fn from(x: $t) -> Self { Self::new(x as u64) }
            }
        )*
    };
}
impl_from_unsigned!(u8, u16, u32, u64, u128, usize);
impl<const P: u64> AddAssign<Fp<P>> for Fp<P> {
    fn add_assign(&mut self, rhs: Fp<P>) {
        self.value += rhs.value;
        if self.value >= P {
            self.value -= P;
        }
    }
}
impl<const P: u64> SubAssign<Fp<P>> for Fp<P> {
    fn sub_assign(&mut self, rhs: Fp<P>) {
        if self.value < rhs.value {
            self.value += P;
        }
        self.value -= rhs.value;
    }
}
impl<const P: u64> MulAssign<Fp<P>> for Fp<P> {
    fn mul_assign(&mut self, rhs: Fp<P>) { self.value = self.value * rhs.value % P; }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl<const P: u64> DivAssign<Fp<P>> for Fp<P> {
    fn div_assign(&mut self, rhs: Fp<P>) { *self *= rhs.inv() }
}
macro_rules! fp_forward_ops {
    ($(
        $trait:ident,
        $trait_assign:ident,
        $fn:ident,
        $fn_assign:ident,
    )*) => {$(
        impl<const P: u64> $trait_assign<&Fp<P>> for Fp<P> {
            fn $fn_assign(&mut self, rhs: &Fp<P>) {
                self.$fn_assign(*rhs);
            }
        }
        impl<const P: u64, T: Into<Fp<P>>> $trait<T> for Fp<P> {
            type Output = Fp<P>;
            fn $fn(mut self, rhs: T) -> Self::Output {
                self.$fn_assign(rhs.into());
                self
            }
        }
        impl<const P: u64> $trait<&Fp<P>> for Fp<P> {
            type Output = Fp<P>;
            fn $fn(self, rhs: &Fp<P>) -> Self::Output {
                self.$fn(*rhs)
            }
        }
        impl<const P: u64, T: Into<Fp<P>>> $trait<T> for &Fp<P> {
            type Output = Fp<P>;
            fn $fn(self, rhs: T) -> Self::Output {
                (*self).$fn(rhs.into())
            }
        }
        impl<const P: u64> $trait<&Fp<P>> for &Fp<P> {
            type Output = Fp<P>;
            fn $fn(self, rhs: &Fp<P>) -> Self::Output {
                (*self).$fn(*rhs)
            }
        }
    )*};
}
fp_forward_ops! {
    Add, AddAssign, add, add_assign,
    Sub, SubAssign, sub, sub_assign,
    Mul, MulAssign, mul, mul_assign,
    Div, DivAssign, div, div_assign,
}
impl<const P: u64> Neg for Fp<P> {
    type Output = Fp<P>;

    fn neg(mut self) -> Self::Output {
        if self.value > 0 {
            self.value = P - self.value;
        }
        self
    }
}
impl<const P: u64> Sum for Fp<P> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self { iter.fold(Self::new(0), |acc, x| acc + x) }
}
impl<'a, const P: u64> Sum<&'a Self> for Fp<P> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self { iter.copied().sum() }
}
impl<const P: u64> Product for Fp<P> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::new(1), |acc, x| acc * x)
    }
}
impl<'a, const P: u64> Product<&'a Self> for Fp<P> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self { iter.copied().product() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    const P: u64 = 998244353;

    #[test]
    fn test_new() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = rng.gen_range(0..P);
            let b = Fp::<P>::new(a);
            assert_eq!(a, b.value());
        }
    }
    #[test]
    fn test_from_u8_exhaustive() {
        for a in u8::MIN..u8::MAX {
            let b = Fp::<P>::from(a);
            assert_eq!(u64::from(a) % P, b.value());
        }
    }
    #[test]
    fn test_from_u64() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = rng.gen::<u64>();
            let b = Fp::<P>::from(a);
            assert_eq!(a % P, b.value());
        }
    }
    #[test]
    fn test_from_i8_exhaustive() {
        for a in i8::MIN..i8::MAX {
            let b = Fp::<P>::from(a);
            assert_eq!(i64::from(a).rem_euclid(P as i64) as u64, b.value());
        }
    }
    #[test]
    fn test_from_i64() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = rng.gen::<i64>();
            let b = Fp::<P>::from(a);
            assert_eq!(a.rem_euclid(P as i64) as u64, b.value());
        }
    }
    #[test]
    fn test_add() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = Fp::<P>::new(rng.gen_range(1..P));
            let b = Fp::<P>::new(rng.gen_range(1..P));
            let result = a + b;
            assert_eq!(result.value(), (a.value() + b.value()) % P);
        }
    }
    #[test]
    fn test_sub() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = Fp::<P>::new(rng.gen_range(1..P));
            let b = Fp::<P>::new(rng.gen_range(1..P));
            let result = a - b;
            assert_eq!(result.value(), (a.value() + P - b.value()) % P);
        }
    }
    #[test]
    fn test_mul() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = Fp::<P>::new(rng.gen_range(1..P));
            let b = Fp::<P>::new(rng.gen_range(1..P));
            let result = a * b;
            assert_eq!(result.value(), a.value() * b.value() % P);
        }
    }
    #[test]
    fn test_inv() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = Fp::<P>::new(rng.gen_range(1..P));
            let b = a.inv();
            assert_eq!(a.value() * b.value() % P, 1);
        }
    }
    #[test]
    fn test_div() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = Fp::<P>::new(rng.gen_range(1..P));
            let b = Fp::<P>::new(rng.gen_range(1..P));
            let result = a / b;
            assert_eq!(result.value(), a.value() * b.inv().value() % P);
        }
    }
    #[test]
    fn test_pow() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..256 {
            let a = Fp::<P>::new(rng.gen_range(1..P));
            let b = rng.gen_range(0..40);
            let result = a.pow(b);
            assert_eq!(
                result,
                std::iter::repeat(a).take(b as usize).product::<Fp<P>>()
            );
        }
    }
}
