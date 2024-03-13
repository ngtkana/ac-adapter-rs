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

#[derive(Clone, Default, Copy)]
pub struct Rational<T: Signed>(T, T);
impl<T: Signed> Rational<T> {
    pub fn new(num: T, den: T) -> Self {
        assert_ne!(den, T::zero(), "分母 0 はだめです。: {:?}/{:?}", &num, &den);
        let g = gcd(num, den).generic_abs() * den.generic_signum();
        Self(num / g, den / g)
    }

    pub fn decompose(self) -> [T; 2] {
        [self.0, self.1]
    }

    pub fn into_f64(self) -> f64
    where
        f64: From<T>,
    {
        f64::from(self.0) / f64::from(self.1)
    }
}
impl<T: Signed> PartialEq for Rational<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 * other.1 == self.1 * other.0
    }
}
impl<T: Signed> Eq for Rational<T> {}
impl<T: Signed> Ord for Rational<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0 * other.1).cmp(&(self.1 * other.0))
    }
}
impl<T: Signed> PartialOrd for Rational<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl<T: Signed> Debug for Rational<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.1 == T::one() {
            write!(f, "{:?}", self.0)
        } else {
            write!(f, "{:?}/{:?}", self.0, self.1)
        }
    }
}
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
impl<T: Signed> AddAssign for Rational<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = Self::new(self.0 * rhs.1 + self.1 * rhs.0, self.1 * rhs.1)
    }
}
impl<T: Signed> SubAssign for Rational<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = Self::new(self.0 * rhs.1 - self.1 * rhs.0, self.1 * rhs.1)
    }
}
impl<T: Signed> MulAssign for Rational<T> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = Self::new(self.0 * rhs.0, self.1 * rhs.1)
    }
}
impl<T: Signed> DivAssign for Rational<T> {
    fn div_assign(&mut self, rhs: Self) {
        assert_ne!(
            rhs.0,
            T::zero(),
            "有理数の 0 除算はだめです。: self = {:?}, rhs = {:?}",
            self,
            rhs
        );
        *self = Self::new(self.0 * rhs.1, self.1 * rhs.0)
    }
}
impl<T: Signed> Neg for Rational<T> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self(-self.0, self.1)
    }
}
impl<T: Signed> Sum for Rational<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self(T::zero(), T::one()), Add::add)
    }
}
impl<T: Signed> Product for Rational<T> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self(T::one(), T::one()), Mul::mul)
    }
}
impl<'a, T: 'a + Signed> Sum<&'a Self> for Rational<T> {
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self(T::zero(), T::one()), Add::add)
    }
}
impl<'a, T: 'a + Signed> Product<&'a Self> for Rational<T> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self(T::one(), T::one()), Mul::mul)
    }
}

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
    fn zero() -> Self;
    fn one() -> Self;
    fn generic_abs(self) -> Self;
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
            println!(
                "{:?} + {:?} = {:?} ({:.3} + {:.3} = {:.3})",
                x, y, z, xf64, yf64, zf64
            );
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
            println!(
                "{:?} - {:?} = {:?} ({:.3} - {:.3} = {:.3})",
                x, y, z, xf64, yf64, zf64
            );
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
            println!(
                "{:?} * {:?} = {:?} ({:.3} * {:.3} = {:.3})",
                x, y, z, xf64, yf64, zf64
            );
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
            println!(
                "{:?} / {:?} = {:?} ({:.3} / {:.3} = {:.3})",
                x, y, z, xf64, yf64, zf64
            );
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
            println!("neg({:?})  = -{:?} (neg({:.3}) = {:.3})", x, y, xf64, yf64);
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
            println!(
                "cmp({:?}, {:?}) = {:?} (cmp({:.3}, {:.3}) = {:?})",
                x, y, z, xf64, yf64, zf64
            );
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
