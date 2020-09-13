use constant::Constant;
use std::{cmp, fmt, iter, mem, ops::*};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fp<Mod: Constant>(Mod::Output);

impl<Mod: Constant> Fp<Mod>
where
    Mod::Output: Value,
{
    #[inline]
    pub fn new(src: Mod::Output) -> Self {
        Self(Self::normalize(src))
    }

    #[inline]
    pub fn from_frac(num: Mod::Output, den: Mod::Output) -> Self {
        Self::new(num) / Self::new(den)
    }

    #[inline]
    pub fn into_inner(self) -> Mod::Output {
        self.0
    }

    #[inline]
    pub fn zero() -> Self {
        Self(Mod::Output::zero())
    }

    #[inline]
    pub fn one() -> Self {
        Self(Mod::Output::one())
    }

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

    #[inline]
    fn normalize(src: Mod::Output) -> Mod::Output {
        Self::normalize_from_the_top(src % Mod::VALUE)
    }

    #[inline]
    fn normalize_from_the_bottom(src: Mod::Output) -> Mod::Output {
        if Mod::VALUE < src {
            src - Mod::VALUE
        } else {
            src
        }
    }

    #[inline]
    fn normalize_from_the_top(src: Mod::Output) -> Mod::Output {
        if src < Mod::Output::zero() {
            src + Mod::VALUE
        } else {
            src
        }
    }
}

impl<Mod: Constant> Add for Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Self;

    #[inline]
    fn add(self, rhs: Self) -> Self {
        Self(Self::normalize_from_the_bottom(
            self.into_inner() + rhs.into_inner(),
        ))
    }
}

impl<Mod: Constant> Sub for Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Self;

    #[inline]
    fn sub(self, rhs: Self) -> Self {
        Self(Self::normalize_from_the_top(
            self.into_inner() - rhs.into_inner(),
        ))
    }
}

impl<Mod: Constant> Mul for Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        Self::new(self.into_inner() * rhs.into_inner())
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<Mod: Constant> Div for Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl<Mod: Constant> Neg for Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if self.into_inner() == Mod::Output::zero() {
            Self::zero()
        } else {
            Self(Mod::VALUE - self.into_inner())
        }
    }
}

impl<Mod: Constant> Neg for &Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Fp<Mod>;

    #[inline]
    fn neg(self) -> Fp<Mod> {
        if self.into_inner() == Mod::Output::zero() {
            Fp::zero()
        } else {
            Fp(Mod::VALUE - self.into_inner())
        }
    }
}

impl<Mod: Constant> iter::Sum<Fp<Mod>> for Fp<Mod>
where
    Mod::Output: Value,
{
    fn sum<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = Fp<Mod>>,
    {
        iter.fold(Self::zero(), Add::add)
    }
}

impl<'a, Mod: 'a + Constant> iter::Sum<&'a Fp<Mod>> for Fp<Mod>
where
    Mod::Output: Value,
{
    fn sum<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = &'a Fp<Mod>>,
    {
        iter.fold(Self::zero(), Add::add)
    }
}

impl<Mod: Constant> iter::Product<Fp<Mod>> for Fp<Mod>
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

impl<'a, Mod: 'a + Constant> iter::Product<&'a Fp<Mod>> for Fp<Mod>
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

macro_rules! forward_assign_biop {
    ($(impl $trait:ident, $fn_assign:ident, $fn:ident)*) => {
        $(
            impl<Mod: Constant> $trait for Fp<Mod>
            where
                Mod::Output: Value
            {
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

macro_rules! forward_ref_binop {
    ($(impl $imp:ident, $method:ident)*) => {
        $(
            impl<'a, Mod: Constant> $imp<Fp<Mod>> for &'a Fp<Mod>
            where
                Mod::Output:Value
            {
                type Output = Fp<Mod>;

                #[inline]
                fn $method(self, other: Fp<Mod>) -> Self::Output {
                    $imp::$method(*self, other)
                }
            }

            impl<'a, Mod: Constant> $imp<&'a Fp<Mod>> for Fp<Mod>
            where
                Mod::Output:Value
            {
                type Output = Fp<Mod>;

                #[inline]
                fn $method(self, other: &Fp<Mod>) -> Self::Output {
                    $imp::$method(self, *other)
                }
            }

            impl<'a, Mod: Constant> $imp<&'a Fp<Mod>> for &'a Fp<Mod>
            where
                Mod::Output:Value
            {
                type Output = Fp<Mod>;

                #[inline]
                fn $method(self, other: &Fp<Mod>) -> Self::Output {
                    $imp::$method(*self, *other)
                }
            }
        )*
    };
}
forward_ref_binop! {
    impl Add, add
    impl Sub, sub
    impl Mul, mul
    impl Div, div
}

impl<Mod: Constant> fmt::Display for Fp<Mod>
where
    Mod::Output: Value,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

pub trait Value:
    Sized
    + Clone
    + Copy
    + fmt::Debug
    + fmt::Display
    + cmp::PartialOrd
    + cmp::PartialEq
    + cmp::Ord
    + cmp::Eq
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Div<Output = Self>
    + Rem<Output = Self>
    + Neg<Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + RemAssign
{
    fn zero() -> Self;
    fn one() -> Self;
}

macro_rules! impl_value {
    ($($type:ty,)*) => {
        $(
        impl Value for $type {
            #[inline]
            fn zero() -> $type {
                0
            }
            #[inline]
            fn one() -> $type {
                1
            }
        }
        )*
    };
}

impl_value! {
    i8, i16, i32, i64, i128, isize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use constant::define_constant;

    define_constant! { type Mod97: i16 = 97; }
    type F97 = Fp<Mod97>;

    #[test]
    fn test_trait_implementations() {
        fn impl_debug<T: fmt::Debug>(_: T) {}
        fn impl_clone<T: Clone>(_: T) {}
        fn impl_copy<T: Copy>(_: T) {}
        fn impl_partial_eq<T: cmp::PartialEq>(_: T) {}
        fn impl_eq<T: cmp::Eq>(_: T) {}

        impl_debug(F97::zero());
        impl_clone(F97::zero());
        impl_copy(F97::zero());
        impl_partial_eq(F97::zero());
        impl_eq(F97::zero());
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

    #[test]
    fn test_pow() {
        // pow
        assert_eq!(F97::new(7).pow(0), F97::new(1));
        assert_eq!(F97::new(7).pow(1), F97::new(7));
        assert_eq!(F97::new(7).pow(2), F97::new(49));
        assert_eq!(F97::new(7).pow(3), F97::new(343 % 97));
        assert_eq!(F97::new(7).pow(4), F97::new(2401 % 97));
    }

    #[test]
    fn test_sum() {
        // Sum<Fp<_>>
        assert_eq!(
            vec![F97::new(2), F97::new(3)].into_iter().sum::<F97>(),
            F97::new(5)
        );

        // Sum<&Fp<_>>
        assert_eq!(
            vec![F97::new(2), F97::new(3)].iter().sum::<F97>(),
            F97::new(5)
        );
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
