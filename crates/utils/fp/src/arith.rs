use super::{Fp, Modable, Value};
use std::ops::*;
use type_traits::*;

impl<Mod: Modable> Add for Fp<Mod>
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

impl<Mod: Modable> Sub for Fp<Mod>
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

impl<Mod: Modable> Mul for Fp<Mod>
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
impl<Mod: Modable> Div for Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Self;

    #[inline]
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl<Mod: Modable> Neg for Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if self.into_inner().is_zero() {
            Self::zero()
        } else {
            Self(Mod::VALUE - self.into_inner())
        }
    }
}

impl<Mod: Modable> Neg for &Fp<Mod>
where
    Mod::Output: Value,
{
    type Output = Fp<Mod>;

    #[inline]
    fn neg(self) -> Fp<Mod> {
        if self.into_inner().is_zero() {
            Fp::zero()
        } else {
            Fp(Mod::VALUE - self.into_inner())
        }
    }
}

macro_rules! forward_assign_biop {
    ($(impl $trait:ident, $fn_assign:ident, $fn:ident)*) => {
        $(
            impl<Mod: Modable> $trait for Fp<Mod>
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
            impl<'a, Mod: Modable> $imp<Fp<Mod>> for &'a Fp<Mod>
            where
                Mod::Output:Value
            {
                type Output = Fp<Mod>;

                #[inline]
                fn $method(self, other: Fp<Mod>) -> Self::Output {
                    $imp::$method(*self, other)
                }
            }

            impl<'a, Mod: Modable> $imp<&'a Fp<Mod>> for Fp<Mod>
            where
                Mod::Output:Value
            {
                type Output = Fp<Mod>;

                #[inline]
                fn $method(self, other: &Fp<Mod>) -> Self::Output {
                    $imp::$method(self, *other)
                }
            }

            impl<'a, Mod: Modable> $imp<&'a Fp<Mod>> for &'a Fp<Mod>
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
