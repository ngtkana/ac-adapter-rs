use super::{Fp, Mod};
use alg_traits::arith::Zero;
use std::ops::*;

impl<M: Mod> Add for Fp<M> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self(Self::normalize_from_the_bottom(
            self.into_inner() + rhs.into_inner(),
        ))
    }
}

impl<M: Mod> Sub for Fp<M> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self(Self::normalize_from_the_top(
            self.into_inner() - rhs.into_inner(),
        ))
    }
}

impl<M: Mod> Mul for Fp<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::new(self.into_inner() * rhs.into_inner())
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<M: Mod> Div for Fp<M> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl<M: Mod> Neg for Fp<M> {
    type Output = Self;
    fn neg(self) -> Self {
        if self.into_inner() == M::Mod::zero() {
            Self::zero()
        } else {
            Self(M::MOD - self.into_inner())
        }
    }
}

impl<M: Mod> Neg for &Fp<M> {
    type Output = Fp<M>;
    fn neg(self) -> Fp<M> {
        if self.into_inner() == M::Mod::zero() {
            Fp::zero()
        } else {
            Fp(M::MOD - self.into_inner())
        }
    }
}

macro_rules! forward_assign_biop {
    ($(impl $trait:ident, $fn_assign:ident, $fn:ident)*) => {
        $(
            impl<M: Mod> $trait for Fp<M> {
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
            impl<'a, M: Mod> $imp<Fp<M>> for &'a Fp<M> {
                type Output = Fp<M>;
                fn $method(self, other: Fp<M>) -> Self::Output {
                    $imp::$method(*self, other)
                }
            }

            impl<'a, M: Mod> $imp<&'a Fp<M>> for Fp<M> {
                type Output = Fp<M>;
                fn $method(self, other: &Fp<M>) -> Self::Output {
                    $imp::$method(self, *other)
                }
            }

            impl<'a, M: Mod> $imp<&'a Fp<M>> for &'a Fp<M> {
                type Output = Fp<M>;
                fn $method(self, other: &Fp<M>) -> Self::Output {
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
