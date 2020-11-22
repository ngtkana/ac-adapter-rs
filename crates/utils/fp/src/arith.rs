use super::{Fp, Mod};
use std::ops::*;

impl<T: Mod> Add for Fp<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let res = self.0 + rhs.0;
        Self::unchecked(if T::MOD <= res { res - T::MOD } else { res })
    }
}

impl<T: Mod> Sub for Fp<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let res = self.0 - rhs.0;
        Self::unchecked(if res < 0 { res + T::MOD } else { res })
    }
}

impl<T: Mod> Mul for Fp<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::new(self.0 * rhs.0)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<T: Mod> Div for Fp<T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        self * rhs.inv()
    }
}

impl<M: Mod> Neg for Fp<M> {
    type Output = Self;
    fn neg(self) -> Self {
        if self.0 == 0 {
            Self::unchecked(0)
        } else {
            Self::unchecked(M::MOD - self.0)
        }
    }
}

impl<M: Mod> Neg for &Fp<M> {
    type Output = Fp<M>;
    fn neg(self) -> Self::Output {
        if self.0 == 0 {
            Fp::unchecked(0)
        } else {
            Fp::unchecked(M::MOD - self.0)
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
            impl<'a, T: Mod> $imp<Fp<T>> for &'a Fp<T> {
                type Output = Fp<T>;
                fn $method(self, other: Fp<T>) -> Self::Output {
                    $imp::$method(*self, other)
                }
            }

            impl<'a, T: Mod> $imp<&'a Fp<T>> for Fp<T> {
                type Output = Fp<T>;
                fn $method(self, other: &Fp<T>) -> Self::Output {
                    $imp::$method(self, *other)
                }
            }

            impl<'a, T: Mod> $imp<&'a Fp<T>> for &'a Fp<T> {
                type Output = Fp<T>;
                fn $method(self, other: &Fp<T>) -> Self::Output {
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
