use super::Poly;
use std::ops::*;
use type_traits::Ring;

impl<T: Ring + Copy> Add for Poly<T> {
    type Output = Poly<T>;
    fn add(self, rhs: Self) -> Self::Output {
        let mut res = self.0.clone();
        if self.0.len() < rhs.0.len() {
            res.resize(rhs.0.len(), T::zero());
        }
        res.iter_mut().zip(rhs.0.iter()).for_each(|(x, y)| {
            *x += *y;
        });
        Self::remove_trailig_zeros(&mut res);
        Poly(res)
    }
}

impl<T: Ring + Copy> Sub for Poly<T>
where
    T: Sub + SubAssign,
{
    type Output = Poly<T>;
    fn sub(self, rhs: Self) -> Self::Output {
        let mut res = self.0.clone();
        if self.0.len() < rhs.0.len() {
            res.resize(rhs.0.len(), T::zero());
        }
        res.iter_mut().zip(rhs.0.iter()).for_each(|(x, y)| {
            *x -= *y;
        });
        Self::remove_trailig_zeros(&mut res);
        Poly(res)
    }
}

#[allow(clippy::suspicious_arithmetic_impl)]
impl<T: Ring + Copy> Mul for Poly<T> {
    type Output = Poly<T>;
    fn mul(self, rhs: Self) -> Self::Output {
        if self.0.is_empty() && rhs.0.is_empty() {
            Poly(Vec::new())
        } else {
            let mut res = vec![T::zero(); self.0.len() + rhs.0.len() - 1];
            for (i, &x) in self.0.iter().enumerate() {
                for (j, &y) in rhs.0.iter().enumerate() {
                    res[i + j] += x * y;
                }
            }
            Self::remove_trailig_zeros(&mut res);
            Poly(res)
        }
    }
}

// TODO: このマクロを fp のものと共通化します。
macro_rules! forward_assign_biop {
    ($(impl $trait:ident, $fn_assign:ident, $fn:ident)*) => {
        $(
            impl<T: Ring + Copy> $trait for Poly<T> {
                #[inline]
                fn $fn_assign(&mut self, rhs: Self) {
                    *self = self.clone().$fn(&rhs);
                }
            }
        )*
    };
}
forward_assign_biop! {
    impl AddAssign, add_assign, add
    impl SubAssign, sub_assign, sub
    impl MulAssign, mul_assign, mul
}

// TODO: このマクロを fp のものと共通化します。
macro_rules! forward_ref_binop {
    ($(impl $imp:ident, $method:ident)*) => {
        $(
            impl<'a, T: Ring + Ring + Copy> $imp<Poly<T>> for &'a Poly<T> {
                type Output = Poly<T>;
                #[inline]
                fn $method(self, other: Poly<T>) -> Self::Output {
                    $imp::$method(self.clone(), other.clone())
                }
            }

            impl<'a, T: Ring + Copy> $imp<&'a Poly<T>> for Poly<T> {
                type Output = Poly<T>;
                #[inline]
                fn $method(self, other: &Poly<T>) -> Self::Output {
                    $imp::$method(self.clone(), other.clone())
                }
            }

            impl<'a, T: Ring + Copy> $imp<&'a Poly<T>> for &'a Poly<T> {
                type Output = Poly<T>;
                #[inline]
                fn $method(self, other: &Poly<T>) -> Self::Output {
                    $imp::$method(self.clone(), other)
                }
            }
        )*
    };
}
forward_ref_binop! {
    impl Add, add
    impl Sub, sub
    impl Mul, mul
}
