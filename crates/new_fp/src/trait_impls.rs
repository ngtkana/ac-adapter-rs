use {
    super::{algo::berlekamp_massey_fp, Fp, Mod},
    std::{
        fmt,
        hash::Hash,
        iter::{Product, Sum},
        ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    },
};

macro_rules! impl_from_large_int {
    ($($T: ty), *$(,)?) => {$(
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

impl<M: Mod, T: Into<Self>> AddAssign<T> for Fp<M> {
    fn add_assign(&mut self, rhs: T) {
        self.value += rhs.into().value;
        if M::P <= self.value {
            self.value -= M::P;
        }
    }
}
impl<M: Mod, T: Into<Self>> SubAssign<T> for Fp<M> {
    fn sub_assign(&mut self, rhs: T) {
        let rhs = rhs.into();
        if self.value < rhs.value {
            self.value += M::P;
        }
        self.value -= rhs.value;
    }
}
impl<M: Mod, T: Into<Self>> MulAssign<T> for Fp<M> {
    fn mul_assign(&mut self, rhs: T) {
        self.value = self.value * rhs.into().value % M::P
    }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl<M: Mod, T: Into<Self>> DivAssign<T> for Fp<M> {
    fn div_assign(&mut self, rhs: T) {
        *self *= rhs.into().inv();
    }
}

impl<'a, M: Mod> From<&'a Self> for Fp<M> {
    fn from(x: &Self) -> Self {
        *x
    }
}

macro_rules! forward_ops {
    ($(($trait:ident, $method_assign:ident, $method:ident),)*) => {$(
        impl<M: Mod, T: Into<Fp<M>>> $trait<T> for Fp<M> {
            type Output = Self;
            fn $method(mut self, rhs: T) -> Self {
                self.$method_assign(rhs);
                self
            }
        }
        impl<'a, M: Mod, T: Into<Fp<M>>> $trait<T> for &'a Fp<M> {
            type Output = Fp<M>;
            fn $method(self, other: T) -> Self::Output {
                $trait::$method(*self, other)
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
        if self.value == 0 {
            self
        } else {
            Self::new_unchecked(M::P - self.value)
        }
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
    fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new(0), |b, x| b + x)
    }
}
impl<'a, M: Mod> Product<&'a Self> for Fp<M> {
    fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
        iter.fold(Self::new(1), |b, x| b * x)
    }
}
impl<M: Mod> fmt::Debug for Fp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        if self.value == 0 {
            return write!(f, "0");
        }
        let [mut num, mut den] = berlekamp_massey_fp(self.value as i64, M::P as i64);
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
impl<M: Mod> fmt::Display for Fp<M> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.value.fmt(f)
    }
}

////////////////////////////////////////////////////////////////////////////////
// PhantomData のせいで derive できなかったもの
////////////////////////////////////////////////////////////////////////////////
impl<M: Mod> Clone for Fp<M> {
    fn clone(&self) -> Self {
        Self::new_unchecked(self.value)
    }
}
impl<M: Mod> Copy for Fp<M> {}
impl<M: Mod> PartialEq for Fp<M> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl<M: Mod> Eq for Fp<M> {}
impl<M: Mod> Default for Fp<M> {
    fn default() -> Self {
        Self::new_unchecked(0)
    }
}
impl<M: Mod> Hash for Fp<M> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

#[cfg(test)]
mod tests {
    use {
        assert_impl::assert_impl,
        std::{
            collections::HashSet,
            fmt::{Debug, Display},
            hash::Hash,
            iter::{Product, Sum},
            ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
        },
    };

    ////////////////////////////////////////////////////////////////////////////////
    // テスト
    ////////////////////////////////////////////////////////////////////////////////
    use crate::{define_mod, fp};
    define_mod! { type 13 }

    macro_rules! assert_fp_eq {
        ($left:expr, $right:expr $(,)?) => {{
            let left: F = $left;
            let right: F = $right;
            assert_eq!(left, right)
        }};
        ($left:expr, $right:expr, $($arg:tt)+) => {{
            let left: F = $left;
            let right: F = $right;
            assert_eq!(left, right)
        }};
    }
    macro_rules! assert_fp_ne {
        ($left:expr, $right:expr $(,)?) => {{
            let left: F = $left;
            let right: F = $right;
            assert_ne!(left, right)
        }};
        ($left:expr, $right:expr, $($arg:tt)+) => {{
            let left: F = $left;
            let right: F = $right;
            assert_ne!(left, right)
        }};
    }

    #[test]
    fn test_fp_assert_impls() {
        assert_impl!(Debug: F);
        assert_impl!(Display: F);
        assert_impl!(Clone: F);
        assert_impl!(Copy: F);
        assert_impl!(PartialEq: F);
        assert_impl!(Eq: F);
        assert_impl!(Hash: F);
        assert_impl!(!PartialOrd: F);
        assert_impl!(!Ord: F);
        assert_impl!(From<u8>: F);
        assert_impl!(From<u16>: F);
        assert_impl!(From<u32>: F);
        assert_impl!(From<u64>: F);
        assert_impl!(From<u128>: F);
        assert_impl!(From<usize>: F);
        assert_impl!(From<i8>: F);
        assert_impl!(From<i16>: F);
        assert_impl!(From<i32>: F);
        assert_impl!(From<i64>: F);
        assert_impl!(From<i128>: F);
        assert_impl!(From<isize>: F);
        assert_impl!(Add: F);
        assert_impl!(Sub: F);
        assert_impl!(Mul: F);
        assert_impl!(Div: F);
        assert_impl!(Neg: F);
        assert_impl!(AddAssign: F);
        assert_impl!(SubAssign: F);
        assert_impl!(MulAssign: F);
        assert_impl!(DivAssign: F);
        assert_impl!(Sum: F);
        assert_impl!(Product: F);
    }

    #[test]
    fn test_fp_simple_impls() {
        // Debug
        fn dbg_fmt(x: F) -> String {
            format!("{:?}", x)
        }
        assert_eq!(&dbg_fmt(fp!(0)), "0");
        assert_eq!(&dbg_fmt(fp!(1)), "1");
        assert_eq!(&dbg_fmt(fp!(2)), "2");
        assert_eq!(&dbg_fmt(fp!(3)), "3");
        assert_eq!(&dbg_fmt(fp!(1) / 2), "1/2");
        assert_eq!(&dbg_fmt(fp!(1) / 3), "1/3");
        assert_eq!(&dbg_fmt(fp!(3) / 2), "3/2");
        assert_eq!(&dbg_fmt(-fp!(1)), "-1");
        assert_eq!(&dbg_fmt(-fp!(2)), "-2");
        assert_eq!(&dbg_fmt(-fp!(3)), "-3");
        assert_eq!(&dbg_fmt(-fp!(1) / 2), "-1/2");
        assert_eq!(&dbg_fmt(-fp!(1) / 3), "-1/3");
        assert_eq!(&dbg_fmt(-fp!(3) / 2), "-3/2");

        // Display
        for i in 0..F::P {
            assert_eq!(format!("{}", F::new(i)), format!("{}", i));
        }

        // Default
        assert_eq!(F::default().value, 0);

        // ParialEq
        assert_fp_eq!(fp!(42), fp!(42));
        assert_fp_eq!(fp!(42), fp!(42 + 13));
        assert_fp_ne!(fp!(42), fp!(43));

        // Hash
        {
            let mut set = HashSet::<F>::new();
            for i in 0..F::P {
                set.insert(fp!(i));
                assert_eq!(set.len(), i as usize + 1);
            }
        }
    }

    #[test]
    fn test_fp_arith() {
        // Add
        for x in 0..F::P {
            for y in 0..F::P {
                assert_fp_eq!(fp!(x) + y, fp!(x + y));
                assert_fp_eq!(&fp!(x) + y, fp!(x + y));
                assert_fp_eq!(fp!(x) + &fp!(y), fp!(x + y));
                assert_fp_eq!(&fp!(x) + &fp!(y), fp!(x + y));
            }
        }
        // Sub
        for x in 0..F::P {
            for y in 0..F::P {
                assert_fp_eq!(fp!(x) - y, fp!(x + F::P - y));
                assert_fp_eq!(&fp!(x) - y, fp!(x + F::P - y));
                assert_fp_eq!(fp!(x) - &fp!(y), fp!(x + F::P - y));
                assert_fp_eq!(&fp!(x) - &fp!(y), fp!(x + F::P - y));
            }
        }
        // Mul
        for x in 0..F::P {
            for y in 0..F::P {
                assert_fp_eq!(fp!(x) * y, fp!(x * y));
                assert_fp_eq!(&fp!(x) * y, fp!(x * y));
                assert_fp_eq!(fp!(x) * &fp!(y), fp!(x * y));
                assert_fp_eq!(&fp!(x) * &fp!(y), fp!(x * y));
            }
        }
        // Div
        for x in 0..F::P {
            for y in 1..F::P {
                assert_fp_eq!(fp!(x) / y * y, fp!(x));
                assert_fp_eq!(&fp!(x) / y * y, fp!(x));
                assert_fp_eq!(fp!(x) / y * &fp!(y), fp!(x));
                assert_fp_eq!(&fp!(x) / y * &fp!(y), fp!(x));
            }
        }
    }

    #[test]
    fn test_fp_pow() {
        for x in 0..F::P {
            for y in 0..10_u32 {
                assert_fp_eq!(fp!(x).pow(y as u64), fp!(x.pow(y)));
            }
        }
    }

    #[test]
    fn test_sum_product() {
        // Sum
        for x in 0..F::P {
            let int = (0..x).collect::<Vec<_>>();
            let fp = (0..x).map(F::new).collect::<Vec<_>>();
            assert_fp_eq!(fp.iter().copied().sum(), fp!(int.iter().sum::<u64>()));
            assert_fp_eq!(fp.iter().sum(), fp!(int.iter().sum::<u64>()));
        }
        // Product
        for x in 1..F::P {
            let int = (1..x).collect::<Vec<_>>();
            let fp = (1..x).map(F::new).collect::<Vec<_>>();
            assert_fp_eq!(
                fp.iter().copied().product(),
                fp!(int.iter().product::<u64>())
            );
            assert_fp_eq!(fp.iter().product(), fp!(int.iter().product::<u64>()));
        }
    }
}
