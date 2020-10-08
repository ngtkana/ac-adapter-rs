mod arith;
use alg_traits::arith::{One, Zero};
use std::{cmp, fmt, iter, mem::swap, ops};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Fp<M: Mod>(M::Mod);

pub use aliases::*;

pub mod aliases {
    use super::{Fp, Mod};

    #[derive(Debug, Clone, PartialEq, Copy, Eq)]
    pub struct Mod100000007 {}
    pub type F100000007 = Fp<Mod100000007>;
    impl Mod for Mod100000007 {
        type Mod = i64;
        const MOD: i64 = 1_000_000_007;
    }

    #[derive(Debug, Clone, PartialEq, Copy, Eq)]
    pub struct Mod998244353 {}
    pub type F998244353 = Fp<Mod998244353>;
    impl Mod for Mod998244353 {
        type Mod = i64;
        const MOD: i64 = 998_244_353;
    }
}

impl<M: Mod> Fp<M> {
    /// 整数から構築します。
    pub fn new(src: M::Mod) -> Self {
        Self(Self::normalize(src))
    }

    /// 分数から構築します。
    pub fn frac(num: M::Mod, den: M::Mod) -> Self {
        Self::new(num) / Self::new(den)
    }

    /// 中身にキャストします。
    pub fn into_inner(self) -> M::Mod {
        self.0
    }

    /// Mod 逆元を返します。[`Div`](https://doc.rust-lang.org/std/ops/trait.Div.html) からも呼ばれています。
    #[allow(clippy::many_single_char_names)]
    pub fn inv(self) -> Self {
        assert_ne!(
            self.into_inner(),
            M::Mod::zero(),
            "さては 0 の逆元を取ろうとしていますね？"
        );
        let mut x = self.into_inner();
        let mut y = M::MOD;
        let mut u = M::Mod::one();
        let mut v = M::Mod::zero();
        while x != M::Mod::zero() {
            let q = y / x;
            y -= q * x;
            v -= q * u;
            swap(&mut x, &mut y);
            swap(&mut u, &mut v);
        }
        assert!(
            x == M::Mod::zero()
                && y == M::Mod::one()
                && (u == M::MOD || u == -M::MOD)
                && (-M::MOD < v && v < M::MOD)
        );
        Self(Self::normalize_from_the_top(v))
    }

    /// 塁乗をします。
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

    fn normalize(src: M::Mod) -> M::Mod {
        Self::normalize_from_the_top(src % M::MOD)
    }

    fn normalize_from_the_bottom(src: M::Mod) -> M::Mod {
        if M::MOD <= src {
            src - M::MOD
        } else {
            src
        }
    }

    fn normalize_from_the_top(src: M::Mod) -> M::Mod {
        if src < M::Mod::zero() {
            src + M::MOD
        } else {
            src
        }
    }
}

impl<M: Mod> Zero for Fp<M> {
    fn zero() -> Fp<M> {
        Fp::new(M::Mod::zero())
    }
}
impl<M: Mod> One for Fp<M> {
    fn one() -> Fp<M> {
        Fp::new(M::Mod::one())
    }
}

impl<M: Mod> iter::Sum<Fp<M>> for Fp<M> {
    fn sum<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = Fp<M>>,
    {
        iter.fold(Fp::zero(), ops::Add::add)
    }
}

impl<'a, M: 'a + Mod> iter::Sum<&'a Fp<M>> for Fp<M> {
    fn sum<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = &'a Fp<M>>,
    {
        iter.fold(Fp::zero(), ops::Add::add)
    }
}

impl<M: Mod> iter::Product<Fp<M>> for Fp<M> {
    fn product<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = Fp<M>>,
    {
        iter.fold(Self::one(), ops::Mul::mul)
    }
}

impl<'a, M: 'a + Mod> iter::Product<&'a Fp<M>> for Fp<M> {
    fn product<I>(iter: I) -> Self
    where
        I: iter::Iterator<Item = &'a Fp<M>>,
    {
        iter.fold(Self::one(), ops::Mul::mul)
    }
}

impl<M: Mod> fmt::Display for Fp<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.0)
    }
}

pub trait Mod: Sized + fmt::Debug + Clone + Copy + cmp::PartialEq + cmp::Eq {
    type Mod: Sized
        + Zero
        + One
        + Clone
        + Copy
        + fmt::Debug
        + fmt::Display
        + cmp::PartialEq
        + cmp::Eq
        + cmp::PartialOrd
        + cmp::Ord
        + ops::Add<Output = Self::Mod>
        + ops::Sub<Output = Self::Mod>
        + ops::Mul<Output = Self::Mod>
        + ops::Div<Output = Self::Mod>
        + ops::Rem<Output = Self::Mod>
        + ops::Neg<Output = Self::Mod>
        + ops::AddAssign
        + ops::SubAssign
        + ops::MulAssign
        + ops::DivAssign
        + ops::RemAssign;
    const MOD: Self::Mod;
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_impl::assert_impl;
    use test_case::test_case;

    #[derive(Debug, Clone, PartialEq, Eq, Copy)]
    struct Mod97 {}
    impl Mod for Mod97 {
        type Mod = i16;
        const MOD: i16 = 97;
    }
    type F97 = Fp<Mod97>;

    #[test]
    fn test_trait_implementations() {
        assert_impl!(fmt::Debug: F97);
        assert_impl!(fmt::Display: F97);
        assert_impl!(Clone: F97);
        assert_impl!(Copy: F97);
        assert_impl!(PartialEq: F97);
        assert_impl!(cmp::PartialEq: F97);
        assert_impl!(cmp::Eq: F97);
        assert_impl!(!cmp::PartialOrd: F97);
        assert_impl!(!cmp::Ord: F97);
        assert_impl!(Zero: F97);
        assert_impl!(One: F97);
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

    #[test_case(7, 0 => 1)]
    #[test_case(7, 1 => 7)]
    #[test_case(7, 2 => 49)]
    #[test_case(7, 3 => 343 % 97)]
    #[test_case(7, 4 => 2401 % 97)]
    fn test_pow(a: i16, b: u64) -> i16 {
        F97::new(a).pow(b).into_inner()
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
