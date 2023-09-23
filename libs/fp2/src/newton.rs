use super::fps_mul;
use super::Fp;
use super::PrimitiveRoot;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Deref;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Fps<const P: u64>(Vec<Fp<P>>);
impl<const P: u64> Fps<P> {
    pub fn new(a: Vec<Fp<P>>) -> Self {
        assert!(a.last() != Some(&Fp::new(0)));
        Self(a)
    }

    pub fn into_inner(self) -> Vec<Fp<P>> { self.0 }

    pub fn truncated(&self, n: usize) -> Self {
        let mut ans = self.clone();
        ans.0.truncate(n);
        ans
    }

    fn __normalize(&mut self) {
        while self.0.last() == Some(&Fp::new(0)) {
            self.0.pop();
        }
    }

    fn __normalized(mut self) -> Self {
        self.__normalize();
        self
    }
}
impl<const P: u64> Fps<P>
where
    (): PrimitiveRoot<P>,
{
    /// Inverse FPS of `self`.
    /// # Requirements
    /// $f_0 \ne 0$
    /// # Returns
    /// $f^{-1} \mod x^{\text{precision}}$
    /// # Complexity
    /// $O(\text{precision} \log \text{precision})$
    /// # Examples
    /// ```
    /// use fp2::fps;
    /// use fp2::Fps;
    /// let f: Fps<998244353> = fps!(1, 1);
    /// let g = f.inv(4);
    /// let expected: Fps<998244353> = fps!(1, -1, 1, -1);
    /// assert_eq!(g, expected);
    /// ```
    pub fn inv(&self, precision: usize) -> Self {
        debug_assert!(!self.is_empty());
        assert!(self[0] != Fp::new(0));
        newton_by(precision, self[0].inv(), |g| {
            (-&g * self.truncated(g.len() * 2) + 2) * g
        })
        .__normalized()
    }
}
impl<const P: u64> Deref for Fps<P> {
    type Target = Vec<Fp<P>>;

    fn deref(&self) -> &Self::Target { &self.0 }
}
impl<const P: u64> AddAssign<&Self> for Fps<P> {
    fn add_assign(&mut self, rhs: &Self) {
        let n = self.len().max(rhs.len());
        self.0.resize(n, Fp::new(0));
        for (a, b) in self.0.iter_mut().zip(rhs.iter()) {
            *a += *b;
        }
        self.__normalize();
    }
}
impl<const P: u64> SubAssign<&Self> for Fps<P> {
    fn sub_assign(&mut self, rhs: &Self) {
        let n = self.len().max(rhs.len());
        self.0.resize(n, Fp::new(0));
        for (a, b) in self.0.iter_mut().zip(rhs.iter()) {
            *a -= *b;
        }
        self.__normalize();
    }
}
impl<const P: u64> MulAssign<&Self> for Fps<P>
where
    (): PrimitiveRoot<P>,
{
    fn mul_assign(&mut self, rhs: &Self) { *self = Self(fps_mul(self, rhs)); }
}
impl<const P: u64> Neg for Fps<P> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for a in self.0.iter_mut() {
            *a = -*a;
        }
        self
    }
}
impl<const P: u64> Neg for &Fps<P> {
    type Output = Fps<P>;

    fn neg(self) -> Self::Output {
        let mut me = self.clone();
        for a in me.0.iter_mut() {
            *a = -*a;
        }
        me
    }
}
macro_rules! fp_forward_ops {
    ($trait:ident, $trait_assign:ident, $fn:ident, $fn_assign:ident) => {
        impl<const P: u64, T: Into<Self>> $trait_assign<T> for Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            fn $fn_assign(&mut self, rhs: T) { self.$fn_assign(&rhs.into()); }
        }
        impl<const P: u64, T: Into<Self>> $trait<T> for Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            type Output = Fps<P>;

            fn $fn(mut self, rhs: T) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }
        impl<const P: u64> $trait<&Self> for Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            type Output = Fps<P>;

            fn $fn(mut self, rhs: &Self) -> Self::Output {
                self.$fn_assign(rhs);
                self
            }
        }
        impl<const P: u64, T: Into<Fps<P>>> $trait<T> for &Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            type Output = Fps<P>;

            fn $fn(self, rhs: T) -> Self::Output { self.clone().$fn(rhs.into()) }
        }
        impl<const P: u64> $trait<&Fps<P>> for &Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            type Output = Fps<P>;

            fn $fn(self, rhs: &Fps<P>) -> Self::Output { (self.clone()).$fn(rhs) }
        }
    };
}
fp_forward_ops!(Add, AddAssign, add, add_assign);
fp_forward_ops!(Sub, SubAssign, sub, sub_assign);
fp_forward_ops!(Mul, MulAssign, mul, mul_assign);

macro_rules! impl_from {
    ($($t:ty),*) => {
        $(
            impl<const P: u64> From<$t> for Fps<P> {
                fn from(x: $t) -> Self { Self::new(vec![Fp::<P>::from(x)]) }
            }
        )*
    };
}
impl_from!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize);
pub fn newton_by<const P: u64>(
    precision: usize,
    init: Fp<P>,
    step: impl Fn(Fps<P>) -> Fps<P>,
) -> Fps<P> {
    let mut ans = Fps::new(vec![init]);
    while ans.len() < precision {
        ans = step(ans);
    }
    ans.truncated(precision)
}
