use super::fps_mul;
use super::Fp;
use super::PrimitiveRoot;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Index;
use std::ops::IndexMut;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;

/// The formal power series (FPS).
/// This object knows a FPS $f$ modulo $x^d$ where $d$ is precision.
/// The precision can be infinite.
/// # Implementation
/// This is a pair of a vector of `coeffs` and `precision`.
/// The infinite precision is represented by `usize::MAX`.
/// # Invariants
/// - `coeffs.last() != Some(&Fp::new(0))`
/// - `coeffs.len() <= precision`
/// # Examples
/// ```
/// use fp2::fp;
/// type Fps = fp2::Fps<998244353>;
/// let f = Fps::new(vec![fp!(1), fp!(2)], 4);
/// let g = f.inv();
/// let expected = Fps::new(vec![fp!(1), fp!(-2), fp!(4), fp!(-8)], 4);
/// assert_eq!(g, expected);
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct Fps<const P: u64> {
    coeffs: Vec<Fp<P>>,
    precision: usize,
}
impl<const P: u64> Fps<P> {
    /// Creates a new FPS with the given coefficients and precision.  # Panics
    /// Panics if the last coefficient is zero.
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// assert_eq!(f.precision(), 4);
    /// assert_eq!(f.into_coeffs(), vec![fp!(1), fp!(2)]);
    /// ```
    pub fn new(coeffs: Vec<Fp<P>>, precision: usize) -> Self {
        let mut result = Self::polynominal(coeffs);
        result.set_precision(precision);
        result
    }

    /// Creates a new FPS the given coefficients and infinite precision.
    /// # Panics
    /// Panics if the last coefficient is zero.
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::polynominal(vec![fp!(1), fp!(2)]);
    /// assert_eq!(f.precision(), usize::MAX);
    /// assert_eq!(f.into_coeffs(), vec![fp!(1), fp!(2)]);
    /// ```
    pub fn polynominal(coeffs: Vec<Fp<P>>) -> Self {
        assert!(coeffs.last() != Some(&Fp::new(0)));
        Self {
            coeffs,
            precision: usize::MAX,
        }
    }

    /// Returns the vector of coefficients.
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// assert_eq!(f.into_coeffs(), vec![fp!(1), fp!(2)]);
    /// ```
    pub fn into_coeffs(self) -> Vec<Fp<P>> { self.coeffs }

    /// Returns the precision $d$.
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// assert_eq!(f.precision(), 4);
    /// ```
    pub fn precision(&self) -> usize { self.precision }

    /// Changes the precision.
    /// If the new precision is smaller than the current one, the coefficients are truncated.
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let mut f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// f.set_precision(1);
    /// assert_eq!(f.precision(), 1);
    /// assert_eq!(f.into_coeffs(), vec![fp!(1)]);
    /// let mut f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// f.set_precision(10);
    /// assert_eq!(f.precision(), 10);
    /// assert_eq!(f.into_coeffs(), vec![fp!(1), fp!(2)]);
    /// ```
    pub fn set_precision(&mut self, precision: usize) {
        self.coeffs.truncate(precision);
        self.__normalize();
        self.precision = precision;
    }

    /// Returns the truncated FPS of `self`.
    /// # Complexity
    /// $O(d)$
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// let g = f.copied_with(1);
    /// assert_eq!(g.precision(), 1);
    /// assert_eq!(g.into_coeffs(), vec![fp!(1)]);
    /// ```
    pub fn copied_with(&self, precision: usize) -> Self {
        Self::new(self.coeffs().take(precision).collect(), precision)
    }

    /// Returns the iterator of coefficients.
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// assert_eq!(f.coeffs().collect::<Vec<_>>(), vec![fp!(1), fp!(2)]);
    /// ```
    pub fn coeffs(&self) -> impl '_ + Iterator<Item = Fp<P>> { self.coeffs.iter().copied() }

    /// Returns the mutable iterator of coefficients.
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let mut f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// for a in f.coeffs_mut() {
    ///    *a += fp!(1);
    /// }
    /// assert_eq!(f.into_coeffs(), vec![fp!(2), fp!(3)]);
    pub fn coeffs_mut(&mut self) -> impl Iterator<Item = &mut Fp<P>> { self.coeffs.iter_mut() }

    fn __normalize(&mut self) {
        while self.coeffs.last() == Some(&Fp::new(0)) {
            self.coeffs.pop().unwrap();
        }
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
    /// $f^{-1} \mod x^d$
    /// # Complexity
    /// $O(d \log d)$
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::new(vec![fp!(1), fp!(2)], 4);
    /// let g = f.inv();
    /// let expected = Fps::new(vec![fp!(1), fp!(-2), fp!(4), fp!(-8)], 4);
    /// assert_eq!(g, expected);
    /// ```
    pub fn inv(&self) -> Self {
        assert_ne!(self.precision, usize::MAX, "The precision must be finite.");
        assert!(
            !self.coeffs.is_empty() && self[0] != Fp::new(0),
            "The constant term must be nonzero."
        );
        let mut g = Fps::new(vec![self[0].inv()], 1);
        while g.precision() < self.precision {
            let precision = self.precision.min(g.precision() * 2);
            let f = self.copied_with(precision);
            g.set_precision(precision);
            g = &g * (-(&f * &g) + 2);
        }
        g
    }

    /// Square root of `self`.
    /// # Requirements
    /// $f_0 = 1$
    /// # Returns
    /// $f^{1/2} \mod x^d$
    /// # Complexity
    /// $O(d \log d)$
    /// # Examples
    /// ```
    /// use fp2::fp;
    /// type Fps = fp2::Fps<998244353>;
    /// let f = Fps::new(vec![fp!(1), fp!(2), fp!(3), fp!(4), fp!(5)], 5);
    /// let g = f.sqrt();
    /// let expected = Fps::new(vec![fp!(1); 5], 5);
    /// assert_eq!(g, expected);
    /// ```
    pub fn sqrt(&self) -> Self {
        assert_ne!(self.precision, usize::MAX, "The precision must be finite.");
        assert!(
            !self.coeffs.is_empty() && self[0] == Fp::new(1),
            "The constant term must be 1."
        );
        let mut g = Fps::new(vec![Fp::new(1)], 1);
        while g.precision() < self.precision {
            let precision = self.precision.min(g.precision() * 2);
            let f = self.copied_with(precision);
            g.set_precision(precision);
            g = (&g + &f * g.inv()) / 2;
        }
        g
    }
}
impl<const P: u64> std::fmt::Debug for Fps<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{:?} mod x^{}",
            self.coeffs().map(Fp::value).collect::<Vec<_>>(),
            self.precision
        )?;
        Ok(())
    }
}
impl<const P: u64> AddAssign<&Self> for Fps<P> {
    fn add_assign(&mut self, rhs: &Self) {
        let precision = self.precision.min(rhs.precision);
        self.coeffs.resize(precision, Fp::new(0));
        for (a, b) in self.coeffs_mut().zip(rhs.coeffs()) {
            *a += b;
        }
        self.__normalize();
    }
}
impl<const P: u64> SubAssign<&Self> for Fps<P> {
    fn sub_assign(&mut self, rhs: &Self) {
        let precision = self.precision.min(rhs.precision);
        self.coeffs.resize(precision, Fp::new(0));
        for (a, b) in self.coeffs_mut().zip(rhs.coeffs()) {
            *a -= b;
        }
        self.__normalize();
    }
}
impl<const P: u64> MulAssign<&Self> for Fps<P>
where
    (): PrimitiveRoot<P>,
{
    fn mul_assign(&mut self, rhs: &Self) {
        *self = Self::new(
            fps_mul(&self.coeffs, &rhs.coeffs),
            self.precision.min(rhs.precision),
        );
    }
}
impl<const P: u64> Neg for Fps<P> {
    type Output = Self;

    fn neg(mut self) -> Self::Output {
        for a in self.coeffs.iter_mut() {
            *a = -*a;
        }
        self
    }
}
impl<const P: u64> Neg for &Fps<P> {
    type Output = Fps<P>;

    fn neg(self) -> Self::Output {
        let mut me = self.clone();
        for a in me.coeffs.iter_mut() {
            *a = -*a;
        }
        me
    }
}
impl<const P: u64> Index<usize> for Fps<P> {
    type Output = Fp<P>;

    fn index(&self, index: usize) -> &Self::Output { &self.coeffs[index] }
}
impl<const P: u64> IndexMut<usize> for Fps<P> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { &mut self.coeffs[index] }
}

macro_rules! fps_forward_ops {
    ($trait:ident, $trait_assign:ident, $fn:ident, $fn_assign:ident) => {
        impl<const P: u64> $trait_assign for Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            fn $fn_assign(&mut self, rhs: Self) { self.$fn_assign(&rhs.into()); }
        }
        impl<const P: u64> $trait for Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            type Output = Fps<P>;

            fn $fn(mut self, rhs: Self) -> Self::Output {
                <Self as $trait_assign>::$fn_assign(&mut self, rhs);
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
        impl<const P: u64> $trait<Fps<P>> for &Fps<P>
        where
            (): PrimitiveRoot<P>,
        {
            type Output = Fps<P>;

            fn $fn(self, rhs: Fps<P>) -> Self::Output { self.clone().$fn(rhs) }
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
fps_forward_ops!(Add, AddAssign, add, add_assign);
fps_forward_ops!(Sub, SubAssign, sub, sub_assign);
fps_forward_ops!(Mul, MulAssign, mul, mul_assign);
impl<const P: u64, T: Into<Fp<P>>> AddAssign<T> for Fps<P> {
    fn add_assign(&mut self, rhs: T) {
        assert_ne!(self.precision, 0, "The precision must be positive.");
        self.coeffs[0] += rhs.into();
    }
}
impl<const P: u64, T: Into<Fp<P>>> SubAssign<T> for Fps<P> {
    fn sub_assign(&mut self, rhs: T) {
        assert_ne!(self.precision, 0, "The precision must be positive.");
        self.coeffs[0] -= rhs.into();
    }
}
impl<const P: u64, T: Into<Fp<P>>> MulAssign<T> for Fps<P> {
    fn mul_assign(&mut self, rhs: T) {
        let rhs = rhs.into();
        for a in self.coeffs.iter_mut() {
            *a *= rhs;
        }
    }
}
#[allow(clippy::suspicious_op_assign_impl)]
impl<const P: u64, T: Into<Fp<P>>> DivAssign<T> for Fps<P> {
    fn div_assign(&mut self, rhs: T) {
        let rhs_inv = rhs.into().inv();
        for a in self.coeffs.iter_mut() {
            *a *= rhs_inv;
        }
    }
}
macro_rules! fps_forward_scalar_ops {
    ($trait:ident, $trait_assign:ident, $fn:ident, $fn_assign:ident) => {
        impl<const P: u64, T: Into<Fp<P>>> $trait<T> for Fps<P> {
            type Output = Fps<P>;

            fn $fn(mut self, rhs: T) -> Self::Output {
                <Self as $trait_assign<T>>::$fn_assign(&mut self, rhs);
                self
            }
        }
    };
}
fps_forward_scalar_ops!(Add, AddAssign, add, add_assign);
fps_forward_scalar_ops!(Sub, SubAssign, sub, sub_assign);
fps_forward_scalar_ops!(Mul, MulAssign, mul, mul_assign);
fps_forward_scalar_ops!(Div, DivAssign, div, div_assign);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fp;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter;

    type Fps9 = Fps<998244353>;

    #[test]
    fn test_fps_mul() {
        let a = Fps9::new(vec![fp!(1), fp!(2)], 5);
        let b = Fps9::new(vec![fp!(3), fp!(4)], 5);
        assert_eq!(&a * &b, Fps9::new(vec![fp!(3), fp!(10), fp!(8)], 5));
    }

    #[test]
    fn test_fps_inv() {
        let a = Fps9::new(vec![fp!(1), fp!(2)], 5);
        let b = a.inv();
        assert_eq!(&a * &b, Fps9::new(vec![fp!(1)], 5));
    }

    #[test]
    fn test_fps_sqrt() {
        let a = Fps9::new(vec![fp!(1), fp!(2), fp!(3), fp!(4), fp!(5)], 5);
        let b = a.sqrt();
        assert_eq!(&b * &b, a);
    }

    fn random_fps_one(rng: &mut StdRng, precision: usize) -> Fps<998244353> {
        Fps::new(
            iter::once(Fp::new(1))
                .chain(iter::repeat_with(|| Fp::new(rng.gen_range(0..998244353))))
                .take(precision)
                .collect(),
            precision,
        )
    }

    #[test]
    fn test_fps_mul_random() {
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps_one(&mut rng, PRECISION);
            let g = random_fps_one(&mut rng, PRECISION);
            let result = &f * &g;
            assert_eq!(result.precision(), PRECISION);
            assert!(result.coeffs.len() <= PRECISION);

            let result = result
                .coeffs()
                .chain(iter::repeat(Fp::new(0)))
                .take(PRECISION)
                .collect::<Vec<_>>();
            let mut expected = fps_mul(&f.coeffs, &g.coeffs);
            expected.resize(PRECISION, Fp::new(0));
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_fps_inv_random() {
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps_one(&mut rng, PRECISION);
            let g = f.inv();
            assert_eq!(g.precision(), PRECISION);
            assert!(g.coeffs.len() <= PRECISION);
            assert_eq!(&f * &g, Fps::new(vec![fp!(1)], PRECISION));
        }
    }

    #[test]
    fn test_fps_sqrt_random() {
        const PRECISION: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let f = random_fps_one(&mut rng, PRECISION);
            let g = f.sqrt();
            assert_eq!(g.precision(), PRECISION);
            assert!(g.coeffs.len() <= PRECISION);
            assert_eq!(&g * &g, f);
        }
    }
}
