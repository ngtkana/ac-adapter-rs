//! # Naive implementation of polynomial operations

use std::iter::Product;
use std::iter::Sum;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::SubAssign;

fn zero<T>() -> T
where
    T: Sum<T>,
{
    std::iter::empty().sum()
}

fn one<T>() -> T
where
    T: Product<T>,
{
    std::iter::empty().product()
}

/// Multiply two polynomials in $O(nm)$ time.
///
/// If $a = 0$ or $b = 0$, returns $0$ (empty vector).
pub fn mul<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Copy + Sum<T> + Mul<Output = T> + AddAssign,
{
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut c = vec![zero(); a.len() + b.len() - 1];
    for (i, &ai) in a.iter().enumerate() {
        for (j, &bj) in b.iter().enumerate() {
            c[i + j] += ai * bj;
        }
    }
    c
}

/// Add two polynomials in $O(\max(n, m))$ time.
///
/// Trailing zeros are removed.
pub fn add<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Copy + PartialEq + Sum<T> + AddAssign,
{
    let mut c = vec![zero(); a.len().max(b.len())];
    for (i, &ai) in a.iter().enumerate() {
        c[i] += ai;
    }
    for (i, &bi) in b.iter().enumerate() {
        c[i] += bi;
    }
    while c.last() == Some(&zero()) {
        c.pop().unwrap();
    }
    c
}

/// Subtract two polynomials in $O(\max(n, m))$ time.
///
/// Trailing zeros are removed.
pub fn sub<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Copy + PartialEq + Sum<T> + AddAssign + SubAssign + Mul<Output = T>,
{
    let mut c = vec![zero(); a.len().max(b.len())];
    for (i, &ai) in a.iter().enumerate() {
        c[i] += ai;
    }
    for (i, &bi) in b.iter().enumerate() {
        c[i] -= bi;
    }
    while c.last() == Some(&zero()) {
        c.pop().unwrap();
    }
    c
}

/// Divide two polynomials in $O((n - m) m)$ time.
///
/// * Returns the quotient and modifies $a$ to store the remainder.
/// * Trailing zeros in $a$ are removed from the remainder.
/// * $b_{m-1} \neq 0$ is required.
pub fn div<T>(a: &mut Vec<T>, b: &[T]) -> Vec<T>
where
    T: Copy + PartialEq + Sum<T> + SubAssign + Mul<Output = T> + Div<Output = T>,
{
    assert!(!b.is_empty() && *b.last().unwrap() != zero::<T>());
    if a.len() < b.len() {
        return vec![];
    }
    let mut c = vec![zero(); a.len() + 1 - b.len()];
    for i in (0..c.len()).rev() {
        c[i] = a[i] / *b.last().unwrap();
        for j in 0..b.len() {
            a[i + j] -= c[i] * b[j];
        }
    }
    while a.last() == Some(&zero()) {
        a.pop().unwrap();
    }
    c
}

/// Evaluate a polynomial at a point in $O(n)$ time.
pub fn eval<T>(p: &[T], x: T) -> T
where
    T: Copy + Sum<T> + Mul<Output = T> + AddAssign + MulAssign,
{
    let mut y = zero();
    for &pi in p.iter().rev() {
        y *= x;
        y += pi;
    }
    y
}

/// Compute the $e$-th power of a polynomial in $O((en)^2 \log e)$ time.
pub fn pow<T>(mut a: Vec<T>, mut e: u64) -> Vec<T>
where
    T: Copy + PartialEq + Sum<T> + Product<T> + AddAssign + Mul<Output = T>,
{
    if e == 0 {
        return vec![one(); 1];
    }
    let mut b = vec![zero(); 1];
    b[0] = one();
    while e > 1 {
        if e % 2 == 1 {
            b = mul(&b, &a);
        }
        a = mul(&a, &a);
        e /= 2;
    }
    mul(&b, &a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::ops::Add;
    use std::ops::DivAssign;
    use std::ops::MulAssign;
    use std::ops::Sub;

    #[derive(Debug, Clone, Copy, PartialEq)]
    struct Fp<const P: u64>(u64);
    impl<const P: u64> Fp<P> {
        fn new(x: u64) -> Self {
            Self(x % P)
        }
    }
    impl<const P: u64> AddAssign for Fp<P> {
        fn add_assign(&mut self, rhs: Self) {
            self.0 += rhs.0;
            if self.0 >= P {
                self.0 -= P;
            }
        }
    }
    impl<const P: u64> Add for Fp<P> {
        type Output = Self;

        fn add(mut self, rhs: Self) -> Self {
            self += rhs;
            self
        }
    }
    impl<const P: u64> SubAssign for Fp<P> {
        fn sub_assign(&mut self, rhs: Self) {
            if self.0 < rhs.0 {
                self.0 += P;
            }
            self.0 -= rhs.0;
        }
    }
    impl<const P: u64> Sub for Fp<P> {
        type Output = Self;

        fn sub(mut self, rhs: Self) -> Self {
            self -= rhs;
            self
        }
    }
    impl<const P: u64> Mul for Fp<P> {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self {
            Self::new(self.0 * rhs.0 % P)
        }
    }
    impl<const P: u64> MulAssign for Fp<P> {
        fn mul_assign(&mut self, rhs: Self) {
            *self = *self * rhs;
        }
    }
    impl<const P: u64> Div for Fp<P> {
        type Output = Self;

        fn div(mut self, rhs: Self) -> Self {
            self /= rhs;
            self
        }
    }
    impl<const P: u64> DivAssign for Fp<P> {
        fn div_assign(&mut self, mut rhs: Self) {
            let mut e = P - 2;
            while e > 0 {
                if e % 2 == 1 {
                    *self *= rhs;
                }
                rhs *= rhs;
                e /= 2;
            }
        }
    }
    impl<const P: u64> Sum<Fp<P>> for Fp<P> {
        fn sum<I: Iterator<Item = Fp<P>>>(iter: I) -> Self {
            iter.fold(Fp::<P>(0), |a, b| a + b)
        }
    }

    fn gen_poly<const P: u64>(n: usize, rng: &mut StdRng) -> Vec<Fp<P>> {
        (0..n)
            .map(|i| {
                if i + 1 == n {
                    Fp::<P>(rng.gen_range(1..P))
                } else {
                    Fp::<P>(rng.gen_range(0..P))
                }
            })
            .collect()
    }

    #[test]
    fn test_add() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let n = rng.gen_range(0..10);
            let a = gen_poly::<P>(n, &mut rng);
            let b = gen_poly::<P>(n, &mut rng);
            let c = add(&a, &b);
            assert!(c.len() <= a.len().max(b.len()));
            let x = Fp::<P>(rng.gen_range(0..P));
            let a = eval(&a, x);
            let b = eval(&b, x);
            let c = eval(&c, x);
            assert_eq!(a + b, c);
        }
    }

    #[test]
    fn test_sub() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let n = rng.gen_range(0..10);
            let a = gen_poly::<P>(n, &mut rng);
            let b = gen_poly::<P>(n, &mut rng);
            let c = sub(&a, &b);
            assert!(c.len() <= a.len().max(b.len()));
            let x = Fp::<P>(rng.gen_range(0..P));
            let a = eval(&a, x);
            let b = eval(&b, x);
            let c = eval(&c, x);
            assert_eq!(a - b, c);
        }
    }

    #[test]
    fn test_mul() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let n = rng.gen_range(0..10);
            let m = rng.gen_range(0..10);
            let a = gen_poly::<P>(n, &mut rng);
            let b = gen_poly::<P>(m, &mut rng);
            let c = mul(&a, &b);
            if a.is_empty() || b.is_empty() {
                assert_eq!(c.len(), 0);
            } else {
                assert_eq!(c.len(), a.len() + b.len() - 1);
            }
            let x = Fp::<P>(rng.gen_range(0..P));
            let a = eval(&a, x);
            let b = eval(&b, x);
            let c = eval(&c, x);
            assert_eq!(a * b, c);
        }
    }

    #[test]
    fn test_div() {
        const P: u64 = 13;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let n = rng.gen_range(0..10);
            let m = rng.gen_range(1..10);
            let a = gen_poly::<P>(n, &mut rng);
            let b = gen_poly::<P>(m, &mut rng);
            let mut r = a.clone();
            let c = div(&mut r, &b);
            assert_eq!(c.len(), a.len().saturating_sub(b.len() - 1));
            let x = Fp::<P>(rng.gen_range(0..P));
            let a = eval(&a, x);
            let b = eval(&b, x);
            let c = eval(&c, x);
            let r = eval(&r, x);
            assert_eq!(a, b * c + r);
        }
    }

    #[derive(Debug, Clone, Copy, PartialEq)]
    struct MinPlus(u64);
    impl Add for MinPlus {
        type Output = Self;

        fn add(self, rhs: Self) -> Self {
            MinPlus(self.0.min(rhs.0))
        }
    }
    impl AddAssign for MinPlus {
        fn add_assign(&mut self, rhs: Self) {
            *self = *self + rhs;
        }
    }
    impl Sum<MinPlus> for MinPlus {
        fn sum<I: Iterator<Item = MinPlus>>(iter: I) -> Self {
            iter.fold(MinPlus(std::u64::MAX), |a, b| a + b)
        }
    }
    impl Mul for MinPlus {
        type Output = Self;

        fn mul(self, rhs: Self) -> Self {
            MinPlus(self.0.saturating_add(rhs.0))
        }
    }
    impl MulAssign for MinPlus {
        fn mul_assign(&mut self, rhs: Self) {
            *self = *self * rhs;
        }
    }
    impl Product<MinPlus> for MinPlus {
        fn product<I: Iterator<Item = MinPlus>>(iter: I) -> Self {
            iter.fold(MinPlus(0), |a, b| a * b)
        }
    }

    #[test]
    fn test_add_min_plus() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let n = rng.gen_range(0..10);
            let a = (0..n)
                .map(|_| MinPlus(rng.gen_range(0..100)))
                .collect::<Vec<_>>();
            let b = (0..n)
                .map(|_| MinPlus(rng.gen_range(0..100)))
                .collect::<Vec<_>>();
            let c = add(&a, &b);
            assert_eq!(c.len(), a.len().max(b.len()));
            for i in 0..c.len() {
                assert_eq!(c[i].0, a[i].0.min(b[i].0),);
            }
        }
    }

    #[test]
    fn test_mul_min_plus() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let n = rng.gen_range(0..10);
            let m = rng.gen_range(0..10);
            let a = (0..n)
                .map(|_| MinPlus(rng.gen_range(0..100)))
                .collect::<Vec<_>>();
            let b = (0..m)
                .map(|_| MinPlus(rng.gen_range(0..100)))
                .collect::<Vec<_>>();
            let c = mul(&a, &b);
            if a.is_empty() || b.is_empty() {
                assert_eq!(c.len(), 0);
            } else {
                assert_eq!(c.len(), a.len() + b.len() - 1);
            }
            for k in 0..c.len() {
                let mut x = std::u64::MAX;
                for i in k.saturating_sub(b.len() - 1)..=k.min(a.len() - 1) {
                    x = x.min(a[i].0 + b[k - i].0);
                }
                assert_eq!(c[k].0, x);
            }
        }
    }

    #[test]
    fn test_pow_min_plus() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..1000 {
            let n = rng.gen_range(0..10);
            let a = (0..n)
                .map(|_| MinPlus(rng.gen_range(0..100)))
                .collect::<Vec<_>>();
            let e = rng.gen_range(0..10);
            let b = pow(a.clone(), e);
            if a.is_empty() {
                vec![MinPlus(0)];
            } else {
                let mut c = vec![MinPlus(u64::MAX); (a.len() - 1) * e as usize + 1];
                c[0] = MinPlus(0);
                for _ in 0..e {
                    let mut swp = vec![MinPlus(u64::MAX); c.len()];
                    for i in 0..=c.len() - a.len() {
                        for j in 0..a.len() {
                            swp[i + j].0 = swp[i + j].0.min(c[i].0.saturating_add(a[j].0));
                        }
                    }
                    c = swp;
                }
                assert_eq!(b, c);
            }
        }
    }
}
