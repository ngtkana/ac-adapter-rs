//! Prealculation of $x⁻¹$, $x!$, etc.
//!
//! # Examples
//!
//! ```
//! use fp::fp;
//! const P: u64 = 998_244_353;
//!
//! let fact = fp_precalc::Fact::<P>::new(10);
//! assert_eq!(fact[5], fp!(120));
//!
//! let ifact = fp_precalc::IFact::new(&fact);
//! assert_eq!(ifact[5], fp!(120).inv());
//!
//! let binom = fp_precalc::Binom::new(&fact, &ifact);
//! let binom = binom.as_fn();
//! assert_eq!(binom(5, 3), fp!(10));
//! ```

use fp::Fp;
use std::ops::Deref;

/// $x⁻¹$ for small $x$'s
pub struct Inv<const P: u64> {
    values: Vec<Fp<P>>,
}
impl<const P: u64> Inv<P> {
    /// Create a new [`Inv`].
    pub fn new(len: usize) -> Self {
        assert!(len >= 2);
        let mut values = vec![Fp::new(0); len];
        values[1] = Fp::new(1);
        for i in 2..len {
            let q = P as usize / i;
            let r = P as usize - q * i;
            values[i] = -values[r] * Fp::from(q);
        }
        Self { values }
    }
}
impl<const P: u64> Deref for Inv<P> {
    type Target = [Fp<P>];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

/// $x!$ for small $x$'s
pub struct Fact<const P: u64> {
    values: Vec<Fp<P>>,
}
impl<const P: u64> Fact<P> {
    pub fn new(len: usize) -> Self {
        assert!(len >= 1);
        let mut values = vec![Fp::new(1); len];
        for i in 1..len {
            values[i] = values[i - 1] * Fp::new(i as u64);
        }
        Self { values }
    }
}
impl<const P: u64> Deref for Fact<P> {
    type Target = [Fp<P>];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

/// $x!⁻¹$ for small $x$'s
pub struct IFact<const P: u64> {
    values: Vec<Fp<P>>,
}
impl<const P: u64> IFact<P> {
    pub fn new(fact: &Fact<P>) -> Self {
        let mut values = fact.values.clone();
        let last = values.last().unwrap();
        *values.last_mut().unwrap() = last.inv();
        for i in (1..values.len()).rev() {
            values[i - 1] = values[i] * Fp::from(i);
        }
        Self { values }
    }
}
impl<const P: u64> Deref for IFact<P> {
    type Target = [Fp<P>];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

/// $\dbinom{n}{k}$ for small $n$'s and $k$'s
pub struct Binom<'a, const P: u64> {
    fact: &'a Fact<P>,
    ifact: &'a IFact<P>,
}
impl<'a, const P: u64> Binom<'a, P> {
    pub fn new(fact: &'a Fact<P>, ifact: &'a IFact<P>) -> Self {
        Self { fact, ifact }
    }
    pub fn as_fn(&'a self) -> impl Fn(usize, usize) -> Fp<P> + 'a {
        move |n, k| {
            if n < k {
                return Fp::new(0);
            }
            let Self { fact, ifact } = self;
            assert!(n < fact.len());
            fact[n] * ifact[k] * ifact[n - k]
        }
    }
}

/// $x^n$ for small $n$'s
pub struct Pow<const P: u64> {
    values: Vec<Fp<P>>,
}
impl<const P: u64> Pow<P> {
    pub fn new(x: Fp<P>, len: usize) -> Self {
        let mut values = vec![Fp::new(1); len];
        for i in 1..len {
            values[i] = values[i - 1] * x;
        }
        Self { values }
    }
}
impl<const P: u64> Deref for Pow<P> {
    type Target = [Fp<P>];

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: u64 = 13;

    #[test]
    fn test_inv() {
        let inv = Inv::<P>::new(P as usize);
        assert_eq!(inv[0], Fp::new(0));
        for i in 1..P {
            assert_eq!(inv[i as usize] * Fp::from(i), Fp::new(1));
        }
    }

    #[test]
    fn test_fact() {
        let fact = Fact::<P>::new(P as usize);
        assert_eq!(fact[0], Fp::new(1));
        for i in 0..P {
            assert_eq!(fact[i as usize], (1..=i).map(Fp::new).product::<Fp<_>>());
        }
    }

    #[test]
    fn test_ifact() {
        let fact = Fact::<P>::new(P as usize);
        let ifact = IFact::new(&fact);
        assert_eq!(ifact[0], Fp::new(1));
        for i in 0..P {
            assert_eq!(
                ifact[i as usize],
                (1..=i).map(Fp::new).product::<Fp<_>>().inv()
            );
        }
    }

    #[test]
    fn test_binom() {
        let fact = Fact::<P>::new(P as usize);
        let ifact = IFact::new(&fact);
        let binom = Binom::new(&fact, &ifact);
        let binom = binom.as_fn();
        for i in 0..P as usize {
            for j in 0..P as usize {
                assert_eq!(
                    binom(i, j),
                    if i < j { Fp::new(0) } else { fact[i] * ifact[j] * ifact[i - j] }
                );
            }
        }
    }

    #[test]
    fn test_pow() {
        let pow = Pow::<P>::new(Fp::new(2), P as usize);
        for i in 0..P {
            assert_eq!(
                pow[i as usize],
                std::iter::repeat_n(Fp::new(2), i as usize).product::<Fp<_>>(),
            );
        }
    }
}
