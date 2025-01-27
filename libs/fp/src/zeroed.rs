use super::Fp;
use std::ops::{DivAssign, MulAssign};

/// Represents a $p$-adic leading term $a \cdot p^e$ ($a \in \mathbb{F} _ p, e \in \mathbb{N}$).
#[derive(Debug, Clone, Copy)]
pub struct Zeroed<const P: u64> {
    unit: Fp<P>,
    zero: u64,
}

impl<const P: u64> Zeroed<P> {
    /// Returns $1 \cdot p^0$.
    /// # Examples
    /// ```
    /// use fp::{Zeroed, Fp};
    /// let x = Zeroed::<998244353>::one();
    /// assert_eq!(x.value(), Fp::new(1));
    /// ```
    pub fn one() -> Self {
        Self {
            unit: Fp::new(1),
            zero: 0,
        }
    }
    /// Projects the value $a \cdot p^e$.
    /// # Examples
    /// ```
    /// use fp::{Zeroed, Fp};
    /// const P: u64 = 998244353;
    /// let mut x = Zeroed::<P>::new(2 * P);
    /// assert_eq!(x.value(), Fp::new(0));
    /// x /= P;
    /// assert_eq!(x.value(), Fp::new(2));
    /// ```
    pub fn new(unit: u64) -> Self {
        let mut self_ = Self::one();
        self_ *= unit;
        self_
    }
    /// Returns the value projected to $\mathbb{F} _ P$.
    /// # Examples
    /// ```
    /// use fp::{Zeroed, Fp};
    /// const P: u64 = 998244353;
    /// let x = Zeroed::<P>::new(2 * P);
    /// assert_eq!(x.value(), Fp::new(0));
    /// ```
    pub fn value(&self) -> Fp<P> {
        if self.zero > 0 {
            Fp::new(0)
        } else {
            self.unit
        }
    }
}

impl<const P: u64> MulAssign<u64> for Zeroed<P> {
    fn mul_assign(&mut self, mut rhs: u64) {
        assert_ne!(rhs, 0);
        while rhs % P == 0 {
            rhs /= P;
            self.zero += 1;
        }
        self.unit *= Fp::new(rhs);
    }
}

impl<const P: u64> DivAssign<u64> for Zeroed<P> {
    fn div_assign(&mut self, mut rhs: u64) {
        assert_ne!(rhs, 0);
        while rhs % P == 0 {
            rhs /= P;
            self.zero -= 1;
        }
        self.unit /= Fp::new(rhs);
    }
}
