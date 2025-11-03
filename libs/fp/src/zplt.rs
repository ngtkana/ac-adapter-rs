use super::Fp;
use std::ops::{DivAssign, MulAssign};

/// A leading term $a⋅p^e ∈ ℤ_p ($a ∈ 𝔽_p, e ∈ ℕ$)
#[derive(Debug, Clone, Copy)]
pub struct ZpLt<const P: u64> {
    unit: Fp<P>,
    zero: u64,
}

impl<const P: u64> ZpLt<P> {
    /// Returns $1 \cdot p^0$.
    /// # Examples
    /// ```
    /// use fp::{ZpLt, Fp};
    /// let x = ZpLt::<998244353>::one();
    /// assert_eq!(x.value(), Fp::new(1));
    /// ```
    pub fn one() -> Self {
        Self {
            unit: Fp::new(1),
            zero: 0,
        }
    }
    /// Returns the value projected to $\mathbb{F} _ P$.
    /// # Examples
    /// ```
    /// use fp::{ZpLt, Fp};
    /// const P: u64 = 998244353;
    /// let x = ZpLt::<P>::new(2 * P);
    /// assert_eq!(x.as_fp(), Fp::new(0));
    /// ```
    pub fn as_fp(&self) -> Fp<P> {
        if self.zero > 0 {
            Fp::new(0)
        } else {
            self.unit
        }
    }
}

impl<const P: u64> From<Fp<P>> for ZpLt<P> {
    fn from(value: Fp<P>) -> Self {
        if value == Fp::new(0) {
            Self {
                unit: Fp::new(1),
                zero: 1,
            }
        } else {
            Self {
                unit: value,
                zero: 0,
            }
        }
    }
}

impl<const P: u64> MulAssign<u64> for ZpLt<P> {
    fn mul_assign(&mut self, mut rhs: u64) {
        assert_ne!(rhs, 0);
        while rhs % P == 0 {
            rhs /= P;
            self.zero += 1;
        }
        self.unit *= Fp::new(rhs);
    }
}

impl<const P: u64> DivAssign<u64> for ZpLt<P> {
    fn div_assign(&mut self, mut rhs: u64) {
        assert_ne!(rhs, 0);
        while rhs % P == 0 {
            rhs /= P;
            self.zero -= 1;
        }
        self.unit /= Fp::new(rhs);
    }
}
