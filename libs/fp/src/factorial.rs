use super::Fp;
use std::ops::Index;

/// Precomputes the factorials and their inverses.
/// # Examples
/// ```
/// use fp::Factorial;
/// use fp::Fp;
/// const P: u64 = 998244353;
/// let fact = Factorial::<P>::new(10);
/// assert_eq!(fact.fact(0).value(), 1);
/// assert_eq!(fact.fact(1).value(), 1);
/// assert_eq!(fact.fact(2).value(), 2);
/// assert_eq!(fact.fact(3).value(), 6);
/// ```
pub struct Factorial<const P: u64> {
    fact: Vec<Fp<P>>,
    inv_fact: Vec<Fp<P>>,
}
impl<const P: u64> Factorial<P> {
    /// Constructs a new instance.
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// ```
    pub fn new(length: usize) -> Self {
        let mut fact = vec![Fp::<P>::new(1); length + 1];
        let mut inv_fact = vec![Fp::<P>::new(1); length + 1];
        for i in 1..=length {
            fact[i] = fact[i - 1] * Fp::<P>::new(i as u64);
        }
        inv_fact[length] = fact[length].inv();
        for i in (1..=length).rev() {
            inv_fact[i - 1] = inv_fact[i] * Fp::<P>::new(i as u64);
        }
        Self { fact, inv_fact }
    }

    /// The factorial $n!$
    /// [`Index`] is implemented for this method.
    /// # Requirements
    /// - $n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.fact(0).value(), 1);
    /// assert_eq!(fact.fact(1).value(), 1);
    /// assert_eq!(fact.fact(2).value(), 2);
    /// assert_eq!(fact.fact(3).value(), 6);
    /// ```
    pub fn fact(&self, n: usize) -> Fp<P> {
        self.fact[n]
    }

    /// The inverse of the factorial $n!$
    /// # Requirements
    /// - $n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.inv_fact(0).value(), 1);
    /// assert_eq!(fact.inv_fact(1).value(), 1);
    /// assert_eq!(fact.inv_fact(2).value(), 499122177);
    /// assert_eq!(fact.inv_fact(3).value(), 166374059);
    /// ```
    pub fn inv_fact(&self, n: usize) -> Fp<P> {
        self.inv_fact[n]
    }

    /// $[x^{n-k}]D^k x^n$.
    /// # Requirements
    /// - $n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.falling(8, 3).value(), 336);
    /// ```
    pub fn falling(&self, n: usize, k: usize) -> Fp<P> {
        if n < k {
            Fp::new(0)
        } else {
            self.fact[n] * self.inv_fact[n - k]
        }
    }

    /// $[x^k](1 + x)^n$.
    /// # Requirements
    /// - $k \le n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.binom(8, 3).value(), 56);
    /// ```
    pub fn binom(&self, n: usize, k: usize) -> Fp<P> {
        assert!(n < self.fact.len());
        if k > n {
            Fp::new(0)
        } else {
            self.fact[n] * self.inv_fact[n - k] * self.inv_fact[k]
        }
    }

    /// $[x^{a_1} \cdot x^{a_l}](x_{a_1} + \cdot x_{a_l})^n$.
    /// # Requirements
    /// - $k \le n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.multinom(&[3, 5]).value(), 56);
    /// ```
    pub fn multinom(&self, a: &[usize]) -> Fp<P> {
        let n = a.iter().sum::<usize>();
        assert!(n < self.fact.len());
        self.fact[n] * a.iter().map(|&x| self.inv_fact[x]).product::<Fp<P>>()
    }

    /// $[x^k](1 + x)^n$.
    /// # Requirements
    /// - $n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.binom_signed(8, 3).value(), 56);
    /// assert_eq!(fact.binom_signed(8, 9).value(), 0);
    /// ```
    pub fn binom_signed(&self, n: usize, k: isize) -> Fp<P> {
        assert!(n < self.fact.len());
        if k < 0 {
            return Fp::new(0);
        }
        let k = k as usize;
        if n < k {
            Fp::new(0)
        } else {
            self.fact[n] * self.inv_fact[n - k] * self.inv_fact[k]
        }
    }

    /// $[x^k](1 - x)^{-n}$.
    /// # Requirements
    /// - $k \gt 0$ or $n \gt 0$
    /// # Examples
    /// ```
    /// use fp::Factorial;
    /// use fp::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.multiset_number(8, 3).value(), 120);
    /// ```
    pub fn multiset_number(&self, n: usize, k: usize) -> Fp<P> {
        if (n, k) == (0, 0) {
            Fp::new(1)
        } else {
            self.binom(n + k - 1, k)
        }
    }
}
impl<const P: u64> Index<usize> for Factorial<P> {
    type Output = Fp<P>;

    fn index(&self, index: usize) -> &Self::Output {
        &self.fact[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: u64 = 998_244_353;

    #[test]
    fn test_factorial() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.fact(0).value(), 1);
        assert_eq!(fact.fact(1).value(), 1);
        assert_eq!(fact.fact(2).value(), 2);
        assert_eq!(fact.fact(3).value(), 6);
    }

    #[test]
    fn test_factorial_inv() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.inv_fact(0).value(), 1);
        assert_eq!(fact.inv_fact(1).value(), 1);
        assert_eq!(fact.inv_fact(2).value(), 499_122_177);
        assert_eq!(fact.inv_fact(3).value(), 166_374_059);
    }

    #[test]
    fn test_falling() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.falling(0, 0).value(), 1);
        assert_eq!(fact.falling(1, 0).value(), 1);
        assert_eq!(fact.falling(1, 1).value(), 1);
        assert_eq!(fact.falling(2, 0).value(), 1);
        assert_eq!(fact.falling(2, 1).value(), 2);
        assert_eq!(fact.falling(2, 2).value(), 2);
        assert_eq!(fact.falling(3, 0).value(), 1);
        assert_eq!(fact.falling(3, 1).value(), 3);
        assert_eq!(fact.falling(3, 2).value(), 6);
        assert_eq!(fact.falling(3, 3).value(), 6);
    }

    #[test]
    fn test_comb() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.binom(0, 0).value(), 1);
        assert_eq!(fact.binom(1, 0).value(), 1);
        assert_eq!(fact.binom(1, 1).value(), 1);
        assert_eq!(fact.binom(2, 0).value(), 1);
        assert_eq!(fact.binom(2, 1).value(), 2);
        assert_eq!(fact.binom(2, 2).value(), 1);
        assert_eq!(fact.binom(3, 0).value(), 1);
        assert_eq!(fact.binom(3, 1).value(), 3);
        assert_eq!(fact.binom(3, 2).value(), 3);
        assert_eq!(fact.binom(3, 3).value(), 1);
    }

    #[test]
    fn test_comb_or_zero() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.binom_signed(0, -1).value(), 0);
        assert_eq!(fact.binom_signed(0, 0).value(), 1);
        assert_eq!(fact.binom_signed(0, 1).value(), 0);
        assert_eq!(fact.binom_signed(1, -1).value(), 0);
        assert_eq!(fact.binom_signed(1, 0).value(), 1);
        assert_eq!(fact.binom_signed(1, 1).value(), 1);
        assert_eq!(fact.binom_signed(1, 2).value(), 0);
        assert_eq!(fact.binom_signed(2, -1).value(), 0);
        assert_eq!(fact.binom_signed(2, 0).value(), 1);
        assert_eq!(fact.binom_signed(2, 1).value(), 2);
        assert_eq!(fact.binom_signed(2, 2).value(), 1);
        assert_eq!(fact.binom_signed(2, 3).value(), 0);
        assert_eq!(fact.binom_signed(3, -1).value(), 0);
        assert_eq!(fact.binom_signed(3, 0).value(), 1);
        assert_eq!(fact.binom_signed(3, 1).value(), 3);
        assert_eq!(fact.binom_signed(3, 2).value(), 3);
        assert_eq!(fact.binom_signed(3, 3).value(), 1);
        assert_eq!(fact.binom_signed(3, 4).value(), 0);
    }

    #[test]
    fn test_comb_with_reputation() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.multiset_number(0, 0).value(), 1);
        assert_eq!(fact.multiset_number(1, 0).value(), 1);
        assert_eq!(fact.multiset_number(1, 1).value(), 1);
        assert_eq!(fact.multiset_number(2, 0).value(), 1);
        assert_eq!(fact.multiset_number(2, 1).value(), 2);
        assert_eq!(fact.multiset_number(2, 2).value(), 3);
        assert_eq!(fact.multiset_number(3, 0).value(), 1);
        assert_eq!(fact.multiset_number(3, 1).value(), 3);
        assert_eq!(fact.multiset_number(3, 2).value(), 6);
        assert_eq!(fact.multiset_number(3, 3).value(), 10);
    }
}
