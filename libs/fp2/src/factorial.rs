use super::Fp;

/// Precomputes the factorials and their inverses.
/// # Examples
/// ```
/// use fp2::Factorial;
/// use fp2::Fp;
/// const P: u64 = 998244353;
/// let fact = Factorial::<P>::new(10);
/// assert_eq!(fact.fact(0).value(), 1);
/// assert_eq!(fact.fact(1).value(), 1);
/// assert_eq!(fact.fact(2).value(), 2);
/// assert_eq!(fact.fact(3).value(), 6);
/// ```
pub struct Factorial<const P: u64> {
    fact: Vec<Fp<P>>,
    inv: Vec<Fp<P>>,
}
impl<const P: u64> Factorial<P> {
    /// Constructs a new instance.
    /// # Examples
    /// ```
    /// use fp2::Factorial;
    /// use fp2::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// ```
    pub fn new(length: usize) -> Self {
        let mut fact = vec![Fp::<P>::new(1); length + 1];
        let mut inv = vec![Fp::<P>::new(1); length + 1];
        for i in 1..=length {
            fact[i] = fact[i - 1] * Fp::<P>::new(i as u64);
        }
        inv[length] = fact[length].inv();
        for i in (1..=length).rev() {
            inv[i - 1] = inv[i] * Fp::<P>::new(i as u64);
        }
        Self { fact, inv }
    }

    /// The factorial $n!$
    /// # Requirements
    /// - $n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp2::Factorial;
    /// use fp2::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.fact(0).value(), 1);
    /// assert_eq!(fact.fact(1).value(), 1);
    /// assert_eq!(fact.fact(2).value(), 2);
    /// assert_eq!(fact.fact(3).value(), 6);
    /// ```
    pub fn fact(&self, n: usize) -> Fp<P> { self.fact[n] }

    /// The inverse of the factorial $n!$
    /// # Requirements
    /// - $n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp2::Factorial;
    /// use fp2::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.inv(0).value(), 1);
    /// assert_eq!(fact.inv(1).value(), 1);
    /// assert_eq!(fact.inv(2).value(), 499122177);
    /// assert_eq!(fact.inv(3).value(), 166374059);
    /// ```
    pub fn inv(&self, n: usize) -> Fp<P> { self.inv[n] }

    /// The permutation $P(n, k)$
    /// # Requirements
    /// - $k \le n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp2::Factorial;
    /// use fp2::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.perm(8, 3).value(), 336);
    /// ```
    pub fn perm(&self, n: usize, k: usize) -> Fp<P> { self.fact[n] * self.inv[n - k] }

    /// The binominal coefficient $n \choose k$
    /// # Requirements
    /// - $k \le n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp2::Factorial;
    /// use fp2::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.comb(8, 3).value(), 56);
    /// ```
    pub fn comb(&self, n: usize, k: usize) -> Fp<P> { self.fact[n] * self.inv[n - k] * self.inv[k] }

    /// The binominal coefficient $n \choose k$, but zero if $k < 0$ or $k > n$
    /// # Requirements
    /// - $n \le \text{length}$
    /// # Examples
    /// ```
    /// use fp2::Factorial;
    /// use fp2::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.comb_or_zero(8, 3).value(), 56);
    /// assert_eq!(fact.comb_or_zero(8, 9).value(), 0);
    /// ```
    pub fn comb_or_zero(&self, n: usize, k: isize) -> Fp<P> {
        if k < 0 || k as usize > n {
            Fp::<P>::new(0)
        } else {
            self.comb(n, k as usize)
        }
    }

    /// The number of $k$-multicombinations of $n$ objects
    /// # Requirements
    /// - $k \gt 0$ or $n \gt 0$
    /// # Examples
    /// ```
    /// use fp2::Factorial;
    /// use fp2::Fp;
    /// const P: u64 = 998244353;
    /// let fact = Factorial::<P>::new(10);
    /// assert_eq!(fact.comb_with_reputation(8, 3).value(), 120);
    /// ```
    pub fn comb_with_reputation(&self, n: usize, k: usize) -> Fp<P> {
        assert!(n > 0 || k > 0);
        self.comb(n + k - 1, k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const P: u64 = 998244353;

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
        assert_eq!(fact.inv(0).value(), 1);
        assert_eq!(fact.inv(1).value(), 1);
        assert_eq!(fact.inv(2).value(), 499122177);
        assert_eq!(fact.inv(3).value(), 166374059);
    }

    #[test]
    fn test_perm() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.perm(0, 0).value(), 1);
        assert_eq!(fact.perm(1, 0).value(), 1);
        assert_eq!(fact.perm(1, 1).value(), 1);
        assert_eq!(fact.perm(2, 0).value(), 1);
        assert_eq!(fact.perm(2, 1).value(), 2);
        assert_eq!(fact.perm(2, 2).value(), 2);
        assert_eq!(fact.perm(3, 0).value(), 1);
        assert_eq!(fact.perm(3, 1).value(), 3);
        assert_eq!(fact.perm(3, 2).value(), 6);
        assert_eq!(fact.perm(3, 3).value(), 6);
    }

    #[test]
    fn test_comb() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.comb(0, 0).value(), 1);
        assert_eq!(fact.comb(1, 0).value(), 1);
        assert_eq!(fact.comb(1, 1).value(), 1);
        assert_eq!(fact.comb(2, 0).value(), 1);
        assert_eq!(fact.comb(2, 1).value(), 2);
        assert_eq!(fact.comb(2, 2).value(), 1);
        assert_eq!(fact.comb(3, 0).value(), 1);
        assert_eq!(fact.comb(3, 1).value(), 3);
        assert_eq!(fact.comb(3, 2).value(), 3);
        assert_eq!(fact.comb(3, 3).value(), 1);
    }

    #[test]
    fn test_comb_or_zero() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.comb_or_zero(0, -1).value(), 0);
        assert_eq!(fact.comb_or_zero(0, 0).value(), 1);
        assert_eq!(fact.comb_or_zero(0, 1).value(), 0);
        assert_eq!(fact.comb_or_zero(1, -1).value(), 0);
        assert_eq!(fact.comb_or_zero(1, 0).value(), 1);
        assert_eq!(fact.comb_or_zero(1, 1).value(), 1);
        assert_eq!(fact.comb_or_zero(1, 2).value(), 0);
        assert_eq!(fact.comb_or_zero(2, -1).value(), 0);
        assert_eq!(fact.comb_or_zero(2, 0).value(), 1);
        assert_eq!(fact.comb_or_zero(2, 1).value(), 2);
        assert_eq!(fact.comb_or_zero(2, 2).value(), 1);
        assert_eq!(fact.comb_or_zero(2, 3).value(), 0);
        assert_eq!(fact.comb_or_zero(3, -1).value(), 0);
        assert_eq!(fact.comb_or_zero(3, 0).value(), 1);
        assert_eq!(fact.comb_or_zero(3, 1).value(), 3);
        assert_eq!(fact.comb_or_zero(3, 2).value(), 3);
        assert_eq!(fact.comb_or_zero(3, 3).value(), 1);
        assert_eq!(fact.comb_or_zero(3, 4).value(), 0);
    }

    #[test]
    fn test_comb_with_reputation() {
        let fact = Factorial::<P>::new(10);
        assert_eq!(fact.comb_with_reputation(1, 0).value(), 1);
        assert_eq!(fact.comb_with_reputation(1, 1).value(), 1);
        assert_eq!(fact.comb_with_reputation(2, 0).value(), 1);
        assert_eq!(fact.comb_with_reputation(2, 1).value(), 2);
        assert_eq!(fact.comb_with_reputation(2, 2).value(), 3);
        assert_eq!(fact.comb_with_reputation(3, 0).value(), 1);
        assert_eq!(fact.comb_with_reputation(3, 1).value(), 3);
        assert_eq!(fact.comb_with_reputation(3, 2).value(), 6);
        assert_eq!(fact.comb_with_reputation(3, 3).value(), 10);
    }
}
