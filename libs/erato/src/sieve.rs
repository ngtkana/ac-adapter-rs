use super::sieve_base::PrimeFactorsByTrialDivision;
use super::sieve_base::PrimeNumbers;
use super::sieve_kind;
use super::Int;
use super::SieveBase;

/// 素数判定テーブル。
///
/// # 計算量
///
/// 篩は必要に応じて暗黙に伸長されるため、その分の追加時間がかかる。
///
/// - 構築: $\Theta(n / \log \log n)$
/// - 素因数分解: $\Theta(\pi(\sqrt{n}))$（$\pi(n)$ は $n$ 未満の素数の個数）
#[derive(Default, Debug, Clone, PartialEq)]
pub struct Sieve {
    base: SieveBase<sieve_kind::Boolean>,
}

impl Sieve {
    /// 空の篩を構築する。この呼び出し自体ではヒープ確保を行わない。
    ///
    /// # 例
    ///
    /// ```
    /// use erato::Sieve;
    ///
    /// let sieve = Sieve::new();
    /// assert_eq!(sieve.len(), 0);
    /// ```
    pub fn new() -> Self {
        Self {
            base: SieveBase::new(),
        }
    }

    /// 篩が空のとき `true` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use erato::Sieve;
    /// assert!(Sieve::with_len(0).is_empty());
    /// assert!(!Sieve::with_len(1).is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// 篩の長さを返す。
    ///
    /// # 例
    ///
    /// ```
    /// use erato::Sieve;
    /// let sieve = Sieve::with_len(42);
    /// assert_eq!(sieve.len(), 42);
    /// ```
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// 指定した長さの篩を構築する。
    ///
    /// # 計算量
    ///
    /// $\Theta(n / \log \log n)$
    ///
    /// # 例
    ///
    /// ```
    /// use erato::Sieve;
    ///
    /// let sieve = Sieve::with_len(10);
    /// assert_eq!(sieve.len(), 10);
    /// ```
    pub fn with_len(n: usize) -> Self {
        Self {
            base: SieveBase::with_len(n),
        }
    }

    /// `x` が素数のとき `true` を返す。
    ///
    /// `self.len() <= x` のとき、篩は `x` を超える最小の 2 冪まで自動的に伸長される。
    ///
    /// # Panics
    ///
    /// `x <= 0` のとき panic する。
    ///
    /// # 例
    ///
    /// ```
    /// use erato::Sieve;
    ///
    /// let mut sieve = Sieve::new();
    /// assert!(sieve.is_prime(2));
    /// assert!(!sieve.is_prime(6));
    /// ```
    pub fn is_prime<T: Int>(&mut self, x: T) -> bool {
        self.base.is_prime(x)
    }

    /// 素数を昇順に列挙するイテレータを返す。必要に応じて篩を繰り返し伸長する。
    ///
    /// # 計算量
    ///
    /// 伸長分を除き $\Theta(\pi(n))$（$\pi(n)$ は $n$ 未満の素数の個数）
    ///
    /// # 例
    ///
    /// ```
    /// use erato::Sieve;
    ///
    /// let mut sieve = Sieve::new();
    /// let mut prime_numbers = sieve.prime_numbers();
    /// assert_eq!(prime_numbers.next(), Some(2));
    /// assert_eq!(prime_numbers.next(), Some(3));
    /// assert_eq!(prime_numbers.next(), Some(5));
    /// assert_eq!(prime_numbers.next(), Some(7));
    /// ```
    pub fn prime_numbers<T: Int>(&mut self) -> PrimeNumbers<'_, sieve_kind::Boolean, T> {
        self.base.prime_numbers()
    }

    /// 試し割り法により、`x` の素因数を昇順に列挙するイテレータを返す。必要に応じて篩を繰り返し伸長する。
    ///
    /// # 計算量
    ///
    /// 伸長分を除き $\Theta(\pi(\sqrt{n}))$（$\pi(n)$ は $n$ 未満の素数の個数）
    ///
    /// # 例
    ///
    /// ```
    /// use erato::Sieve;
    ///
    /// let mut sieve = Sieve::new();
    /// itertools::assert_equal(sieve.prime_factors(84), vec![2, 2, 3, 7]);
    /// ```
    pub fn prime_factors<T: Int>(&mut self, n: T) -> PrimeFactorsByTrialDivision<'_, T> {
        self.base.prime_factors_by_trial_division(n)
    }
}

#[cfg(test)]
mod tests {
    use super::Sieve;
    use test_case::test_case;

    #[test]
    fn test_is_prime_via_new() {
        let mut sieve = Sieve::new();
        assert!(sieve.is_prime(2));
        assert!(sieve.is_prime(3));
        assert!(!sieve.is_prime(9));
        assert!(!sieve.is_prime(12));
        assert!(!sieve.is_prime(18));
        assert!(sieve.is_prime(7));
        assert!(sieve.is_prime(307));
        assert!(!sieve.is_prime(102));
    }

    #[test]
    fn test_is_prime_via_with_capacity() {
        let mut sieve = Sieve::with_len(10);
        assert!(sieve.is_prime(2));
        assert!(sieve.is_prime(3));
        assert!(!sieve.is_prime(9));
        assert!(!sieve.is_prime(12));
        assert!(!sieve.is_prime(18));
        assert!(sieve.is_prime(7));
        assert!(sieve.is_prime(307));
        assert!(!sieve.is_prime(102));
    }

    #[test_case(0 => Vec::<i32>::new())]
    #[test_case(1 => vec![2])]
    #[test_case(2 => vec![2, 3])]
    #[test_case(5 => vec![2, 3, 5, 7, 11])]
    fn test_prime_numbers(len: usize) -> Vec<i32> {
        let mut sieve = Sieve::new();
        sieve.prime_numbers().take(len).collect()
    }

    #[test_case(1 => Vec::<i32>::new())]
    #[test_case(2 => vec![2])]
    #[test_case(15 => vec![3, 5])]
    #[test_case(84 => vec![2, 2, 3, 7])]
    fn test_prime_divisors(n: i32) -> Vec<i32> {
        let mut sieve = Sieve::new();
        sieve.prime_factors(n).collect()
    }

    #[test_case(1 => Vec::<i32>::new())]
    #[test_case(2 => vec![2])]
    #[test_case(15 => vec![3, 5])]
    #[test_case(84 => vec![2, 3, 7])]
    #[test_case(648 => vec![2, 3])]
    fn test_prime_divisors_unique(n: i32) -> Vec<i32> {
        let mut sieve = Sieve::new();
        sieve.prime_factors(n).unique().collect()
    }

    #[test_case(1 => Vec::<(i32, usize)>::new())]
    #[test_case(2 => vec![(2, 1)])]
    #[test_case(15 => vec![(3, 1), (5, 1)])]
    #[test_case(84 => vec![(2, 2), (3, 1), (7, 1)])]
    #[test_case(648 => vec![(2, 3), (3, 4)])]
    fn test_prime_divisors_rle(n: i32) -> Vec<(i32, usize)> {
        let mut sieve = Sieve::new();
        sieve.prime_factors(n).rle().collect()
    }
}
