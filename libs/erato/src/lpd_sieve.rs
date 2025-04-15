use super::sieve_base::PrimeFactorsByLookup;
use super::sieve_base::PrimeNumbers;
use super::sieve_kind;
use super::Int;
use super::SieveBase;

/// Least-prime-divisor table.
///
/// # Complexity
///
/// The complexity of algorithms are like this, but it takes extra time to grow itself implicitly.
///
/// - Construction: O ( n lg n )
/// - Prime factorization: O ( ω( n ) ), where ω( n ) is the number of prime divisors, with
/// 
/// multiple divisors counted repeatedly.
#[derive(Default, Debug, Clone, PartialEq)]
pub struct LpdSieve {
    base: SieveBase<sieve_kind::Usize>,
}

impl LpdSieve {
    /// Construct a new empty sieve. No heap allocations is run via this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    ///
    /// let sieve = LpdSieve::new();
    /// assert_eq!(sieve.len(), 0);
    /// ```
    pub fn new() -> Self {
        Self {
            base: SieveBase::new(),
        }
    }

    /// Returns `true` if a sieve is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    /// assert!(LpdSieve::with_len(0).is_empty());
    /// assert!(!LpdSieve::with_len(1).is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.base.is_empty()
    }

    /// Returns the length of a sieve.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    /// let sieve = LpdSieve::with_len(42);
    /// assert_eq!(sieve.len(), 42);
    /// ```
    pub fn len(&self) -> usize {
        self.base.len()
    }

    /// Construct a sieve of given length.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    ///
    /// let sieve = LpdSieve::with_len(10);
    /// assert_eq!(sieve.len(), 10);
    /// ```
    pub fn with_len(n: usize) -> Self {
        Self {
            base: SieveBase::with_len(n),
        }
    }

    /// Returns `true` if `x` is a prime number.
    ///
    /// # Panics
    ///
    /// if `x <= 0`.
    ///
    ///
    /// # Note
    ///
    /// If `self.len() <= x` sieve will extended the size to the next power of two of `x`.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    ///
    /// let mut sieve = LpdSieve::new();
    /// assert!(sieve.is_prime(2));
    /// assert!(!sieve.is_prime(6));
    /// ```
    pub fn is_prime<T: Int>(&mut self, x: T) -> bool {
        self.base.is_prime(x)
    }

    /// Returns the least prime divisor of `x`.
    ///
    /// # Panics
    ///
    /// if `x <= 1`.
    ///
    ///
    /// # Note
    ///
    /// If `self.len() <= x` sieve will extended the size to the next power of two of `x`.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    ///
    /// let mut sieve = LpdSieve::new();
    /// assert!(sieve.is_prime(2));
    /// assert!(!sieve.is_prime(6));
    /// ```
    pub fn lpd<T: Int>(&mut self, x: T) -> T {
        self.base.lpd(x)
    }

    /// Returns an iterator to generate all the prime numbers in ascending order, extending
    /// itself repeatedly.
    ///
    ///
    /// # Complexity
    ///
    /// Beside the incremental building, it takes Θ ( π ( n ) ), where π ( n ) is the number of
    /// prime numbers less than n.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    ///
    /// let mut sieve = LpdSieve::new();
    /// let mut prime_numbers = sieve.prime_numbers();
    /// assert_eq!(prime_numbers.next(), Some(2));
    /// assert_eq!(prime_numbers.next(), Some(3));
    /// assert_eq!(prime_numbers.next(), Some(5));
    /// assert_eq!(prime_numbers.next(), Some(7));
    /// ```
    pub fn prime_numbers<T: Int>(&mut self) -> PrimeNumbers<sieve_kind::Usize, T> {
        self.base.prime_numbers()
    }

    /// Use trial-division algorithm to iterate over all the prime divisors of `x`, extending itself repeatedly.
    ///
    /// # Complexity
    ///
    /// Beside the incremental building, it takes Θ ( ω ( n ) ),  where ω ( n ) is the number of prime numbers less than n.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::LpdSieve;
    ///
    /// let mut sieve = LpdSieve::new();
    /// itertools::assert_equal(sieve.prime_factors(84), vec![2, 2, 3, 7]);
    /// ```
    pub fn prime_factors<T: Int>(&mut self, n: T) -> PrimeFactorsByLookup<T> {
        self.base.prime_factors_by_lookup(n)
    }
}

#[cfg(test)]
mod tests {
    use super::LpdSieve;
    use test_case::test_case;

    #[test]
    fn test_is_prime_via_new() {
        let mut sieve = LpdSieve::new();
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
        let mut sieve = LpdSieve::with_len(10);
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
        let mut sieve = LpdSieve::new();
        sieve.prime_numbers().take(len).collect()
    }

    #[test_case(1 => Vec::<i32>::new())]
    #[test_case(2 => vec![2])]
    #[test_case(15 => vec![3, 5])]
    #[test_case(84 => vec![2, 2, 3, 7])]
    fn test_prime_divisors(n: i32) -> Vec<i32> {
        let mut sieve = LpdSieve::new();
        sieve.prime_factors(n).collect()
    }

    #[test_case(1 => Vec::<i32>::new())]
    #[test_case(2 => vec![2])]
    #[test_case(15 => vec![3, 5])]
    #[test_case(84 => vec![2, 3, 7])]
    #[test_case(648 => vec![2, 3])]
    fn test_prime_divisors_unique(n: i32) -> Vec<i32> {
        let mut sieve = LpdSieve::new();
        sieve.prime_factors(n).unique().collect()
    }

    #[test_case(1 => Vec::<(i32, usize)>::new())]
    #[test_case(2 => vec![(2, 1)])]
    #[test_case(15 => vec![(3, 1), (5, 1)])]
    #[test_case(84 => vec![(2, 2), (3, 1), (7, 1)])]
    #[test_case(648 => vec![(2, 3), (3, 4)])]
    fn test_prime_divisors_rle(n: i32) -> Vec<(i32, usize)> {
        let mut sieve = LpdSieve::new();
        sieve.prime_factors(n).rle().collect()
    }
}
