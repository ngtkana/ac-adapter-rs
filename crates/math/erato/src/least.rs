use super::{construct_least_table, Int};

/// Use a sieve of eratosthenes to query if an integer is prime.
#[derive(Debug, Clone, PartialEq)]
pub struct Least {
    least: Vec<usize>,
}

impl Least {
    /// Construct a new empty sieve. No heap allocations is run via this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::Least;
    /// let _ = Least::new();
    /// ```
    pub fn new() -> Self {
        Self { least: Vec::new() }
    }

    /// Construct a new empty sieve.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::Least;
    /// let _ = Least::with_capacity(10);
    /// ```
    pub fn with_capacity(n: usize) -> Self {
        Self {
            least: construct_least_table(n.next_power_of_two()),
        }
    }

    /// Returns a least prime divisor of `x`.
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
    /// use erato::Least;
    ///
    /// let mut sieve = Least::new();
    /// assert_eq!(sieve.least(2), 2);
    /// assert_eq!(sieve.least(6), 2);
    /// assert_eq!(sieve.least(105), 3);
    /// ```
    pub fn least<T: Int>(&mut self, x: T) -> T {
        assert!(T::one() <= x);
        let x = x.as_usize();
        if self.least.len() <= x {
            *self = Self::with_capacity(x + 1);
        }
        T::from_usize(self.least[x.as_usize()])
    }

    /// Returns an iterator generating all the prime factors in non-decreasing order.
    ///
    /// # Algorithm
    ///
    /// Repeatedly consult the sieve for the least prime divisor of the current integer.
    ///
    ///
    /// # Complexity
    ///
    /// If the sieve is sufficiently constructed, it takes time linear to the number of prime divisors
    /// with multiple divisor counted repeatedly. Otherwise, it takes another O ( n ) to construct a sieve.
    ///
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
    /// use erato::Least;
    ///
    /// let mut sieve = Least::new();
    /// itertools::assert_equal(sieve.factorize(84), vec![2, 2, 3, 7]);
    /// ```
    pub fn factorize<'a, T: Int>(&'a mut self, n: T) -> Factorize<'a, T> {
        Factorize { sieve: self, n }
    }
}

/// [See the document of `Least::factorize`](Least::factorize)
pub struct Factorize<'a, T> {
    sieve: &'a mut Least,
    n: T,
}
impl<'a, T: Int> Iterator for Factorize<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let Self { sieve, n } = self;
        if *n == T::one() {
            None
        } else {
            let p = sieve.least(*n);
            *n /= p;
            Some(p)
        }
    }
}

#[cfg(test)]
mod tests {
    use {super::Least, test_case::test_case};

    #[test]
    fn test_is_prime_via_new() {
        let mut sieve = Least::new();
        assert_eq!(sieve.least(2), 2);
        assert_eq!(sieve.least(3), 3);
        assert_eq!(sieve.least(9), 3);
        assert_eq!(sieve.least(12), 2);
        assert_eq!(sieve.least(18), 2);
        assert_eq!(sieve.least(7), 7);
        assert_eq!(sieve.least(307), 307);
        assert_eq!(sieve.least(301), 7);
    }

    #[test]
    fn test_is_prime_via_with_capacity() {
        let mut sieve = Least::with_capacity(10);
        assert_eq!(sieve.least(2), 2);
        assert_eq!(sieve.least(3), 3);
        assert_eq!(sieve.least(9), 3);
        assert_eq!(sieve.least(12), 2);
        assert_eq!(sieve.least(18), 2);
        assert_eq!(sieve.least(7), 7);
        assert_eq!(sieve.least(307), 307);
        assert_eq!(sieve.least(301), 7);
    }

    #[test_case(1 => Vec::<i32>::new())]
    #[test_case(2 => vec![2])]
    #[test_case(3 => vec![3])]
    #[test_case(4 => vec![2, 2])]
    #[test_case(12 => vec![2, 2, 3])]
    #[test_case(60 => vec![2, 2, 3, 5])]
    #[test_case(121 => vec![11, 11])]
    fn test_factorize(n: i32) -> Vec<i32> {
        Least::new().factorize(n).collect::<Vec<_>>()
    }
}
