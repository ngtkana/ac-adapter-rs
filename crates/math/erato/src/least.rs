use super::Int;

/// Use a sieve of eratosthenes to query if an integer is prime.
pub struct Least {
    least: Vec<usize>,
}

impl Least {
    /// Construct a new empty sieve. No heap allocations is run via this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::IsPrime;
    /// let _ = IsPrime::new();
    /// ```
    pub fn new() -> Self {
        Self { least: Vec::new() }
    }

    /// Construct a new empty sieve. No heap allocations is run via this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::IsPrime;
    /// let _ = IsPrime::with_capacity(10);
    /// ```
    pub fn with_capacity(n: usize) -> Self {
        Self {
            least: construct_table(n.next_power_of_two()),
        }
    }

    /// Returns `true` if `x` is a prime number.
    ///
    /// # Panics
    ///
    /// if `x <= 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::IsPrime;
    ///
    /// let mut sieve = IsPrime::new();
    /// assert!(sieve.is_prime(2));
    /// assert!(!sieve.is_prime(6));
    /// ```
    pub fn least<T: Int>(&mut self, x: T) -> T {
        assert!(T::zero() <= x);
        let x = x.as_usize();
        if self.least.len() <= x {
            *self = Self::with_capacity(x + 1);
        }
        T::from_usize(self.least[x.as_usize()])
    }
}

fn construct_table(n: usize) -> Vec<usize> {
    let mut least = vec![std::usize::MAX; n];
    for p in 2..n {
        if least[p] != std::usize::MAX {
            continue;
        }
        least[p] = p;
        let mut i = p * p;
        while i < n {
            if least[i] == std::usize::MAX {
                least[i] = p;
            }
            i += p;
        }
    }
    least
}

#[cfg(test)]
mod tests {
    use {
        super::{construct_table, Least},
        test_case::test_case,
    };

    #[test_case(0 => Vec::<usize>::new())]
    #[test_case(1 => vec![std::usize::MAX])]
    #[test_case(2 => vec![std::usize::MAX, std::usize::MAX])]
    #[test_case(3 => vec![std::usize::MAX, std::usize::MAX, 2])]
    #[test_case(4 => vec![std::usize::MAX, std::usize::MAX, 2, 3])]
    #[test_case(5 => vec![std::usize::MAX, std::usize::MAX, 2, 3, 2])]
    #[test_case(6 => vec![std::usize::MAX, std::usize::MAX, 2, 3, 2, 5])]
    #[test_case(16 => vec![std::usize::MAX, std::usize::MAX, 2, 3, 2, 5, 2, 7, 2, 3, 2, 11, 2, 13, 2, 3])]
    fn test_construct_table(n: usize) -> Vec<usize> {
        construct_table(n)
    }

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
}
