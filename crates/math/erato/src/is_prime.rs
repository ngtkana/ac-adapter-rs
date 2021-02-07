use super::Int;

/// Use a sieve of eratosthenes to query if an integer is prime.
pub struct IsPrime {
    is_prime: Vec<bool>,
}

impl IsPrime {
    /// Construct a new empty sieve. No heap allocations is run via this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::IsPrime;
    /// let _ = IsPrime::new();
    /// ```
    pub fn new() -> Self {
        Self {
            is_prime: Vec::new(),
        }
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
            is_prime: construct_table(n.next_power_of_two()),
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
    pub fn is_prime<T: Int>(&mut self, x: T) -> bool {
        assert!(T::zero() <= x);
        let x = x.as_usize();
        if self.is_prime.len() <= x {
            *self = Self::with_capacity(x + 1);
        }
        self.is_prime[x.as_usize()]
    }
}

fn construct_table(n: usize) -> Vec<bool> {
    let mut is_prime = vec![true; n];
    (0..2.min(n)).for_each(|i| is_prime[i] = false);
    for p in (2..).take_while(|&p| p * p < n) {
        if !is_prime[p] {
            continue;
        }
        let mut i = p * p;
        while i < n {
            is_prime[i] = false;
            i += p;
        }
    }
    is_prime
}

#[cfg(test)]
mod tests {
    use {
        super::{construct_table, IsPrime},
        test_case::test_case,
    };

    #[test_case(0 => Vec::<bool>::new())]
    #[test_case(1 => vec![false])]
    #[test_case(2 => vec![false, false])]
    #[test_case(3 => vec![false, false, true])]
    #[test_case(4 => vec![false, false, true, true])]
    #[test_case(5 => vec![false, false, true, true, false])]
    fn test_construct_table(n: usize) -> Vec<bool> {
        construct_table(n)
    }

    #[test]
    fn test_is_prime_via_new() {
        let mut sieve = IsPrime::new();
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
        let mut sieve = IsPrime::with_capacity(10);
        assert!(sieve.is_prime(2));
        assert!(sieve.is_prime(3));
        assert!(!sieve.is_prime(9));
        assert!(!sieve.is_prime(12));
        assert!(!sieve.is_prime(18));
        assert!(sieve.is_prime(7));
        assert!(sieve.is_prime(307));
        assert!(!sieve.is_prime(102));
    }
}
