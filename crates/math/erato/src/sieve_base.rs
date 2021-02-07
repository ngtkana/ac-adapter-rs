use {
    super::{
        sieve_kind::{self, SieveKind},
        Int,
    },
    std::marker::PhantomData,
};

pub type Sieve = SieveBase<sieve_kind::Boolean>;
pub type SieveUsize = SieveBase<sieve_kind::Usize>;

/// Use a sieve of eratosthenes to query if an integer is prime.
#[derive(Debug, Clone, PartialEq)]
pub struct SieveBase<S: SieveKind> {
    sieve: Vec<S::SieveValue>,
    list: Vec<usize>,
}

impl<S: SieveKind> SieveBase<S> {
    /// Construct a new empty sieve. No heap allocations is run via this method.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::Sieve;
    /// let _ = Sieve::new();
    /// ```
    pub fn new() -> Self {
        Self {
            sieve: S::new(),
            list: Vec::new(),
        }
    }

    pub fn len(&self) -> usize {
        self.sieve.len()
    }

    pub fn reserve(&mut self, len: usize) {
        if self.len() <= len {
            *self = Self::with_capacity(len);
        }
    }

    /// Construct a new empty sieve.
    ///
    /// # Examples
    ///
    /// ```
    /// use erato::Sieve;
    /// let _ = Sieve::with_capacity(10);
    /// ```
    pub fn with_capacity(n: usize) -> Self {
        let sieve = S::construct(n);
        let list = sieve
            .iter()
            .enumerate()
            .filter(|&(index, &b)| S::is_prime(index, b))
            .map(|(index, _)| index)
            .collect();
        Self { sieve, list }
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
    /// use erato::Sieve;
    ///
    /// let mut sieve = Sieve::new();
    /// assert!(sieve.is_prime(2));
    /// assert!(!sieve.is_prime(6));
    /// ```
    pub fn is_prime<T: Int>(&mut self, x: T) -> bool {
        assert!(T::zero() <= x);
        let x = x.as_usize();
        if self.sieve.len() <= x {
            *self = Self::with_capacity(x + 1);
        }
        S::is_prime(x, self.sieve[x.as_usize()])
    }
}

impl<S: SieveKind> SieveBase<S> {
    pub fn prime_numbers<T: Int>(&mut self) -> PrimeNumbers<S, T> {
        PrimeNumbers {
            sieve: self,
            index: 0,
            _marker: PhantomData,
        }
    }
    pub fn prime_factors<T: Int>(&mut self, n: T) -> FactorizeByTrialDivision<S, T> {
        assert!(T::zero() < n);
        let mut prime_numbers = self.prime_numbers();
        FactorizeByTrialDivision {
            p: prime_numbers.next().unwrap(),
            prime_numbers,
            n,
        }
    }
}

/// [See the document of `SieveBase::prime_numbers`](SieveBase::prime_numbers)
pub struct PrimeNumbers<'a, S: SieveKind, T: Int> {
    sieve: &'a mut SieveBase<S>,
    index: usize,
    _marker: PhantomData<T>,
}
impl<'a, S: SieveKind, T: Int> Iterator for PrimeNumbers<'a, S, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let Self { sieve, index, .. } = self;
        let p = if let Some(&p) = sieve.list.get(*index) {
            T::from_usize(p)
        } else {
            sieve.reserve((sieve.len() * 2).max(3));
            T::from_usize(sieve.list[*index])
        };
        *index += 1;
        Some(p)
    }
}

/// [See the document of `SieveBase::factorize`](SieveBase::factorize)
pub struct FactorizeByTrialDivision<'a, S: SieveKind, T: Int> {
    prime_numbers: PrimeNumbers<'a, S, T>,
    p: T,
    n: T,
}
impl<'a, S: SieveKind, T: Int> Iterator for FactorizeByTrialDivision<'a, S, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            prime_numbers,
            p,
            n,
        } = self;
        if *n == T::one() {
            None
        } else {
            while *n % *p != T::zero() {
                *p = prime_numbers.next().unwrap();
            }
            *n /= *p;
            Some(*p)
        }
    }
}

#[cfg(test)]
mod tests {
    use {super::Sieve, test_case::test_case};

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
        let mut sieve = Sieve::with_capacity(10);
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
}
