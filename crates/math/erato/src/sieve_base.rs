use {
    super::{
        sieve_kind::{self, SieveKind},
        Int, PrimeFactors, Rle, Unique,
    },
    std::marker::PhantomData,
};

/// Use a sieve of eratosthenes to query if an integer is prime.
#[derive(Debug, Clone, PartialEq)]
pub struct SieveBase<S: SieveKind> {
    sieve: Vec<S::SieveValue>,
    list: Vec<usize>,
}

impl<S: SieveKind> SieveBase<S> {
    pub fn new() -> Self {
        Self {
            sieve: S::new(),
            list: Vec::new(),
        }
    }
    pub fn len(&self) -> usize {
        self.sieve.len()
    }
    pub fn with_len(n: usize) -> Self {
        let sieve = S::construct(n);
        let list = sieve
            .iter()
            .enumerate()
            .filter(|&(index, &b)| S::is_prime(index, b))
            .map(|(index, _)| index)
            .collect();
        Self { sieve, list }
    }
    pub fn is_prime<T: Int>(&mut self, x: T) -> bool {
        assert!(T::zero() <= x);
        let x = x.as_usize();
        if self.sieve.len() <= x {
            *self = Self::with_len(x + 1);
        }
        S::is_prime(x, self.sieve[x.as_usize()])
    }
    pub fn prime_numbers<T: Int>(&mut self) -> PrimeNumbers<S, T> {
        PrimeNumbers {
            sieve: self,
            index: 0,
            _marker: PhantomData,
        }
    }
    fn extend(&mut self, len: usize) {
        assert!(2 * self.len() <= len);
        *self = Self::with_len(len);
    }
}

impl SieveBase<sieve_kind::Boolean> {
    pub fn prime_factors_by_trial_division<T: Int>(
        &mut self,
        n: T,
    ) -> PrimeFactorsByTrialDivision<T> {
        assert!(T::zero() < n);
        let mut prime_numbers = self.prime_numbers();
        PrimeFactorsByTrialDivision {
            p: prime_numbers.next().unwrap(),
            prime_numbers,
            n,
        }
    }
}

/// An iterator to generate all the prime numbers, constructed by [`crate::Sieve::prime_numbers`].
pub struct PrimeNumbers<'a, S: SieveKind, T: Int> {
    sieve: &'a mut SieveBase<S>,
    index: usize,
    _marker: PhantomData<T>,
}

/// See the document of [`crate::Sieve::prime_factors`]
pub struct PrimeFactorsByTrialDivision<'a, T: Int> {
    prime_numbers: PrimeNumbers<'a, sieve_kind::Boolean, T>,
    p: T,
    n: T,
}
impl<'a, S: SieveKind, T: Int> Iterator for PrimeNumbers<'a, S, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let Self { sieve, index, .. } = self;
        let p = if let Some(&p) = sieve.list.get(*index) {
            T::from_usize(p)
        } else {
            sieve.extend((sieve.len() * 2).max(3));
            T::from_usize(sieve.list[*index])
        };
        *index += 1;
        Some(p)
    }
}
impl<T: Int> PrimeFactorsByTrialDivision<'_, T> {
    pub fn unique(self) -> Unique<T, Self> {
        PrimeFactors::unique(self)
    }
    pub fn rle(self) -> Rle<T, Self> {
        PrimeFactors::rle(self)
    }
}
impl<'a, T: Int> Iterator for PrimeFactorsByTrialDivision<'a, T> {
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
                if *n <= *p * *p {
                    *p = *n;
                    break;
                }
                *p = prime_numbers.next().unwrap();
            }
            *n /= *p;
            Some(*p)
        }
    }
}

/// See the document of [`crate::LpdSieve::prime_factors`]
pub struct PrimeFactorsByLookup<'a, T: Int> {
    sieve: &'a mut SieveBase<sieve_kind::Usize>,
    n: T,
}
impl SieveBase<sieve_kind::Usize> {
    pub fn prime_factors_by_lookup<T: Int>(&mut self, n: T) -> PrimeFactorsByLookup<T> {
        assert!(T::zero() < n);
        PrimeFactorsByLookup { sieve: self, n }
    }
    pub fn lpd<T: Int>(&mut self, n: T) -> T {
        let n = n.as_usize();
        if self.sieve.len() <= n {
            self.extend(2 * (n + 1));
        }
        T::from_usize(self.sieve[n])
    }
}
impl<T: Int> PrimeFactorsByLookup<'_, T> {
    /// Forward [`crate::PrimeFactors::unique`].
    pub fn unique(self) -> Unique<T, Self> {
        PrimeFactors::unique(self)
    }
    /// Forward [`crate::PrimeFactors::rle`].
    pub fn rle(self) -> Rle<T, Self> {
        PrimeFactors::rle(self)
    }
}
impl<'a, T: Int> Iterator for PrimeFactorsByLookup<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        let Self { sieve, n } = self;
        if *n == T::one() {
            None
        } else {
            let p = sieve.lpd(*n);
            *n /= p;
            Some(p)
        }
    }
}
