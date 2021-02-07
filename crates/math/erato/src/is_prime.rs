use {super::Int, std::marker::PhantomData};

pub type Sieve = SieveBase<needs_list::No>;
pub type SieveWithList = SieveBase<needs_list::Yes>;

/// Use a sieve of eratosthenes to query if an integer is prime.
#[derive(Debug, Clone, PartialEq)]
pub struct SieveBase<L: NeedsList> {
    sieve: Vec<bool>,
    list: L::PrimeList,
}

impl<L: NeedsList> SieveBase<L> {
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
            sieve: Vec::new(),
            list: L::new(),
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
        let sieve = construct_is_prime_table(n);
        let list = L::construct(&sieve);
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
        self.sieve[x.as_usize()]
    }
}

impl SieveBase<needs_list::Yes> {
    pub fn prime_numbers<T: Int>(&mut self) -> PrimeNumbers<T> {
        PrimeNumbers {
            sieve: self,
            index: 0,
            _marker: PhantomData,
        }
    }
    pub fn prime_factors<T: Int>(&mut self, n: T) -> FactorizeByTrialDivision<T> {
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
pub struct PrimeNumbers<'a, T> {
    sieve: &'a mut SieveBase<needs_list::Yes>,
    index: usize,
    _marker: PhantomData<T>,
}
impl<'a, T: Int> Iterator for PrimeNumbers<'a, T> {
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
pub struct FactorizeByTrialDivision<'a, T> {
    prime_numbers: PrimeNumbers<'a, T>,
    p: T,
    n: T,
}
impl<'a, T: Int> Iterator for FactorizeByTrialDivision<'a, T> {
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

pub trait NeedsList {
    type PrimeList;
    fn new() -> Self::PrimeList;
    fn construct(src: &[bool]) -> Self::PrimeList;
}
pub mod needs_list {
    use super::{extract_prime_numbers_from_is_prime_table, NeedsList};
    #[derive(Debug, Clone, Copy, PartialEq)]
    pub enum Yes {}
    pub enum No {}
    impl NeedsList for Yes {
        type PrimeList = Vec<usize>;
        fn new() -> Self::PrimeList {
            Vec::new()
        }
        fn construct(src: &[bool]) -> Self::PrimeList {
            extract_prime_numbers_from_is_prime_table(src)
        }
    }
    impl NeedsList for No {
        type PrimeList = ();
        fn new() -> Self::PrimeList {}
        fn construct(_src: &[bool]) -> Self::PrimeList {}
    }
}

fn construct_is_prime_table(n: usize) -> Vec<bool> {
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

fn extract_prime_numbers_from_is_prime_table(is_prime: &[bool]) -> Vec<usize> {
    is_prime
        .iter()
        .enumerate()
        .filter(|&(_, &b)| b)
        .map(|(p, _)| p)
        .collect()
}

#[cfg(test)]
mod tests {
    use {
        super::{
            construct_is_prime_table, extract_prime_numbers_from_is_prime_table, Sieve,
            SieveWithList,
        },
        test_case::test_case,
    };

    #[test_case(0 => Vec::<bool>::new())]
    #[test_case(1 => vec![false])]
    #[test_case(2 => vec![false, false])]
    #[test_case(3 => vec![false, false, true])]
    #[test_case(4 => vec![false, false, true, true])]
    #[test_case(5 => vec![false, false, true, true, false])]
    fn test_construct_is_prime_table(n: usize) -> Vec<bool> {
        construct_is_prime_table(n)
    }

    #[test_case(0 => Vec::<usize>::new())]
    #[test_case(1 => Vec::<usize>::new())]
    #[test_case(2 => Vec::<usize>::new())]
    #[test_case(3 => vec![2])]
    #[test_case(4 => vec![2, 3])]
    #[test_case(5 => vec![2, 3])]
    #[test_case(6 => vec![2, 3, 5])]
    #[test_case(16 => vec![2, 3, 5, 7, 11, 13])]
    fn test_extract_prime_numbers_from_is_prime_table(n: usize) -> Vec<usize> {
        extract_prime_numbers_from_is_prime_table(&construct_is_prime_table(n))
    }

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
        let mut sieve = SieveWithList::new();
        sieve.prime_numbers().take(len).collect()
    }

    #[test_case(1 => Vec::<i32>::new())]
    #[test_case(2 => vec![2])]
    #[test_case(15 => vec![3, 5])]
    #[test_case(84 => vec![2, 2, 3, 7])]
    fn test_prime_divisors(n: i32) -> Vec<i32> {
        let mut sieve = SieveWithList::new();
        sieve.prime_factors(n).collect()
    }
}
