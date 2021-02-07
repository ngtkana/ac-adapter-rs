use super::{sieve_kind, Int, SieveBase, SieveKind};

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
pub struct PrimeFactorsByTrialDivision<'a, T: Int> {
    prime_numbers: PrimeNumbers<'a, sieve_kind::Boolean, T>,
    p: T,
    n: T,
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
                *p = prime_numbers.next().unwrap();
            }
            *n /= *p;
            Some(*p)
        }
    }
}
