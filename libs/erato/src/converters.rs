use super::Int;
use super::PrimeFactorsByLookup;
use super::PrimeFactorsByTrialDivision;
use std::iter::Peekable;
use std::marker::PhantomData;

/// An abstraction of prime factor generator.
///
/// It provides a few useful converters.
pub trait PrimeFactors<T: Int>: Sized + Iterator<Item = T> {
    /// Make prime factors unique.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use erato::Sieve;
    ///
    /// let mut sieve = Sieve::new();
    /// itertools::assert_equal(sieve.prime_factors(84).unique(), vec![2, 3, 7]);
    /// ```
    fn unique(self) -> Unique<T, Self> {
        Unique {
            iter: self,
            prev: None,
        }
    }
    /// Returns an iterator to generate the pairs of distinct prime divisors and the multiplicity
    /// of it.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use erato::Sieve;
    ///
    /// let mut sieve = Sieve::new();
    /// itertools::assert_equal(sieve.prime_factors(84).rle(), vec![(2, 2), (3, 1), (7, 1)]);
    /// ```
    fn rle(self) -> Rle<T, Self> {
        Rle {
            iter: self.peekable(),
            _marker: PhantomData,
        }
    }
}
impl<'a, T: Int> PrimeFactors<T> for PrimeFactorsByTrialDivision<'a, T> {}
impl<'a, T: Int> PrimeFactors<T> for PrimeFactorsByLookup<'a, T> {}

/// An iterator returned by [`PrimeFactors::unique`]
pub struct Unique<T: Int, P: PrimeFactors<T>> {
    iter: P,
    prev: Option<T>,
}
impl<T: Int, P: PrimeFactors<T>> Iterator for Unique<T, P> {
    type Item = P::Item;

    fn next(&mut self) -> Option<Self::Item> {
        let prev = self.prev;
        let res = self.iter.find(|&p| Some(p) != prev);
        self.prev = res;
        res
    }
}

/// An iterator returned by [`PrimeFactors::rle`]
pub struct Rle<T: Int, P: PrimeFactors<T>> {
    iter: Peekable<P>,
    _marker: PhantomData<T>,
}
impl<T: Int, P: PrimeFactors<T>> Iterator for Rle<T, P> {
    type Item = (P::Item, usize);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(p) = self.iter.next() {
            let mut multi = 1;
            while self.iter.peek() == Some(&p) {
                multi += 1;
                self.iter.next();
            }
            Some((p, multi))
        } else {
            None
        }
    }
}
