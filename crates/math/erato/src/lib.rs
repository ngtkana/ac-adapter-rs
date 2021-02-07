//! Use the two types of sieve of eratosthenes to query.
//!
//! # Difference between [`Sieve`] and [`SieveUsize`]
//!
//! [`Sieve`] is an ordinary sieve of eratosthenes, which is constructed in O ( n lg lg n ) time,
//! while [`SieveUsize`] is a table of "least prime divisors'.
//!
//! Least prime divisors will accelerate prime factorization, but it takes O ( n lg n ) time to
//! construct it. Furthermore, it requires a sieve to constructed to the length n + 1, while the
//! trial division algorithm requires a sieve to constructed to the length √n + 1.
//!
//!
//! # Common usage
//!
//! It can be used to check if an integer is a prime number.
//!
//! ```
//! use erato::{Sieve, SieveUsize};
//!
//! let mut sieve = Sieve::new();
//! assert!(sieve.is_prime(2));
//! assert!(!sieve.is_prime(20));
//!
//! let mut sieve = SieveUsize::new();
//! assert!(sieve.is_prime(2));
//! assert!(!sieve.is_prime(20));
//! ```
//!
//!
//! And it can enumerate all the prime numbers.
//!
//! ```
//! use erato::{Sieve, SieveUsize};
//!
//! let mut sieve = Sieve::new();
//! let mut prime_numbers = sieve.prime_numbers();
//! assert_eq!(prime_numbers.next(), Some(2));
//! assert_eq!(prime_numbers.next(), Some(3));
//!
//! let mut sieve = SieveUsize::new();
//! let mut prime_numbers = sieve.prime_numbers();
//! assert_eq!(prime_numbers.next(), Some(2));
//! assert_eq!(prime_numbers.next(), Some(3));
//! ```
//!
//!
//! # Prime factorization
//!
//! `Sieve` provides a trial-division algorithm,
//!
//! ```
//! use erato::Sieve;
//!
//! let mut sieve = Sieve::new();
//! itertools::assert_equal(sieve.prime_factors_by_trial_division(84), vec![2, 2, 3, 7]);
//! ```
//!
//! while `SieveUsize` provides a table-lookup algorithm.
//!
//! ```
//! use erato::SieveUsize;
//!
//! let mut sieve = SieveUsize::new();
//! itertools::assert_equal(sieve.prime_factors_by_lookup(84), vec![2, 2, 3, 7]);
//! ```

mod int;
mod sieve;
mod sieve_base;
mod sieve_kind;
mod sieve_usize;

pub use {
    int::Int,
    sieve::Sieve,
    sieve_base::{PrimeFactorsByLookup, PrimeFactorsByTrialDivision, PrimeNumbers},
    sieve_usize::SieveUsize,
};

use sieve_base::SieveBase;
