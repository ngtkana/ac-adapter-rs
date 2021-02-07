//! Use the two types of sieve of eratosthenes to query.
//!
//! # Difference between [`Sieve`] and [`LpdSieve`]
//!
//! [`Sieve`] is an ordinary sieve of eratosthenes, which is constructed in O ( n lg lg n ) time,
//! while [`LpdSieve`] is a table of "least prime divisors'.
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
//! use erato::{Sieve, LpdSieve};
//!
//! let mut sieve = Sieve::new();
//! assert!(sieve.is_prime(2));
//! assert!(!sieve.is_prime(20));
//!
//! let mut sieve = LpdSieve::new();
//! assert!(sieve.is_prime(2));
//! assert!(!sieve.is_prime(20));
//! ```
//!
//!
//! And it can enumerate all the prime numbers.
//!
//! ```
//! use erato::{Sieve, LpdSieve};
//!
//! let mut sieve = Sieve::new();
//! let mut prime_numbers = sieve.prime_numbers();
//! assert_eq!(prime_numbers.next(), Some(2));
//! assert_eq!(prime_numbers.next(), Some(3));
//!
//! let mut sieve = LpdSieve::new();
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
//! itertools::assert_equal(sieve.prime_factors(84), vec![2, 2, 3, 7]);
//! ```
//!
//! while `LpdSieve` provides a table-lookup algorithm.
//!
//! ```
//! use erato::LpdSieve;
//!
//! let mut sieve = LpdSieve::new();
//! itertools::assert_equal(sieve.prime_factors(84), vec![2, 2, 3, 7]);
//! ```
//!
//! See [`PrimeFactors`] to make unique or run-length encode them.

mod converters;
mod int;
mod lpd_sieve;
mod sieve;
mod sieve_base;
mod sieve_kind;

pub use {
    converters::{PrimeFactors, Rle, Unique},
    int::Int,
    lpd_sieve::LpdSieve,
    sieve::Sieve,
    sieve_base::{PrimeFactorsByLookup, PrimeFactorsByTrialDivision, PrimeNumbers},
};

use sieve_base::SieveBase;
