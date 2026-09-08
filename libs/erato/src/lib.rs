//! エラトステネスの篩により、素数判定・素数列挙・素因数分解を行う。
//!
//! 篩は $2$ から順に合成数を篩い落とすことで素数を求める。本クレートは 2 種類の篩を提供する。
//! [`Sieve`] は篩全体を bool 配列として持つ素朴な実装で、素因数分解は試し割りで行う。
//! [`LpdSieve`] は各数について最小素因数（least prime divisor）を記録する実装で、
//! テーブル引きにより素因数分解を高速化できるが、構築コストと必要な篩の長さが大きくなる。
//!
//! # 仕様
//!
//! 長さ $n$ の篩を構築すると、$2 \le i \le n$ を満たす各 $i$ の素数性・最小素因数を判定できる。
//!
//! - [`Sieve::is_prime`] / [`LpdSieve::is_prime`]: $i$ が素数かどうかを判定
//! - [`Sieve::prime_numbers`] / [`LpdSieve::prime_numbers`]: 素数を昇順に列挙するイテレータ
//! - [`Sieve::prime_factors`] は試し割り（$\sqrt{i} + 1$ までの篩が必要）、
//!   [`LpdSieve::prime_factors`] はテーブル引き（$i + 1$ までの篩が必要）で、
//!   $i$ を素因数の昇順の列に分解する
//!
//! いずれの篩も必要な長さを超えたクエリを受けると自動的に伸長される。
//!
//! # 例
//!
//! ```
//! use erato::LpdSieve;
//! use erato::Sieve;
//!
//! // 素数判定
//! let mut sieve = Sieve::new();
//! assert!(sieve.is_prime(2));
//! assert!(!sieve.is_prime(20));
//!
//! // 素数列挙
//! let mut prime_numbers = sieve.prime_numbers();
//! assert_eq!(prime_numbers.next(), Some(2));
//! assert_eq!(prime_numbers.next(), Some(3));
//!
//! // 素因数分解（試し割り）
//! itertools::assert_equal(sieve.prime_factors(84), vec![2, 2, 3, 7]);
//!
//! // 素因数分解（テーブル引き）
//! let mut lpd_sieve = LpdSieve::new();
//! itertools::assert_equal(lpd_sieve.prime_factors(84), vec![2, 2, 3, 7]);
//! ```
//!
//! [`PrimeFactors`] を使うと、素因数列を重複除去したり連長圧縮したりできる。
//!
//! # 計算量
//!
//! - [`Sieve`] 構築: $\Theta(n \log \log n)$、素因数分解: $\Theta(\pi(\sqrt{n}))$
//! - [`LpdSieve`] 構築: $O(n \log n)$、素因数分解: $O(\omega(n))$（重複込みの素因数の個数）

mod converters;
mod int;
mod lpd_sieve;
mod sieve;
mod sieve_base;
mod sieve_kind;

pub use converters::PrimeFactors;
pub use converters::Rle;
pub use converters::Unique;
pub use int::Int;
pub use lpd_sieve::LpdSieve;
pub use sieve::Sieve;
pub use sieve_base::PrimeFactorsByLookup;
pub use sieve_base::PrimeFactorsByTrialDivision;
pub use sieve_base::PrimeNumbers;
use sieve_base::SieveBase;
