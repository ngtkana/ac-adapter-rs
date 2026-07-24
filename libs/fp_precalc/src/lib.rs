//! Precomputed factorial and modular inverse tables for $𝔽_P$.
//!
//! This crate provides a compile-time configurable struct to precompute and cache
//! factorials, inverse factorials, and modular inverses in $𝔽_P$ (a prime field).
//! Use this when you need to compute many binomial coefficients or factorial-based
//! values without recalculating them repeatedly.
//!
//! # When to Use
//!
//! - Computing multiple binomial coefficients $\binom{n}{k}$ efficiently
//! - Permutation and combination calculations in modular arithmetic
//! - Algorithms where factorial values appear frequently (e.g., combinatorics)
//!
//! # Build Pattern
//!
//! Use method chaining to build only the tables you need:
//!
//! ```
//! use fp_precalc::Precalc;
//! use fp::fp;
//!
//! const P: u64 = 1009;
//! let precalc = Precalc::<P>::new(100)
//!     .build_fact()
//!     .build_finv_using_fact();
//!
//! let binom_5_2 = precalc.binom(5, 2);
//! assert_eq!(binom_5_2, fp::<P>(10));  // C(5,2) = 10
//! ```
//!
//! # Main Items
//!
//! - [`Precalc`]: The main struct for storing precomputed tables
//! - [`Switch`], [`On`], [`Off`]: Type-level booleans for compile-time configuration
//!
//! # Complexity
//!
//! - `build_fact`: $O(n)$ time, $O(n)$ space
//! - `build_inv`: $O(n)$ time, $O(n)$ space
//! - `build_finv_using_fact`: $O(n)$ time, $O(n)$ space
//! - `build_finv_using_inv`: $O(n)$ time, $O(n)$ space
//! - `binom`: $O(1)$ time (after precomputation)

use fp::{Fp, fpu};

/// Type-level boolean trait for configuring which tables are present.
///
/// Implementations (`On` and `Off`) use `type Option<T>` to represent
/// whether a table is stored (`T` when On, `()` when Off), enabling
/// compile-time selection of which precomputed tables to include.
///
/// # Examples
///
/// ```text
/// Switch is used internally via On/Off enums
/// to control whether fields are present in Precalc
/// ```
pub trait Switch {
    type Option<T>;
}

/// Marks a table as present in `Precalc`.
///
/// When used as a type parameter, indicates the corresponding table
/// is stored and accessible via query methods.
///
/// # Examples
///
/// ```text
/// Used as: Precalc<P, On, Off, Off>
/// meaning: fact table is present, finv and inv are not
/// ```
pub enum On {}

/// Marks a table as absent in `Precalc`.
///
/// When used as a type parameter, indicates the corresponding table
/// is not stored (represented internally as `()`).
///
/// # Examples
///
/// ```text
/// Used as: Precalc<P, Off, Off, Off>
/// meaning: no tables are present (initial state)
/// ```
pub enum Off {}

impl Switch for On {
    type Option<T> = T;
}
impl Switch for Off {
    type Option<T> = ();
}

/// Precomputed tables of factorials, inverse factorials, and modular inverses for $𝔽_P$.
///
/// This struct uses type-level booleans to track which tables are available.
/// Build tables selectively using the builder methods, then query them in $O(1)$ time.
///
/// The three optional tables are:
/// - `fact`: Factorials $n!$ for $n \in [0, \text{len})$
/// - `finv`: Inverse factorials $(n!)^{-1}$ for $n \in [0, \text{len})$
/// - `inv`: Modular inverses $i^{-1}$ for $i \in [0, \text{len})$
///
/// # Generic Parameters
///
/// - `P`: Prime modulus (const generic)
/// - `Fact`: `On` if fact table is present, `Off` otherwise (defaults to `Off`)
/// - `Finv`: `On` if finv table is present, `Off` otherwise (defaults to `Off`)
/// - `Inv`: `On` if inv table is present, `Off` otherwise (defaults to `Off`)
///
/// # Examples
///
/// ```
/// use fp_precalc::Precalc;
///
/// const P: u64 = 1009;
/// let precalc = Precalc::<P>::new(10);
/// assert_eq!(precalc.len(), 10);
/// ```
pub struct Precalc<const P: u64, Fact: Switch = Off, Finv: Switch = Off, Inv: Switch = Off> {
    len: usize,
    fact: Fact::Option<Vec<Fp<P>>>,
    finv: Finv::Option<Vec<Fp<P>>>,
    inv: Inv::Option<Vec<Fp<P>>>,
}

impl<const P: u64> Precalc<P, Off, Off, Off> {
    /// Creates an empty precomputation context with capacity for `len` elements.
    ///
    /// No tables are built yet; call builder methods to populate them.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(100);
    /// assert_eq!(precalc.len(), 100);
    /// assert!(!precalc.is_empty());
    /// ```
    pub fn new(len: usize) -> Self {
        Precalc {
            len,
            fact: (),
            finv: (),
            inv: (),
        }
    }

    /// Returns the capacity (maximum $n$ for which tables can be queried).
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(50);
    /// assert_eq!(precalc.len(), 50);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the precomputation capacity is zero.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let empty = Precalc::<P>::new(0);
    /// let non_empty = Precalc::<P>::new(10);
    /// assert!(empty.is_empty());
    /// assert!(!non_empty.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

// ==========================================
// Build
// ==========================================

/// Builds the factorial table.
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, Off, Finv, Inv> {
    /// Precomputes factorials: $\text{fact}\[i\] = i! \bmod P$ for $i \in \[0, \text{len})$.
    ///
    /// Time: $O(n)$, Space: $O(n)$
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    /// use fp::fp;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact();
    /// assert_eq!(precalc.fact(0), fp::<P>(1));  // 0! = 1
    /// assert_eq!(precalc.fact(5), fp::<P>(120));  // 5! = 120
    /// ```
    pub fn build_fact(self) -> Precalc<P, On, Finv, Inv> {
        let Precalc { len, finv, inv, .. } = self;
        let mut fact = vec![fpu(1); len];
        if 2 < len {
            for i in 2..len {
                fact[i] = fact[i - 1] * fpu(i);
            }
        }
        Precalc {
            len,
            fact,
            finv,
            inv,
        }
    }
}

/// Builds the modular inverse table.
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, Off> {
    /// Precomputes modular inverses: $\text{inv}\[i\] = i^{-1} \bmod P$ for $i \in \[1, \text{len})$.
    ///
    /// Uses the formula: $i^{-1} \equiv -\lfloor P/i \rfloor \cdot (P \bmod i)^{-1} \pmod{P}$
    ///
    /// Time: $O(n)$, Space: $O(n)$
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    /// use fp::fp;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(10).build_inv();
    /// let inv_2 = precalc.inv(2);
    /// assert_eq!(inv_2 * fp::<P>(2), fp::<P>(1));  // 2^{-1} * 2 = 1 mod P
    /// ```
    pub fn build_inv(self) -> Precalc<P, Fact, Finv, On> {
        let Precalc {
            len, fact, finv, ..
        } = self;
        let mut inv = vec![fpu(1); len];
        if 2 < len {
            for i in 2..len {
                let q = P as usize / i;
                let r = P as usize - i * q;
                inv[i] = inv[r] * -fpu(q);
            }
        }
        Precalc {
            len,
            fact,
            finv,
            inv,
        }
    }
}

/// Builds inverse factorials using the inverse table.
impl<const P: u64, Fact: Switch> Precalc<P, Fact, Off, On> {
    /// Precomputes inverse factorials using precomputed inverses.
    ///
    /// Requires `inv` table to be built. Computes:
    /// $\text{finv}\[i\] = \text{finv}\[i-1\] \cdot i^{-1}$ for $i \in \[2, \text{len})$
    ///
    /// Time: $O(n)$, Space: $O(n)$
    ///
    /// # Panics
    ///
    /// Panics if `inv` table is not built (accessed via `self.inv[i]`).
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    /// use fp::fp;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6)
    ///     .build_fact()
    ///     .build_inv()
    ///     .build_finv_using_inv();
    /// let fact_5 = precalc.fact(5);
    /// let finv_5 = precalc.finv(5);
    /// assert_eq!(fact_5 * finv_5, fp::<P>(1));  // fact[5] * finv[5] = 1
    /// ```
    pub fn build_finv_using_inv(self) -> Precalc<P, Fact, On, On> {
        let Precalc { len, fact, inv, .. } = self;
        let mut finv = vec![fpu(1); len];
        if 2 < len {
            for i in 2..len {
                finv[i] = finv[i - 1] * inv[i];
            }
        }
        Precalc {
            len,
            fact,
            finv,
            inv,
        }
    }
}

/// Builds inverse factorials using the factorial table.
impl<const P: u64, Inv: Switch> Precalc<P, On, Off, Inv> {
    /// Precomputes inverse factorials using precomputed factorials.
    ///
    /// Requires `fact` table to be built. Uses:
    /// $\text{finv}\[\text{len}-1\] = (\text{fact}\[\text{len}-1\])^{-1}$
    /// $\text{finv}\[i\] = \text{finv}\[i+1\] \cdot (i+1)$ for $i \in \[2, \text{len}-2\]$ (reversed)
    ///
    /// Time: $O(n)$, Space: $O(n)$
    ///
    /// # Panics
    ///
    /// Panics if `len` is 0 or if `fact` table is not built.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    /// use fp::fp;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6)
    ///     .build_fact()
    ///     .build_finv_using_fact();
    /// let fact_5 = precalc.fact(5);
    /// let finv_5 = precalc.finv(5);
    /// assert_eq!(fact_5 * finv_5, fp::<P>(1));  // fact[5] * finv[5] = 1
    /// ```
    pub fn build_finv_using_fact(self) -> Precalc<P, On, On, Inv> {
        let Precalc { len, fact, inv, .. } = self;
        let mut finv = vec![fpu(1); len];
        if len > 0 {
            finv[len - 1] = fact[len - 1].inv();
            if 3 < len {
                for i in (2..len - 1).rev() {
                    finv[i] = finv[i + 1] * fpu(i + 1);
                }
            }
        }
        Precalc {
            len,
            fact,
            finv,
            inv,
        }
    }
}

// ==========================================
// Query
// ==========================================

/// Query factorial table.
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, On, Finv, Inv> {
    /// Returns $n! \bmod P$.
    ///
    /// # Panics
    ///
    /// Panics if `n >= len` or if `fact` table was not built.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact();
    /// assert_eq!(precalc.fact(5).to_string(), "120");
    /// ```
    pub fn fact(&self, n: usize) -> Fp<P> {
        self.fact[n]
    }
}

/// Query inverse factorial table.
impl<const P: u64, Fact: Switch, Inv: Switch> Precalc<P, Fact, On, Inv> {
    /// Returns $(n!)^{-1} \bmod P$.
    ///
    /// # Panics
    ///
    /// Panics if `n >= len` or if `finv` table was not built.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6)
    ///     .build_fact()
    ///     .build_finv_using_fact();
    /// let inv_5_fact = precalc.finv(5);
    /// // inv_5_fact * precalc.fact(5) ≡ 1 (mod P)
    /// ```
    pub fn finv(&self, n: usize) -> Fp<P> {
        self.finv[n]
    }
}

/// Query modular inverse table.
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, On> {
    /// Returns $n^{-1} \bmod P$.
    ///
    /// # Panics
    ///
    /// Panics if `n >= len` or if `inv` table was not built.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(10).build_inv();
    /// let inv_2 = precalc.inv(2);
    /// // inv_2 * 2 ≡ 1 (mod P)
    /// ```
    pub fn inv(&self, n: usize) -> Fp<P> {
        self.inv[n]
    }
}

/// Query binomial coefficient.
impl<const P: u64, Inv: Switch> Precalc<P, On, On, Inv> {
    /// Computes $\binom{n}{k} = \frac{n!}{k!(n-k)!} \bmod P$.
    ///
    /// Requires both `fact` and `finv` tables to be built.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - `n >= len` (n out of bounds)
    /// - `k >= len` (k out of bounds)
    /// - `k > n` (binomial coefficient undefined)
    ///
    /// # Examples
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6)
    ///     .build_fact()
    ///     .build_finv_using_fact();
    /// assert_eq!(precalc.binom(5, 2).to_string(), "10");  // C(5,2) = 10
    /// ```
    pub fn binom(&self, n: usize, k: usize) -> Fp<P> {
        assert!(n < self.len, "n={n} out of bounds for len={}", self.len);
        assert!(k < self.len, "k={k} out of bounds for len={}", self.len);
        assert!(k <= n, "k={k} must be <= n={n}");
        self.fact[n] * self.finv[k] * self.finv[n - k]
    }
}
