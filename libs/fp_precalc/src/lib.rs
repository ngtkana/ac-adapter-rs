//! 有限体 $𝔽_P$ の階乗・逆階乗・逆元テーブルの事前計算。
//!
//! $\binom{n}{k}$ を $O(1)$ で計算したい場合に使用。
//!
//! # 使用例
//!
//! ```
//! use fp::fp;
//! use fp_precalc::Precalc;
//! const P: u64 = 1009;
//! let pc = Precalc::<P>::new(100).build_fact().build_finv_using_fact();
//! assert_eq!(pc.binom(5, 2), fp::<P>(10)); // C(5,2) = 10
//! ```
//!
//! # API
//!
//! - [`Precalc::build_fact()`]: 階乗 $n!$、計算量 $O(n)$
//! - [`Precalc::build_inv()`]: 逆元 $n^{-1}$、計算量 $O(n)$
//! - [`Precalc::build_finv_using_fact()`]: 逆階乗 $(n!)^{-1}$、計算量 $O(n)$
//! - [`Precalc::binom()`]: 二項係数 $\binom{n}{k}$、計算量 $O(1)$

use fp::Fp;
use fp::fpu;

/// テーブルの有無を型で表現するトレイト。型レベル真偽値。
pub trait Switch {
    type Option<T>;
}

/// テーブルが有る場合の型。
pub enum On {}

/// テーブルが無い場合の型。
pub enum Off {}

impl Switch for On {
    type Option<T> = T;
}
impl Switch for Off {
    type Option<T> = ();
}

/// 階乗・逆階乗・逆元のテーブル。型で有無を追跡。
///
/// ビルダーパターンで選択的に構築。クエリは $O(1)$。
pub struct Precalc<const P: u64, Fact: Switch = Off, Finv: Switch = Off, Inv: Switch = Off> {
    len: usize,
    fact: Fact::Option<Vec<Fp<P>>>,
    finv: Finv::Option<Vec<Fp<P>>>,
    inv: Inv::Option<Vec<Fp<P>>>,
}

impl<const P: u64> Precalc<P, Off, Off, Off> {
    /// 容量 len で初期化。テーブル未構築。
    pub fn new(len: usize) -> Self {
        Precalc {
            len,
            fact: (),
            finv: (),
            inv: (),
        }
    }

    /// 容量を返す。
    pub fn len(&self) -> usize {
        self.len
    }

    /// 容量が 0 なら true。
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

// ==========================================
// Build
// ==========================================

/// 階乗テーブルを構築。
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, Off, Finv, Inv> {
    /// 階乗 $n!$、計算量 $O(n)$。
    ///
    /// 例:
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::fp;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact();
    /// assert_eq!(precalc.fact(0), fp::<P>(1)); // 0! = 1
    /// assert_eq!(precalc.fact(5), fp::<P>(120)); // 5! = 120
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

/// 逆元テーブルを構築。
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, Off> {
    /// 逆元 $i^{-1}$、拡張ユークリッド、$O(n)$。
    ///
    ///
    /// 例:
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::fp;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(10).build_inv();
    /// let inv_2 = precalc.inv(2);
    /// assert_eq!(inv_2 * fp::<P>(2), fp::<P>(1)); // 2^{-1} * 2 = 1 mod P
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

/// 逆元テーブルを使用して逆階乗を構築。
impl<const P: u64, Fact: Switch> Precalc<P, Fact, Off, On> {
    /// 逆元テーブルから逆階乗を構築。
    ///
    ///
    /// 例:
    ///
    /// # Panics
    ///
    /// Panics if `inv` table is not built (accessed via `self.inv[i]`).
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::fp;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6)
    ///     .build_fact()
    ///     .build_inv()
    ///     .build_finv_using_inv();
    /// let fact_5 = precalc.fact(5);
    /// let finv_5 = precalc.finv(5);
    /// assert_eq!(fact_5 * finv_5, fp::<P>(1)); // fact[5] * finv[5] = 1
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

/// 階乗テーブルを使用して逆階乗を構築。
impl<const P: u64, Inv: Switch> Precalc<P, On, Off, Inv> {
    /// 階乗テーブルから逆階乗を構築。
    ///
    ///
    /// 例:
    ///
    /// # Panics
    ///
    /// Panics if `len` is 0 or if `fact` table is not built.
    ///
    /// # Examples
    ///
    /// ```
    /// use fp::fp;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact().build_finv_using_fact();
    /// let fact_5 = precalc.fact(5);
    /// let finv_5 = precalc.finv(5);
    /// assert_eq!(fact_5 * finv_5, fp::<P>(1)); // fact[5] * finv[5] = 1
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

/// 階乗テーブルをクエリ。
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, On, Finv, Inv> {
    /// $n!$ を返す。
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

/// 逆階乗テーブルをクエリ。
impl<const P: u64, Fact: Switch, Inv: Switch> Precalc<P, Fact, On, Inv> {
    /// $(n!)^{-1}$ を返す。
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
    /// let precalc = Precalc::<P>::new(6).build_fact().build_finv_using_fact();
    /// let inv_5_fact = precalc.finv(5);
    /// // inv_5_fact * precalc.fact(5) ≡ 1 (mod P)
    /// ```
    pub fn finv(&self, n: usize) -> Fp<P> {
        self.finv[n]
    }
}

/// 逆元テーブルをクエリ。
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, On> {
    /// $n^{-1}$ を返す。
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

/// 二項係数をクエリ。
impl<const P: u64, Inv: Switch> Precalc<P, On, On, Inv> {
    /// 二項係数 $binom{n}{k}$、計算量 $O(1)$。
    ///
    /// fact と finv テーブルが必要。
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
    /// let precalc = Precalc::<P>::new(6).build_fact().build_finv_using_fact();
    /// assert_eq!(precalc.binom(5, 2).to_string(), "10"); // C(5,2) = 10
    /// ```
    pub fn binom(&self, n: usize, k: usize) -> Fp<P> {
        assert!(n < self.len, "n={n} out of bounds for len={}", self.len);
        assert!(k < self.len, "k={k} out of bounds for len={}", self.len);
        assert!(k <= n, "k={k} must be <= n={n}");
        self.fact[n] * self.finv[k] * self.finv[n - k]
    }
}
