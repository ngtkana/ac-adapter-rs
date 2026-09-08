//! 有限体 $\mathbb{F}_P$ 上の階乗・逆元・逆階乗テーブルを事前計算し、二項係数を $O(1)$ で求める。
//!
//! 階乗テーブルは $\mathrm{fact}_i = \mathrm{fact}_{i-1} \times i$ の漸化式で構築する。
//! 逆元テーブルは $P \bmod i$ を利用した線形篩で、拡張ユークリッド互除法を使わずに構築する。
//! 逆階乗テーブルは、逆元テーブルがあれば $\mathrm{finv}_i = \mathrm{finv}_{i-1} \times \mathrm{inv}_i$ で、
//! なければ階乗テーブルの末尾のみ拡張ユークリッドで逆元を求め、そこから逆順に
//! $\mathrm{finv}_i = \mathrm{finv}_{i+1} \times (i+1)$ で埋める。いずれも $O(n)$ で、
//! 構築後は階乗・逆元・逆階乗の参照と二項係数の計算がすべて $O(1)$ になる。
//!
//! テーブルの構築有無は型パラメータ `Fact`, `Finv`, `Inv`（[`On`] / [`Off`]）で追跡し、
//! 未構築のテーブルへのアクセスをコンパイル時に禁止する。
//!
//! # 仕様
//!
//! - 型: `Precalc<const P: u64, Fact = Off, Finv = Off, Inv = Off>`（容量 `len`、`P` は素数）
//! - 構築（ビルダーパターン、任意の順で呼び出し可）
//!   - [`build_fact`](Precalc::build_fact): 階乗 $n!$
//!   - [`build_inv`](Precalc::build_inv): 逆元 $n^{-1}$
//!   - [`build_finv_using_inv`](Precalc::build_finv_using_inv): 逆元テーブルから逆階乗 $(n!)^{-1}$
//!   - [`build_finv_using_fact`](Precalc::build_finv_using_fact): 階乗テーブルから逆階乗 $(n!)^{-1}$
//! - クエリ（対応するテーブルが構築済みのときのみ型で呼び出し可能）
//!   - [`fact`](Precalc::fact), [`finv`](Precalc::finv), [`inv`](Precalc::inv), [`binom`](Precalc::binom)
//!
//! # 例
//!
//! ```
//! use fp::fp_new;
//! use fp_precalc::Precalc;
//! const P: u64 = 1009;
//! let pc = Precalc::<P>::new(100).build_fact().build_finv_using_fact();
//! assert_eq!(pc.binom(5, 2), fp_new::<P>(10)); // C(5,2) = 10
//! ```
//!
//! # 計算量
//!
//! - `build_fact`, `build_inv`, `build_finv_using_inv`, `build_finv_using_fact`: $O(n)$
//! - `fact`, `finv`, `inv`, `binom`: $O(1)$

use fp::Fp;
use fp::fpu;

/// テーブル構築の有無を型レベルで表現するトレイト。
///
/// [`On`] を渡すと `Option<T> = T`、[`Off`] を渡すと `Option<T> = ()` になる。
pub trait Switch {
    /// 構築済みなら `T`、未構築なら `()`。
    type Option<T>;
}

/// テーブルが構築済みであることを表す型。[`Switch::Option`] は `T` そのもの。
pub enum On {}

/// テーブルが未構築であることを表す型。[`Switch::Option`] は `()`。
pub enum Off {}

impl Switch for On {
    type Option<T> = T;
}
impl Switch for Off {
    type Option<T> = ();
}

/// 階乗・逆元・逆階乗のテーブル。テーブルごとの構築有無を型パラメータで追跡する。
///
/// `Fact`, `Finv`, `Inv` はそれぞれ対応するテーブルが構築済みなら [`On`]、
/// 未構築なら [`Off`]。構築済みのテーブルに対応するクエリメソッドのみ呼び出せる。
///
/// # 例
///
/// ```
/// use fp_precalc::Precalc;
/// const P: u64 = 1009;
/// let pc = Precalc::<P>::new(6).build_fact();
/// assert_eq!(pc.fact(5).to_string(), "120");
/// ```
pub struct Precalc<const P: u64, Fact: Switch = Off, Finv: Switch = Off, Inv: Switch = Off> {
    len: usize,
    fact: Fact::Option<Vec<Fp<P>>>,
    finv: Finv::Option<Vec<Fp<P>>>,
    inv: Inv::Option<Vec<Fp<P>>>,
}

impl<const P: u64> Precalc<P, Off, Off, Off> {
    /// 容量 `len` で初期化する。テーブルはまだ構築されていない。
    ///
    /// # 例
    ///
    /// ```
    /// use fp_precalc::Precalc;
    /// const P: u64 = 1009;
    /// let pc = Precalc::<P>::new(10);
    /// assert_eq!(pc.len(), 10);
    /// ```
    pub fn new(len: usize) -> Self {
        Precalc {
            len,
            fact: (),
            finv: (),
            inv: (),
        }
    }

    /// 容量 `len` を返す。
    pub fn len(&self) -> usize {
        self.len
    }

    /// 容量が 0 なら `true` を返す。
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

// ==========================================
// Build
// ==========================================

/// 階乗テーブルを構築する。
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, Off, Finv, Inv> {
    /// 階乗テーブル $\mathrm{fact}_i = i!$ を構築する。
    ///
    /// $\mathrm{fact}_i = \mathrm{fact}_{i-1} \times i$ の漸化式で計算する。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact();
    /// assert_eq!(precalc.fact(0), fp_new::<P>(1)); // 0! = 1
    /// assert_eq!(precalc.fact(5), fp_new::<P>(120)); // 5! = 120
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(n)$
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

/// 逆元テーブルを構築する。
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, Off> {
    /// 逆元テーブル $\mathrm{inv}_i = i^{-1} \bmod P$ を構築する。
    ///
    /// $q = \lfloor P / i \rfloor$、$r = P - iq$ とおくと $iq \equiv -r \pmod P$ より
    /// $i^{-1} \equiv -q \cdot r^{-1} \pmod P$ が成り立つ。$r < i$ なので既に求めた
    /// $\mathrm{inv}_r$ を使い漸化式で計算でき、拡張ユークリッド互除法を使わず求まる。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(10).build_inv();
    /// let inv_2 = precalc.inv(2);
    /// assert_eq!(inv_2 * fp_new::<P>(2), fp_new::<P>(1)); // 2^{-1} * 2 = 1 mod P
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(n)$
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

/// 逆元テーブルを使い逆階乗テーブルを構築する。
impl<const P: u64, Fact: Switch> Precalc<P, Fact, Off, On> {
    /// 逆元テーブルから逆階乗テーブル $\mathrm{finv}_i = (i!)^{-1}$ を構築する。
    ///
    /// $\mathrm{finv}_i = \mathrm{finv}_{i-1} \times \mathrm{inv}_i$ の漸化式で計算する。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6)
    ///     .build_fact()
    ///     .build_inv()
    ///     .build_finv_using_inv();
    /// let fact_5 = precalc.fact(5);
    /// let finv_5 = precalc.finv(5);
    /// assert_eq!(fact_5 * finv_5, fp_new::<P>(1)); // fact[5] * finv[5] = 1
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(n)$
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

/// 階乗テーブルを使い逆階乗テーブルを構築する。
impl<const P: u64, Inv: Switch> Precalc<P, On, Off, Inv> {
    /// 階乗テーブルから逆階乗テーブル $\mathrm{finv}_i = (i!)^{-1}$ を構築する。
    ///
    /// 末尾 $\mathrm{finv}_{n-1} = (\mathrm{fact}_{n-1})^{-1}$ のみ拡張ユークリッド互除法
    /// （$O(\log P)$）で求め、そこから $\mathrm{finv}_i = \mathrm{finv}_{i+1} \times (i+1)$
    /// の漸化式で逆順に埋める。逆元テーブルを構築しない分、
    /// [`build_finv_using_inv`](Self::build_finv_using_inv) よりメモリ効率が良い。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact().build_finv_using_fact();
    /// let fact_5 = precalc.fact(5);
    /// let finv_5 = precalc.finv(5);
    /// assert_eq!(fact_5 * finv_5, fp_new::<P>(1)); // fact[5] * finv[5] = 1
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(n)$
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

/// 階乗テーブルをクエリする。
impl<const P: u64, Finv: Switch, Inv: Switch> Precalc<P, On, Finv, Inv> {
    /// $n!$ を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact();
    /// assert_eq!(precalc.fact(5).to_string(), "120");
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(1)$
    ///
    /// # Panics
    ///
    /// `n >= len` のとき panic する。
    pub fn fact(&self, n: usize) -> Fp<P> {
        self.fact[n]
    }
}

/// 逆階乗テーブルをクエリする。
impl<const P: u64, Fact: Switch, Inv: Switch> Precalc<P, Fact, On, Inv> {
    /// $(n!)^{-1}$ を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact().build_finv_using_fact();
    /// assert_eq!(precalc.finv(5) * precalc.fact(5), fp_new::<P>(1));
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(1)$
    ///
    /// # Panics
    ///
    /// `n >= len` のとき panic する。
    pub fn finv(&self, n: usize) -> Fp<P> {
        self.finv[n]
    }
}

/// 逆元テーブルをクエリする。
impl<const P: u64, Fact: Switch, Finv: Switch> Precalc<P, Fact, Finv, On> {
    /// $n^{-1}$ を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use fp::fp_new;
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(10).build_inv();
    /// assert_eq!(precalc.inv(2) * fp_new::<P>(2), fp_new::<P>(1));
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(1)$
    ///
    /// # Panics
    ///
    /// `n >= len` のとき panic する。
    pub fn inv(&self, n: usize) -> Fp<P> {
        self.inv[n]
    }
}

/// 二項係数をクエリする。
impl<const P: u64, Inv: Switch> Precalc<P, On, On, Inv> {
    /// 二項係数 $\binom{n}{k} = \dfrac{n!}{k! (n-k)!}$ を返す。
    ///
    /// $\mathrm{fact}_n \times \mathrm{finv}_k \times \mathrm{finv}_{n-k}$ で計算する。
    ///
    /// # 例
    ///
    /// ```
    /// use fp_precalc::Precalc;
    ///
    /// const P: u64 = 1009;
    /// let precalc = Precalc::<P>::new(6).build_fact().build_finv_using_fact();
    /// assert_eq!(precalc.binom(5, 2).to_string(), "10"); // C(5,2) = 10
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(1)$
    ///
    /// # Panics
    ///
    /// `n >= len`、`k >= len`、`k > n` のいずれかのとき panic する。
    pub fn binom(&self, n: usize, k: usize) -> Fp<P> {
        assert!(n < self.len, "n={n} out of bounds for len={}", self.len);
        assert!(k < self.len, "k={k} out of bounds for len={}", self.len);
        assert!(k <= n, "k={k} must be <= n={n}");
        self.fact[n] * self.finv[k] * self.finv[n - k]
    }
}
