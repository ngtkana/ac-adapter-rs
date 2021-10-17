use std::{iter::successors, marker::PhantomData};

mod algo;
mod trait_impls;

/// [`Fp`] で剰余を取るための法情報
pub trait Mod {
    /// 法
    const P: u64;
}
/// [`Mod`] を実装した型 `$MOD` ( = `M` in default) と、それを [`Fp`] で包んだ型の
/// エイリアス `$FP` ( = `F` in default ) とを定義します。
///
/// `$MOD` は [`Mod`] 以外のトレイトは何も実装しませんが、
/// そのようなものを型引数とするときも [`Fp`] は [`Copy`] や [`Default`] などの便利なトレイトを実装します。
///
/// # 基本的な使い方
///
/// ```
/// use new_fp::{define_mod, fp};
///
/// define_mod! { type 13 }
/// assert_eq!(F::new(5) * 4, fp!(7));
/// ```
///
/// 展開後イメージ
///
/// ```
/// use new_fp::{Mod, Fp};
///
/// enum M {}
/// impl Mod for M {
///     const P: u64 = 13;
/// }
/// type F = Fp::<M>;
/// ```
///
/// # 型名の指定の仕方
///
/// ```
/// use new_fp::{define_mod, fp};
///
/// define_mod! { type 13, MOOOOOOOD, FPPPPPP }
/// assert_eq!(FPPPPPP::new(5) * 4, fp!(7));
/// ```
///
///
/// # Visibility
///
/// `type` の前に visibility を書くことができて、`$MOD`, `$FP` の可視性になります。
///
/// ```
/// use new_fp::fp;
/// use some_module::F;
/// assert_eq!(F::new(5) * 4, fp!(7));
///
/// mod some_module {
///     use new_fp::define_mod;
///     define_mod! { pub type 13 } // ここに `pub` を書きましょう。
/// }
/// ```
///
/// このように、何も書かないと visibility なしになります。
///
/// ```compile_fail
/// use some_module::F; // shouldn't compile! (invisible)
/// assert_eq!(F::new(5) * 4, fp!(7));
///
/// mod some_module {
///     use new_fp::define_mod;
///     define_mod! { type 13 } // no `pub`!!
/// }
/// ```
///
#[macro_export]
macro_rules! define_mod {
    ($vis:vis type $P:expr, $MOD:ident, $FP:ident) => {
        $vis enum $MOD {}
        impl $crate::Mod for $MOD {
            const P: u64 = $P;
        }
        $vis type $FP = $crate::Fp<$MOD>;
    };
    ($vis:vis type $P:expr) => {
        $crate::define_mod!{ $vis type $P, M, F }
    }
}
define_mod! { pub type 1_000_000_007, M1000000007, F1000000007 }
define_mod! { pub type 998_244_353, M998244353, F998244353 } // 119 * 2 ^ 23 + 1

/// [`Fp`] 型のオブジェクトを構築します。
///
/// # 使い方
///
/// １つ式を入れると、それで [`Fp::from()`] を呼びます。
///
/// ```
/// use new_fp::{fp, define_mod};
/// define_mod! { type 13 }
///
/// // リテラル
/// let a: F = fp!(6);
/// assert_eq!(a.value(), 6);
///
/// // 式
/// assert_eq!(fp!(2 + 3), F::new(5));
///
/// // 変数
/// let x: i16 = -3;
/// assert_eq!(fp!(x), F::new(10));
/// ```
///
/// セミコロン区切りで２つ整数を入れると、順に分子、分母とする分数を構築します。
///
/// ```
/// use new_fp::{fp, define_mod};
/// define_mod! { type 13 }
///
/// assert_eq!(fp!(2; 3), F::new(2) / F::new(3));
/// ```
#[macro_export]
macro_rules! fp {
    ($num:expr; $den:expr) => {
        $crate::Fp::from($num) / $crate::Fp::from($den)
    };
    ($value:expr) => {
        $crate::Fp::from($value)
    };
}

/// 演算のたびに自動で固定素数値 `M::P` で剰余を取る、整数型のラッパーです。
///
pub struct Fp<M> {
    value: u64,
    __marker: PhantomData<M>,
}
impl<M: Mod> Fp<M> {
    /// `M::P` へのショートカットです。
    pub const P: u64 = M::P;
    /// 値 `value` に対応する [`Fp`] のオブジェクトを構築します。
    pub fn new(value: u64) -> Self {
        Self::new_unchecked(value % M::P)
    }
    /// 対応する値を返します。
    pub fn value(self) -> u64 {
        self.value
    }
    /// Mod 逆数を返します。
    ///
    /// # Panics
    ///
    /// `self` が `0` のとき
    ///
    pub fn inv(self) -> Self {
        if self.value == 0 {
            return self;
        }
        Self::new_unchecked(algo::ext_euclid_modinv(self.value, M::P))
    }
    /// 冪を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use new_fp::{fp, define_mod};
    /// define_mod! { type 13 }
    /// ```
    pub fn pow(mut self, mut exp: u64) -> Self {
        if exp == 0 {
            Self::new(1)
        } else {
            let mut acc = Self::new(1);
            while 1 < exp {
                if exp % 2 == 1 {
                    acc *= self;
                }
                exp /= 2;
                self *= self;
            }
            acc * self
        }
    }
    fn new_unchecked(value: u64) -> Self {
        Self {
            value,
            __marker: PhantomData,
        }
    }
}

/// 階乗を順に返すイテレータを生成します。
///
/// # Examples
///
/// ```
/// use new_fp::{fact_iter, define_mod, fp};
/// define_mod! { type 13 }
///
/// let mut fact = fact_iter::<M>();
/// assert_eq!(fact.next(), Some(fp!(1)));
/// assert_eq!(fact.next(), Some(fp!(1)));
/// assert_eq!(fact.next(), Some(fp!(2)));
/// assert_eq!(fact.next(), Some(fp!(6)));
/// assert_eq!(fact.next(), Some(fp!(24)));
/// ```
pub fn fact_iter<M: Mod>() -> impl Iterator<Item = Fp<M>> {
    (1..).scan(Fp::new(1), |state, x| {
        let ans = *state;
        *state *= x;
        Some(ans)
    })
}

/// 階乗とその逆数を前計算します。
///
/// # Examples
///
/// ```
/// use new_fp::{fact_build, define_mod, fp};
/// define_mod! { type 13 }
///
/// let fact = fact_build::<M>(3);
/// assert_eq!(fact.0[0], vec![fp!(1), fp!(1), fp!(2)]);
/// assert_eq!(fact.0[1], vec![fp!(1), fp!(1), fp!(1; 2)]);
/// ```
///
#[allow(clippy::missing_panics_doc)]
pub fn fact_build<M: Mod>(n: usize) -> FactTable<M> {
    FactTable(if n == 0 {
        [Vec::new(), Vec::new()]
    } else {
        let fact = fact_iter::<M>().take(n).collect::<Vec<_>>();
        let mut fact_inv = vec![fact.last().unwrap().inv(); n];
        (1..n).rev().for_each(|i| fact_inv[i - 1] = fact_inv[i] * i);
        [fact, fact_inv]
    })
}

/// [`fact_build`] の戻り値型で、階乗とその逆数のテーブルを管理しています。
///
/// # Examples
///
/// ```
/// use new_fp::{fact_build, define_mod, fp};
/// define_mod! { type 13 }
///
/// let fact = fact_build::<M>(4);
///
/// assert_eq!(fact.0[0], vec![fp!(1), fp!(1), fp!(2), fp!(6)]);
/// assert_eq!(fact.0[1], vec![fp!(1), fp!(1), fp!(1; 2), fp!(1; 6)]);
/// ```
///
///
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct FactTable<M: Mod>(pub [Vec<Fp<M>>; 2]);
impl<M: Mod> FactTable<M> {
    /// k ≤ n < len ならば binom(n, k) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_mod, fp};
    /// define_mod! { type 13 }
    /// let fact = fact_build::<M>(5);
    ///
    /// assert_eq!(fact.binom(4, 0), fp!(1));
    /// assert_eq!(fact.binom(4, 1), fp!(4));
    /// assert_eq!(fact.binom(4, 2), fp!(6));
    /// ```
    pub fn binom(&self, n: usize, k: usize) -> Fp<M> {
        assert!(n < self.0[0].len());
        assert!(k <= n);
        self.0[0][n] * self.0[1][k] * self.0[1][n - k]
    }
    /// i + j < len ならば binom(i + j, i) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_mod, fp};
    /// define_mod! { type 13 }
    /// let fact = fact_build::<M>(5);
    ///
    /// assert_eq!(fact.binom2(0, 4), fp!(1));
    /// assert_eq!(fact.binom2(1, 3), fp!(4));
    /// assert_eq!(fact.binom2(2, 2), fp!(6));
    /// ```
    pub fn binom2(&self, i: usize, j: usize) -> Fp<M> {
        self.binom(i + j, i)
    }
    /// 0 ≤ k ≤ n < len ならば 1 / binom(n, k) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_mod, fp};
    /// define_mod! { type 13 }
    /// let fact = fact_build::<M>(5);
    ///
    /// assert_eq!(fact.binom_inv(4, 0), fp!(1; 1));
    /// assert_eq!(fact.binom_inv(4, 1), fp!(1; 4));
    /// assert_eq!(fact.binom_inv(4, 2), fp!(1; 6));
    /// ```
    pub fn binom_inv(&self, n: u64, k: u64) -> Fp<M> {
        let n = n as usize;
        let k = k as usize;
        assert!(n < self.0[0].len());
        assert!(k <= n);
        self.0[1][n] * self.0[0][k] * self.0[0][n - k]
    }
    /// 0 ≤ n < len ならば binom(n, k) を返します。さもなくばパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use new_fp::{fact_build, define_mod, fp};
    /// define_mod! { type 13 }
    /// let fact = fact_build::<M>(5);
    ///
    /// // `binom` と同じ
    /// assert_eq!(fact.binom_or_zero(4, 0), fp!(1));
    /// assert_eq!(fact.binom_or_zero(4, 1), fp!(4));
    /// assert_eq!(fact.binom_or_zero(4, 2), fp!(6));
    ///
    /// // `k` が範囲外なると `0` を返します。
    /// assert_eq!(fact.binom_or_zero(4, 5), fp!(0));
    /// assert_eq!(fact.binom_or_zero(4, -1), fp!(0));
    /// ```
    pub fn binom_or_zero(&self, n: usize, k: isize) -> Fp<M> {
        assert!(n < self.0[0].len() as usize);
        if (0..=n as isize).contains(&k) {
            self.binom(n, k as usize)
        } else {
            Fp::new(0)
        }
    }
}

/// 二項係数 binom(n, k) を、n ごとにまとめて返すイテレータを生成します。
///
/// # Examples
///
/// ```
/// use new_fp::{binom_iter, define_mod, fp};
/// define_mod! { type 13 }
///
/// let mut binom = binom_iter::<M>();
/// assert_eq!(binom.next(), Some(vec![fp!(1)]));
/// assert_eq!(binom.next(), Some(vec![fp!(1), fp!(1)]));
/// assert_eq!(binom.next(), Some(vec![fp!(1), fp!(2), fp!(1)]));
/// assert_eq!(binom.next(), Some(vec![fp!(1), fp!(3), fp!(3), fp!(1)]));
/// ```
pub fn binom_iter<M: Mod>() -> impl Iterator<Item = Vec<Fp<M>>> {
    successors(Some(vec![Fp::new(1)]), |last| {
        let mut crr = last.clone();
        crr.push(Fp::new(0));
        crr[1..].iter_mut().zip(last).for_each(|(x, &y)| *x += y);
        Some(crr)
    })
}
