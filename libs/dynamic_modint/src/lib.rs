//! 法を実行時に決定できる mod 整数演算。
//!
//! 法をコンパイル時定数にできない場合に使う。法はスレッドローカルな `Cell` に保持し、
//! [`define_mod!`] マクロが生成するタグ型（[`Mod`] トレイト実装）を介してアクセスする。
//! 法が素数であることは要求しないため、逆元・除算は提供しない。
//!
//! # 仕様
//!
//! - `define_mod! { M: T = value }`: 型 `M`（内部型 `T`）を定義し、法を `value` に初期化
//! - `define_mod! { M: T }` + `M::set(value)`: 定義と初期化を分離
//! - 型: `Mint<M>`（`M: Mod`）
//! - 生成: [`mint::<M>(value)`](mint), [`Mint::new(value)`](Mint::new) — 値を法で還元
//! - 演算: `+`, `-`, `*`, 単項 `-`
//! - `Sum`: $\sum_i a_i$、`Product`: $\prod_i a_i$
//!
//! # 例
//!
//! ```
//! use dynamic_modint::{define_mod, mint, Mod};
//!
//! define_mod! { M: usize = 19 }
//!
//! let x = mint::<M>(12);
//! let y = mint::<M>(13);
//! assert_eq!(x + y, mint::<M>(6)); // (12 + 13) mod 19 = 6
//! ```
//!
//! # 計算量
//!
//! - 加減乗算: $O(1)$

use std::{
    cmp::{Eq, PartialEq},
    fmt::{self, Debug, Display},
    marker::PhantomData,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
};

/// 実行時に法を持つタグ型 `$name` を定義する。
///
/// 法はスレッドローカルな `Cell<$type>` に保持する。`$value` を与えると定義と同時に
/// 法を設定でき、省略すると後から `$name::set(value)` で設定する。
///
/// # 仕様
///
/// - `define_mod! { $name: $type }`: 法未設定（初期値 0）で `$name` を定義
/// - `define_mod! { $name: $type = $value }`: 法を `$value` として `$name` を定義
///
/// # 例
///
/// 定義と初期化を同時に行う。
///
/// ```
/// use dynamic_modint::{define_mod, mint, Mod};
///
/// define_mod! { M: usize = 19 }
///
/// let x = mint::<M>(12);
/// let y = mint::<M>(13);
/// assert_eq!(x + y, mint::<M>(6));
/// ```
///
/// 定義と初期化を分ける。
///
/// ```
/// use dynamic_modint::{define_mod, mint, Mod};
///
/// define_mod! { M: usize }
/// M::set(19);
///
/// let x = mint::<M>(12);
/// let y = mint::<M>(13);
/// assert_eq!(x + y, mint::<M>(6));
/// ```
#[macro_export]
macro_rules! define_mod {
    ($name:ident: $type:ty) => {
        enum $name {}
        impl $name {
            fn with<F, R>(f: F) -> R
            where
                F: FnOnce(&std::cell::Cell<$type>) -> R,
            {
                thread_local! {
                    static STORAGE: std::cell::Cell<$type> = const { std::cell::Cell::new(0) };
                }
                STORAGE.with(f)
            }
        }
        impl $crate::Mod for $name {
            type Value = $type;
            fn get() -> $type {
                Self::with(|cell| cell.get())
            }
            fn set(value: $type) {
                Self::with(|cell| cell.set(value))
            }
        }
    };
    ($name:ident: $type:ty = $value:expr) => {
        $crate::define_mod! { $name: $type }
        $name::set($value);
    };
}

/// 実行時に決まる法を保持するタグ型が実装するトレイト。
///
/// [`define_mod!`] マクロが実装を自動生成するため、直接実装する必要はない。
pub trait Mod {
    /// 法・値の内部表現型。
    type Value: Scalar;

    /// 現在設定されている法を返す。
    fn get() -> Self::Value;

    /// 法を `value` に設定する。
    fn set(value: Self::Value);
}

/// [`Mint`] の内部値として使える符号なし整数型が満たすべき制約。
///
/// `u8`, `u16`, `u32`, `u64`, `u128`, `usize` に実装済み。
pub trait Scalar:
    PartialEq
    + Eq
    + PartialOrd
    + Ord
    + Debug
    + Display
    + Clone
    + Copy
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Rem<Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + RemAssign
{
    /// 加法単位元 $0$。
    const CONST_0: Self;
    /// 乗法単位元 $1$。
    const CONST_1: Self;
}

macro_rules! impl_scalar {
    ($($type:ty),+ $(,)?) => {
        $(
            impl Scalar for $type {
                const CONST_0: Self = 0;
                const CONST_1: Self = 1;
            }
        )+
    };
}
impl_scalar!(u8, u16, u32, u64, u128, usize);

/// 法 `M` を実行時に持つ mod 整数。
///
/// 内部値は常に $[0, M)$ に還元された状態で保持する。四則演算のうち加減乗算と
/// 単項マイナスを実装し、法が素数と限らないため逆元・除算は提供しない。
///
/// # 例
///
/// ```
/// use dynamic_modint::{define_mod, mint, Mod};
///
/// define_mod! { M: u64 = 19 }
/// let x = mint::<M>(12);
/// let y = mint::<M>(13);
/// assert_eq!(x + y, mint::<M>(6)); // (12 + 13) mod 19 = 6
/// ```
pub struct Mint<M: Mod> {
    value: M::Value,
    _marker: PhantomData<M>,
}
impl<M: Mod> Mint<M> {
    /// 内部値 $[0, M)$ をそのまま取り出す。
    pub const fn value(self) -> M::Value {
        self.value
    }
    /// 値を法 $M$ で還元して [`Mint`] を構築する。
    ///
    /// # 例
    ///
    /// ```
    /// use dynamic_modint::{define_mod, Mint, Mod};
    ///
    /// define_mod! { M: u64 = 19 }
    /// assert_eq!(Mint::<M>::new(25).value(), 6); // 25 mod 19 = 6
    /// ```
    pub fn new(value: M::Value) -> Self {
        Self {
            value: value % M::get(),
            _marker: PhantomData,
        }
    }
}

impl<M: Mod> PartialEq for Mint<M> {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl<M: Mod> Eq for Mint<M> {}
impl<M: Mod> Debug for Mint<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
impl<M: Mod> Display for Mint<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.value)
    }
}
impl<M: Mod> Clone for Mint<M> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<M: Mod> Copy for Mint<M> {}

/// [`Mint::new`] のエイリアス。
///
/// # 例
///
/// ```
/// use dynamic_modint::{define_mod, mint, Mod};
///
/// define_mod! { M: u64 = 19 }
/// assert_eq!(mint::<M>(25).value(), 6); // 25 mod 19 = 6
/// ```
pub fn mint<M: Mod>(value: M::Value) -> Mint<M> {
    Mint::new(value)
}

impl<M: Mod> Add for Mint<M> {
    type Output = Self;

    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<M: Mod> AddAssign for Mint<M> {
    fn add_assign(&mut self, rhs: Self) {
        self.value += rhs.value;
        if self.value >= M::get() {
            self.value -= M::get();
        }
    }
}

impl<M: Mod> Sub for Mint<M> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<M: Mod> SubAssign for Mint<M> {
    fn sub_assign(&mut self, rhs: Self) {
        if self.value < rhs.value {
            self.value += M::get();
        }
        self.value -= rhs.value;
    }
}

impl<M: Mod> Mul for Mint<M> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        mint(self.value * rhs.value % M::get())
    }
}

impl<M: Mod> Neg for Mint<M> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self.value == M::Value::CONST_0 {
            mint(M::Value::CONST_0)
        } else {
            mint(M::get() - self.value)
        }
    }
}

impl<M: Mod> std::iter::Sum for Mint<M> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Mint::new(M::Value::CONST_0), Add::add)
    }
}

impl<M: Mod> std::iter::Product for Mint<M> {
    fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Mint::new(M::Value::CONST_1), Mul::mul)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_set_mod_19() {
        define_mod! { M: u64 = 19 }

        let x = mint::<M>(12);
        let y = mint::<M>(13);
        assert_eq!(x + y, mint::<M>(6));
    }
}
