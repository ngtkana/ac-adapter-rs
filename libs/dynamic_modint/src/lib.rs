//! 実行時(遅延初期化) modint
//!
//! 法が素数であることは仮定しません。実行時 mod はそういう使い方が多いですからね。
//!
//! # 実装されているもの
//!
//! * 足し算: $a + b$
//! * 引き算: $a - b$
//! * Negation: $-a$
//! * 掛け算: $a * b$
//! * 総和: $\sum_i a_i$
//! * 総積: $\prod_i a_i$
//!
//! # Examples
//!
//! ```
//! use std::cell::Cell;
//! use dynamic_modint::{define_mod, Mod, mint};
//!
//! // 遅延初期化される MOD を置く
//! // `STORAGE` は衝突しない任意の名前にしてください
//! define_mod!(M(usize); STORAGE);
//!
//! // 以下 main 関数
//! M::set(19);
//! let x = mint::<M>(12);
//! let y = mint::<M>(13);
//! assert_eq!(x + y, mint::<M>(6));
//! ```

use std::{
    cmp::{Eq, PartialEq},
    fmt::{self, Debug, Display},
    marker::PhantomData,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign},
};

/// # 遅延初期化される MOD を定義する
///
/// * `$name`: 型名
/// * `$type`: 内部型
/// * `$storage_name`: [`thread_local`] な [`Cell`](std::cell::Cell) の名前 (以降書かない。衝突しない名前ならなんでも OK)
///
#[macro_export]
macro_rules! define_mod {
    ($name:ident($type:ty); $storage_name:ident) => {
        thread_local! {
            static $storage_name: std::cell::Cell<$type> = const { std::cell::Cell::new(0) };
        }

        enum $name {}
        impl $crate::Mod for $name {
            type Value = $type;
            fn get() -> $type {
                $storage_name.get()
            }
            fn set(value: $type) {
                $storage_name.set(value)
            }
        }
    };
}

/// 法を指定するためのタグ型
pub trait Mod {
    type Value: Scalar;

    fn get() -> Self::Value;

    fn set(value: Self::Value);
}

/// ベースとなる整数型 (primitive unsigned int)
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
    const CONST_0: Self;
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

/// 実行時 modint 型
pub struct Mint<M: Mod> {
    value: M::Value,
    _marker: PhantomData<M>,
}
impl<M: Mod> Mint<M> {
    /// 中身の整数を取り出す
    pub const fn value(self) -> M::Value {
        self.value
    }
    /// 整数を受け取って、[`Mint`] を構築する
    pub const fn new(value: M::Value) -> Self {
        Self {
            value,
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

/// [`Mint::new`] と同じ
pub const fn mint<M: Mod>(value: M::Value) -> Mint<M> {
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
        Mint::new(iter.map(Mint::value).fold(M::Value::CONST_0, Add::add) % M::get())
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

    define_mod!(M(u64); STORAGE);

    #[test]
    fn test_set_mod_19() {
        M::set(19);
        let x = mint::<M>(12);
        let y = mint::<M>(13);
        assert_eq!(x + y, mint::<M>(6));
    }
}
