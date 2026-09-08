use std::fmt::Debug;
use std::mem::size_of;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::BitAnd;
use std::ops::BitAndAssign;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::BitXor;
use std::ops::BitXorAssign;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Not;
use std::ops::Shl;
use std::ops::ShlAssign;
use std::ops::Shr;
use std::ops::ShrAssign;
use std::ops::Sub;
use std::ops::SubAssign;

/// 符号なし整数型に共通の演算・定数をまとめたトレイト。
///
/// `usize`, `u8`, `u16`, `u32`, `u64`, `u128` に実装済み。ビットマスク操作
/// （[`crate::bitmask_combinations`], [`crate::bitmask_subsets`], [`crate::i2powm1`]）が
/// 型非依存で書けるようにするための抽象化。
pub trait Unsigned:
    Sized
    + PartialEq
    + PartialOrd
    + Debug
    + Clone
    + Copy
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
    + Mul<Output = Self>
    + MulAssign
    + Div<Output = Self>
    + DivAssign
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
    + Not<Output = Self>
{
    /// ビット幅。
    const BITS: u32;
    /// 最大値。
    const MAX: Self;
    /// $0$。
    const ZERO: Self;
    /// $1$。
    const ONE: Self;
    /// ラップアラウンドする単項マイナス（$2^{\mathrm{BITS}}$ を法とした $-\mathrm{self}$）。
    fn wrapping_neg(self) -> Self;
    /// ビット幅を返す（型のバイト数 $\times 8$）。`BITS` と同じ値。
    fn bit_length() -> u32 {
        size_of::<Self>() as u32 * 8
    }
}

macro_rules! impl_unsigned {
    ($($T:ty),* $(,)?) => {$(
        impl Unsigned for $T {
            const BITS: u32 = <$T>::BITS;
            const MAX: Self = <$T>::MAX;
            const ZERO: Self = 0;
            const ONE: Self = 1;
            fn wrapping_neg(self) -> Self { self.wrapping_neg() }
        }
    )*}
}

impl_unsigned! { usize, u8, u16, u32, u64, u128 }
