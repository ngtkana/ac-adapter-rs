//! 冪集合上の高速ゼータ変換、高速メビウス変換をします。
//!
//!
//! # なんでも屋さん [`for_each`]
//!
//! [`for_each`] は要素への可変参照を取ります。
//! これに `|x, y| x + y` を入れると正向き・逆向きの高速ゼータ変換ができ、
//! `|x, y| y - x` を入れると正向き・逆向きの高速メビウス変換がすべてできます。
//!
//!
//! # ゼータ変換
//!
//! ゼータ変換は、可換で結合的な 2 項演算に対して定義されています。
//! メビウス変換が定義されてそれが逆変換になるためには、アーベル群の加法である必要があります。
//!
//! |       | ゼータ変換   | 反転ゼータ変換    | メビウス変換   | 反転メビウス変換  |
//! | -     | -            | -                 | -              |  -                |
//! | 一般  | [`zeta`]     | [`rzeta`]         | 非可逆         | 非可逆            |
//! | +     | [`add`]      | [`radd`]          | [`add_inv`]    |  [`add_inv`]      |
//! | max   | [`max`]      | [`rmax`]          | 非可逆         | 非可逆            |
//! | min   | [`min`]      | [`rmin`]          | 非可逆         | 非可逆            |
//! | ^     | [`bitxor`]   | [`rbitxor`]       | [`bitxor`]     |  [`bitxor`]       |
//! | \|    | [`bitor`]    | [`rbitor`]        | 非可逆         | 非可逆            |
//! | &     | [`bitand`]   | [`rbitand`]       | 非可逆         | 非可逆            |
//!
//!
//! # Examples
//!
//! [`add`] で + に関するゼータ変換ができます。
//!
//! ```
//! use zeta::add;
//! use zeta::add_inv;
//!
//! let mut a = [1, 2, 4, 8];
//! add(&mut a);
//! assert_eq!(a, [1, 3, 5, 15]);
//! ```
//!
//! [`add_inv`] はメビウス変換です。中身は `rzeta(&a, |x, y| y - x)` です。
//!
//! ```
//! # use zeta::add_inv;
//! # let mut a = [1, 3, 5, 15];
//! add_inv(&mut a);
//! assert_eq!(a, [1, 2, 4, 8]);
//! ```
//!

use std::cmp::Ord;
use std::cmp::{self};
use std::ops::Add;
use std::ops::BitAnd;
use std::ops::BitOr;
use std::ops::BitXor;
use std::ops::Sub;

/// ゼータ変換・メビウス変換のための基本関数
pub fn for_each<T>(a: &mut [T], f: impl Fn(&mut T, &mut T)) {
    let n = a.len().trailing_zeros();
    assert_eq!(a.len(), 1 << n);
    for i in 0..n {
        for bs in 0..1 << n {
            if bs >> i & 1 == 0 {
                let (left, right) = a.split_at_mut(bs + 1);
                f(&mut left[bs], &mut right[(1 << i) - 1]);
            }
        }
    }
}

/// `f` を加法とするゼータ変換をします。
///
/// # 制約
///
/// - a の長さが 2 冪
/// - f が可換かつ結合的
///
///
/// # 効果
///
/// a( S ) = f { a ( T ): T ⊆ S }
///
///
/// # 計算量
///
/// n が配列の長さであるとして、f を丁度 (n lg n) / 2 回呼びます。
///
///
/// # Examples
///
/// 累積和は [`add`] を使うとよいのですが、あえて [`zeta`] を使うならばこうです。
///
/// ```
/// # use zeta::zeta;
/// let mut a = [1, 2, 4, 8];
/// zeta(&mut a, |x, y| x + y);
/// assert_eq!(a, [1, 3, 5, 15]);
/// ```
pub fn zeta<T: Copy>(a: &mut [T], f: impl Fn(T, T) -> T) { for_each(a, |x, y| *y = f(*x, *y)); }

/// 反転束において、`f` を加法とするゼータ変換をします。
///
/// # 制約
///
/// - a の長さが 2 冪
/// - f が可換かつ結合的
///
///
/// # 効果
///
/// a( S ) = f { a ( T ): S ⊆ T }
///
///
/// # 計算量
///
/// n が配列の長さであるとして、f を丁度 (n lg n) / 2 回呼びます。
///
///
/// # Examples
///
/// 累積和は [`add`] を使うとよいのですが、あえて [`zeta`] を使うならばこうです。
///
/// ```
/// # use zeta::rzeta;
/// let mut a = [1, 2, 4, 8];
/// rzeta(&mut a, |x, y| x + y);
/// assert_eq!(a, [15, 10, 12, 8]);
/// ```
pub fn rzeta<T: Copy>(a: &mut [T], f: impl Fn(T, T) -> T) { for_each(a, |x, y| *x = f(*x, *y)); }
/// \+ でゼータ変換
pub fn add<T: Copy + Add<Output = T>>(a: &mut [T]) { zeta(a, Add::add); }
/// 反転束において \+ でゼータ変換
pub fn radd<T: Copy + Add<Output = T>>(a: &mut [T]) { rzeta(a, Add::add); }
/// (+, -) でメビウス変換
pub fn add_inv<T: Copy + Sub<Output = T>>(a: &mut [T]) { zeta(a, |x, y| y - x) }
/// 反転束において (+, -) でメビウス変換
pub fn add_rinv<T: Copy + Sub<Output = T>>(a: &mut [T]) { rzeta(a, |x, y| y - x) }
/// max でゼータ変換
pub fn max<T: Copy + Ord>(a: &mut [T]) { zeta(a, cmp::max); }
/// 反転束において max でメビウス変換
pub fn rmax<T: Copy + Ord>(a: &mut [T]) { rzeta(a, cmp::max); }
/// min でゼータ変換
pub fn min<T: Copy + Ord>(a: &mut [T]) { zeta(a, cmp::min); }
/// 反転束において min でメビウス変換
pub fn rmin<T: Copy + Ord>(a: &mut [T]) { rzeta(a, cmp::min); }
/// bit-xor でゼータ変換
pub fn bitxor<T: Copy + BitXor<Output = T>>(a: &mut [T]) { zeta(a, BitXor::bitxor); }
/// 反転束において bit-xor でメビウス変換
pub fn rbitxor<T: Copy + BitXor<Output = T>>(a: &mut [T]) { rzeta(a, BitXor::bitxor); }
/// bit-or でゼータ変換
pub fn bitor<T: Copy + BitOr<Output = T>>(a: &mut [T]) { zeta(a, BitOr::bitor); }
/// 反転束において bit-or でメビウス変換
pub fn rbitor<T: Copy + BitOr<Output = T>>(a: &mut [T]) { rzeta(a, BitOr::bitor); }
/// bit-and でゼータ変換
pub fn bitand<T: Copy + BitAnd<Output = T>>(a: &mut [T]) { zeta(a, BitAnd::bitand); }
/// 反転束において bit-and でメビウス変換
pub fn rbitand<T: Copy + BitAnd<Output = T>>(a: &mut [T]) { rzeta(a, BitAnd::bitand); }

/// すべての添字集合に関して (二項演算 f, 単位元 e) で畳み込んだ結果を構築します。
pub fn aggr<T: Copy>(a: &[T], f: impl Fn(T, T) -> T, e: T) -> Vec<T> {
    let mut b = vec![e; 1 << a.len()];
    (0..a.len()).for_each(|i| b[1 << i] = a[i]);
    zeta(&mut b, f);
    b
}

#[cfg(test)]
mod tests {
    use super::add;
    use super::aggr;
    use super::bitand;
    use super::bitor;
    use super::bitxor;
    use super::max;
    use super::min;
    use super::radd;
    use super::rbitand;
    use super::rbitor;
    use super::rbitxor;
    use super::rmax;
    use super::rmin;
    use itertools::Itertools;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::cmp;
    use std::iter::repeat_with;
    use std::ops::Add;
    use std::ops::BitAnd;
    use std::ops::BitOr;
    use std::ops::BitXor;
    use test_case::test_case;

    #[derive(Clone, Copy)]
    enum Dir {
        Sub,
        Super,
    }

    #[allow(clippy::unused_unit)]
    #[test_case(Add::add, 0, add, Dir::Sub)]
    #[test_case(cmp::max, std::u32::MIN, max, Dir::Sub)]
    #[test_case(cmp::min, std::u32::MAX, min, Dir::Sub)]
    #[test_case(BitXor::bitxor, 0, bitxor, Dir::Sub)]
    #[test_case(BitOr::bitor, 0, bitor, Dir::Sub)]
    #[test_case(BitAnd::bitand, std::u32::MAX, bitand, Dir::Sub)]
    #[test_case(Add::add, 0, radd, Dir::Super)]
    #[test_case(cmp::max, std::u32::MIN, rmax, Dir::Super)]
    #[test_case(cmp::min, std::u32::MAX, rmin, Dir::Super)]
    #[test_case(BitXor::bitxor, 0, rbitxor, Dir::Super)]
    #[test_case(BitOr::bitor, 0, rbitor, Dir::Super)]
    #[test_case(BitAnd::bitand, std::u32::MAX, rbitand, Dir::Super)]
    fn test_zeta_ops(f: fn(u32, u32) -> u32, e: u32, g: fn(&mut [u32]), dir: Dir) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=5);
            let elms = repeat_with(|| rng.gen_range(0..=20))
                .take(1 << n)
                .collect_vec();
            let result = {
                let mut elms = elms.clone();
                g(&mut elms);
                elms
            };
            let expected = (0..1 << n)
                .map(|bs| {
                    elms.iter()
                        .enumerate()
                        .filter(|&(cs, _)| match dir {
                            Dir::Sub => !bs & cs == 0,
                            Dir::Super => bs & !cs == 0,
                        })
                        .map(|(_, &x)| x)
                        .fold(e, f)
                })
                .collect_vec();
            assert_eq!(result, expected);
        }
    }

    #[allow(clippy::unused_unit)]
    #[test_case(Add::add, 0)]
    #[test_case(cmp::max, std::u32::MIN)]
    #[test_case(cmp::min, std::u32::MAX)]
    #[test_case(BitXor::bitxor, 0)]
    #[test_case(BitOr::bitor, 0)]
    #[test_case(BitAnd::bitand, std::u32::MAX)]
    fn test_aggr(f: fn(u32, u32) -> u32, e: u32) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..=5);
            let elms = repeat_with(|| rng.gen_range(0..=20)).take(n).collect_vec();
            let result = aggr(&elms, f, e);
            let expected = (0..1 << n)
                .map(|bs| {
                    elms.iter()
                        .enumerate()
                        .filter(|&(i, _)| bs >> i & 1 == 1)
                        .map(|(_, &x)| x)
                        .fold(e, f)
                })
                .collect_vec();
            assert_eq!(result, expected);
        }
    }
}
