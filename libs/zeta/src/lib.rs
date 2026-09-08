//! 冪集合上の高速ゼータ変換・高速メビウス変換。
//!
//! 添字をビット集合とみなし、1 ビットだけ異なる添字のペアを順に更新することで、
//! 全 $2^n$ 個の部分集合について「可換結合演算 `f` による部分集合和」を
//! $O(n 2^n)$ で一括計算する（$n$ はビット数）。逆変換（メビウス変換）は
//! `f` が可換群の加法である場合に限り、減算により定義できる。
//!
//! # 仕様
//!
//! [`for_each`] が実装の共通部分で、1 ビットだけ異なるペアすべてに関数を適用する。
//! [`zeta`] と [`rzeta`] は任意の可換結合演算による部分集合和・上位集合和のゼータ変換で、
//! 演算ごとに `add`/`radd`, `max`/`rmax`, `min`/`rmin`, `bitxor`/`rbitxor`, `bitor`/`rbitor`,
//! `bitand`/`rbitand` の特殊化を用意する。加法のみ [`add_inv`] / [`add_rinv`] で逆変換
//! （メビウス変換）ができる。[`aggr`] は単元集合上の値から、全部分集合の畳み込み結果をまとめて構築する。
//!
//! | 演算 | ゼータ変換 | 逆順ゼータ変換 | メビウス変換 | 逆順メビウス変換 |
//! | --- | --- | --- | --- | --- |
//! | 一般 | [`zeta`] | [`rzeta`] | 非可逆 | 非可逆 |
//! | + | [`add`] | [`radd`] | [`add_inv`] | [`add_rinv`] |
//! | max | [`max`] | [`rmax`] | 非可逆 | 非可逆 |
//! | min | [`min`] | [`rmin`] | 非可逆 | 非可逆 |
//! | ^ | [`bitxor`] | [`rbitxor`] | [`bitxor`] | [`bitxor`] |
//! | \| | [`bitor`] | [`rbitor`] | 非可逆 | 非可逆 |
//! | & | [`bitand`] | [`rbitand`] | 非可逆 | 非可逆 |
//!
//! # 例
//!
//! ```
//! use zeta::add;
//! use zeta::add_inv;
//!
//! let mut a = [1, 2, 4, 8];
//! add(&mut a); // 添字を部分集合とみなした部分集合和
//! assert_eq!(a, [1, 3, 5, 15]);
//!
//! add_inv(&mut a); // 加法のメビウス変換で元に戻る
//! assert_eq!(a, [1, 2, 4, 8]);
//! ```
//!
//! # 計算量
//!
//! 配列長を $n$（$2$ 冪）とすると、いずれの関数も `f` を $\frac{n \log n}{2}$ 回呼ぶ（$O(n \log n)$）。

use std::cmp::Ord;
use std::cmp::{self};
use std::ops::Add;
use std::ops::BitAnd;
use std::ops::BitOr;
use std::ops::BitXor;
use std::ops::Sub;

/// 添字をビット集合とみなし、1 ビットだけ異なるペア `(bs, bs | 1 << i)` すべてに `f` を適用する。
///
/// [`zeta`]・[`rzeta`] の実装の共通部分。`a` の長さは $2$ 冪であることが前提。
///
/// # 計算量
///
/// $O(n 2^n)$（`a` の長さが $2^n$）
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

/// 可換結合演算 `f` によるゼータ変換：$a(S) \gets \bigoplus_{T \subseteq S} a(T)$。
///
/// `a` の長さは $2$ 冪、`f` は可換かつ結合的であることが前提。
///
/// # 例
///
/// 累積和は [`add`] で計算できるが、あえて `zeta` で書くと次のようになる。
///
/// ```
/// # use zeta::zeta;
/// let mut a = [1, 2, 4, 8];
/// zeta(&mut a, |x, y| x + y);
/// assert_eq!(a, [1, 3, 5, 15]);
/// ```
pub fn zeta<T: Copy>(a: &mut [T], f: impl Fn(T, T) -> T) {
    for_each(a, |x, y| *y = f(*x, *y));
}

/// 可換結合演算 `f` による上位集合方向のゼータ変換：$a(S) \gets \bigoplus_{S \subseteq T} a(T)$。
///
/// `a` の長さは $2$ 冪、`f` は可換かつ結合的であることが前提。
///
/// # 例
///
/// ```
/// # use zeta::rzeta;
/// let mut a = [1, 2, 4, 8];
/// rzeta(&mut a, |x, y| x + y);
/// assert_eq!(a, [15, 10, 12, 8]);
/// ```
pub fn rzeta<T: Copy>(a: &mut [T], f: impl Fn(T, T) -> T) {
    for_each(a, |x, y| *x = f(*x, *y));
}
/// 加法によるゼータ変換（[`zeta`] の特殊化）：$a(S) \gets \sum_{T \subseteq S} a(T)$。
pub fn add<T: Copy + Add<Output = T>>(a: &mut [T]) {
    zeta(a, Add::add);
}
/// 加法による上位集合方向のゼータ変換（[`rzeta`] の特殊化）：$a(S) \gets \sum_{S \subseteq T} a(T)$。
pub fn radd<T: Copy + Add<Output = T>>(a: &mut [T]) {
    rzeta(a, Add::add);
}
/// 加法のメビウス変換（[`add`] の逆演算）：$a(S) \gets \sum_{T \subseteq S} (-1)^{|S \setminus T|} a(T)$。
///
/// # 例
///
/// ```
/// # use zeta::add_inv;
/// let mut a = [1, 3, 5, 15];
/// add_inv(&mut a);
/// assert_eq!(a, [1, 2, 4, 8]);
/// ```
pub fn add_inv<T: Copy + Sub<Output = T>>(a: &mut [T]) {
    zeta(a, |x, y| y - x);
}
/// 加法の上位集合方向のメビウス変換（[`radd`] の逆演算）：$a(S) \gets \sum_{S \subseteq T} (-1)^{|T \setminus S|} a(T)$。
pub fn add_rinv<T: Copy + Sub<Output = T>>(a: &mut [T]) {
    rzeta(a, |x, y| y - x);
}
/// 最大値によるゼータ変換（[`zeta`] の特殊化）：$a(S) \gets \max_{T \subseteq S} a(T)$。
pub fn max<T: Copy + Ord>(a: &mut [T]) {
    zeta(a, cmp::max);
}
/// 最大値による上位集合方向のゼータ変換（[`rzeta`] の特殊化）。
pub fn rmax<T: Copy + Ord>(a: &mut [T]) {
    rzeta(a, cmp::max);
}
/// 最小値によるゼータ変換（[`zeta`] の特殊化）：$a(S) \gets \min_{T \subseteq S} a(T)$。
pub fn min<T: Copy + Ord>(a: &mut [T]) {
    zeta(a, cmp::min);
}
/// 最小値による上位集合方向のゼータ変換（[`rzeta`] の特殊化）。
pub fn rmin<T: Copy + Ord>(a: &mut [T]) {
    rzeta(a, cmp::min);
}
/// bit-xor によるゼータ変換（[`zeta`] の特殊化）。
pub fn bitxor<T: Copy + BitXor<Output = T>>(a: &mut [T]) {
    zeta(a, BitXor::bitxor);
}
/// bit-xor による上位集合方向のゼータ変換（[`rzeta`] の特殊化）。
pub fn rbitxor<T: Copy + BitXor<Output = T>>(a: &mut [T]) {
    rzeta(a, BitXor::bitxor);
}
/// bit-or によるゼータ変換（[`zeta`] の特殊化）。
pub fn bitor<T: Copy + BitOr<Output = T>>(a: &mut [T]) {
    zeta(a, BitOr::bitor);
}
/// bit-or による上位集合方向のゼータ変換（[`rzeta`] の特殊化）。
pub fn rbitor<T: Copy + BitOr<Output = T>>(a: &mut [T]) {
    rzeta(a, BitOr::bitor);
}
/// bit-and によるゼータ変換（[`zeta`] の特殊化）。
pub fn bitand<T: Copy + BitAnd<Output = T>>(a: &mut [T]) {
    zeta(a, BitAnd::bitand);
}
/// bit-and による上位集合方向のゼータ変換（[`rzeta`] の特殊化）。
pub fn rbitand<T: Copy + BitAnd<Output = T>>(a: &mut [T]) {
    rzeta(a, BitAnd::bitand);
}

/// 単元集合上の値 `a` から、全 $2^n$ 個の部分集合の畳み込みを構築する（$n$ は `a` の長さ）。
///
/// 単位元 `e` で初期化した長さ $2^n$ の配列の添字 $2^i$ の位置へ `a[i]` を埋め込み、
/// [`zeta`] を適用する。
///
/// # 例
///
/// ```
/// use zeta::aggr;
/// let a = [1, 2, 4];
/// let b = aggr(&a, |x, y| x + y, 0);
/// assert_eq!(b, [0, 1, 2, 3, 4, 5, 6, 7]); // b[bs] = bs が立てているビットに対応する a[i] の総和
/// ```
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
    #[test_case(cmp::max, u32::MIN, max, Dir::Sub)]
    #[test_case(cmp::min, u32::MAX, min, Dir::Sub)]
    #[test_case(BitXor::bitxor, 0, bitxor, Dir::Sub)]
    #[test_case(BitOr::bitor, 0, bitor, Dir::Sub)]
    #[test_case(BitAnd::bitand, u32::MAX, bitand, Dir::Sub)]
    #[test_case(Add::add, 0, radd, Dir::Super)]
    #[test_case(cmp::max, u32::MIN, rmax, Dir::Super)]
    #[test_case(cmp::min, u32::MAX, rmin, Dir::Super)]
    #[test_case(BitXor::bitxor, 0, rbitxor, Dir::Super)]
    #[test_case(BitOr::bitor, 0, rbitor, Dir::Super)]
    #[test_case(BitAnd::bitand, u32::MAX, rbitand, Dir::Super)]
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
    #[test_case(cmp::max, u32::MIN)]
    #[test_case(cmp::min, u32::MAX)]
    #[test_case(BitXor::bitxor, 0)]
    #[test_case(BitOr::bitor, 0)]
    #[test_case(BitAnd::bitand, u32::MAX)]
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
