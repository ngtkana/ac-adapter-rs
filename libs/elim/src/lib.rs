//! GF(2) 上の 0-1 行列を列基本変形し、ランクを求める。
//!
//! 各列を $\mathbb{F}_2$ ベクトル空間の元とみなし、列の入れ替え・列同士の加算（XOR）という
//! 列に対する基本変形だけで掃き出し法を行う。列基本変形は列ベクトルの張る空間を変えないため、
//! 変形後の行列からランクを直接読み取れる。
//!
//! # 仕様
//!
//! [`column_reduce`] は $h \times w$ の 0-1 行列 $A$（`bool` で表現、真が 1）を破壊的に
//! 列基本変形し、ランク $r$ を返す。変形後の行列は次を満たす（列基本形）。
//! ピボット行を $p_1 < p_2 < \cdots < p_r$ とすると、
//!
//! - 列ベクトルの張る空間は変形前後で不変
//! - $j \le r$ のとき、第 $j$ 列は行 $p_j$ が 1、他のピボット行 $p_1, \ldots, p_r$（$p_j$ を除く）が 0
//! - $j > r$ のとき、第 $j$ 列はすべて 0
//!
//! # 例
//!
//! ```
//! use elim::column_reduce;
//!
//! let mut a = vec![
//!     vec![false, true, true],
//!     vec![false, true, true],
//!     vec![true, true, false],
//! ];
//! let r = column_reduce(&mut a);
//! assert_eq!(r, 2);
//! assert_eq!(a, vec![
//!     vec![true, false, false],
//!     vec![true, false, false],
//!     vec![false, true, false],
//! ]);
//! ```
//!
//! # 計算量
//!
//! - [`column_reduce`][]: $O(hw\min(h, w))$

/// 0-1 行列を列基本変形し、ランクを返す。
///
/// 列ベクトルの張る空間を保ったまま列基本形（詳細は[モジュールの説明](crate)を参照）に変形する。
///
/// # 例
///
/// ```
/// use elim::column_reduce;
///
/// let mut a = vec![vec![false, true, true], vec![false, true, true], vec![
///     true, true, false,
/// ]];
/// let r = column_reduce(&mut a);
/// assert_eq!(r, 2);
/// assert_eq!(a, vec![
///     vec![true, false, false],
///     vec![true, false, false],
///     vec![false, true, false],
/// ]);
/// ```
pub fn column_reduce(a: &mut [Vec<bool>]) -> usize {
    let h = a.len();
    let w = a[0].len();
    let mut i = 0;
    let mut j = 0;
    let mut rank = 0;
    while let Some([i_swp, j_swp]) = (i..h)
        .flat_map(|i| (j..w).map(move |j| [i, j]))
        .find(|&[i, j]| a[i][j])
    {
        i = i_swp;
        for a in a.iter_mut() {
            a.swap(j, j_swp);
        }
        for j1 in (0..w).filter(|&j1| j1 != j) {
            if a[i][j1] {
                a.iter_mut()
                    .filter(|ai| ai[j])
                    .for_each(|ai| ai[j1] ^= true);
            }
        }
        rank += 1;
        i += 1;
        j += 1;
    }
    rank
}

#[cfg(test)]
mod tests {
    use super::column_reduce;
    use itertools::Itertools;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter::repeat_with;
    use std::ops::BitXor;

    fn assert_column_reduced(a: &[Vec<bool>]) {
        let h = a.len();
        let w = a[0].len();
        let mut used = vec![false; h];
        for j in (0..w).rev() {
            if let Some(pivot) = a.iter().position(|ai| ai[j]) {
                used[pivot] = true;
                assert!(used[..pivot].iter().all(|&x| !x));
                assert!((pivot + 1..h).all(|i| !used[i] || !a[i][j]));
            }
        }
    }
    fn spanning_space(a: &[Vec<bool>]) -> Vec<Vec<bool>> {
        let w = a.len();
        let mut ans = (0..1 << w)
            .map(|bs| {
                a.iter()
                    .map(|ai| {
                        (0..w)
                            .filter(|&j| bs >> j & 1 == 1)
                            .map(|j| ai[j])
                            .fold(false, BitXor::bitxor)
                    })
                    .collect_vec()
            })
            .collect_vec();
        ans.sort();
        assert!(ans.len().is_power_of_two());
        ans
    }

    #[test]
    fn test_column_reduce() {
        let mut rng = StdRng::seed_from_u64(42);
        let test = |rng: &mut StdRng, numer: u32, denom: u32| {
            for _ in 0..50 {
                let n = rng.gen_range(1..=6);
                let a = repeat_with(|| {
                    repeat_with(|| rng.gen_ratio(numer, denom))
                        .take(n)
                        .collect_vec()
                })
                .take(n)
                .collect_vec();
                let mut b = a.clone();
                column_reduce(&mut b);
                assert_column_reduced(&b);
                assert_eq!(spanning_space(&a), spanning_space(&b));
            }
        };
        test(&mut rng, 1, 2);
        test(&mut rng, 1, 10);
        test(&mut rng, 1, 50);
    }
}
