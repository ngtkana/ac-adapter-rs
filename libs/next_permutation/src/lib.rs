//! 順列・shuffle・整数の分割を辞書順に列挙する。
//!
//! いずれも「現在の並びを、辞書順で次（または前）の並びに $O(n)$ で書き換える」`next_*`/`prev_*`
//! 系関数を核とする。全列挙はこれを、それ以上次が無くなる（`false` が返る）まで繰り返すことで
//! 実現し、`for_each_*` はコールバック方式、`*(...)` は結果を `Vec` に集めて返す。
//! `next_*` はソート済み（昇順）の初期状態から呼び始めれば辞書順最小から昇順に列挙できる。
//!
//! # 仕様
//!
//! - 順列: [`next_permutation`][], [`for_each_permutation`][], [`permutations`][]
//! - $(K, N-K)$-shuffle（`a[..k]`, `a[k..]` それぞれの相対順序を保ったまま2群に混ぜる方法）:
//!   [`next_shuffle`][], [`for_each_shuffle`][], [`shuffles`][]
//! - ペアリング（$(2, 2, \ldots, 2)$-shuffle。$n$ 個の要素を $n/2$ 組のペアに分ける）:
//!   [`next_pairing`][], [`for_each_pairing`][], [`pairings`][]
//! - 整数の分割（分割は正整数の非増加列で表し、列自体は辞書順に昇順で列挙）:
//!   [`next_partition`][], [`for_each_partition`][], [`partitions`][]
//! - 整数の分割（上記と同じ表現・逆順に列挙）:
//!   [`prev_partition`][], [`for_each_partition_rev`][], [`partitions_rev`][]
//!
//! # 例
//!
//! ```
//! use next_permutation::permutations;
//!
//! let ps = permutations(vec![1, 2, 3]);
//! assert_eq!(ps.len(), 6); // 3! = 6 通り
//! assert_eq!(ps[0], vec![1, 2, 3]); // 辞書順最小から始まる
//! assert_eq!(ps[5], vec![3, 2, 1]); // 辞書順最大で終わる
//! ```
//!
//! # 計算量
//!
//! - `next_*`/`prev_*`（[`next_permutation`][] 等）: ならし $O(n)$
//! - 全列挙系（[`permutations`][] 等）: 総和で $O(n \cdot (\text{列挙数}))$

/// `a` を辞書順で次の順列に書き換える。次が無ければ `false` を返す。
///
/// 末尾から見て最初に増加している位置 $i$（$a_i < a_{i+1}$）を探し、$a_i$ より大きい要素のうち
/// 末尾に最も近いもの $a_j$ と交換した後、$i$ より後ろを反転することで次の順列を得る。
///
/// # 例
///
/// ```
/// use next_permutation::next_permutation;
///
/// let mut a = vec![1, 2, 3];
/// assert!(next_permutation(&mut a));
/// assert_eq!(a, vec![1, 3, 2]);
///
/// let mut a = vec![3, 2, 1]; // 辞書順最大
/// assert!(!next_permutation(&mut a));
/// ```
pub fn next_permutation<T: Ord>(a: &mut [T]) -> bool {
    let Some(i) = a.windows(2).rposition(|w| w[0] < w[1]) else {
        return false;
    };
    let j = a.iter().rposition(|x| x > &a[i]).unwrap();
    a.swap(i, j);
    a[i + 1..].reverse();
    true
}

/// `a` をソートしてから、辞書順の全順列それぞれについて `f` を呼び出す。
///
/// # 例
///
/// ```
/// use next_permutation::for_each_permutation;
///
/// let mut result = Vec::new();
/// for_each_permutation(&mut [2, 1], |a| result.push(a.to_vec()));
/// assert_eq!(result, vec![vec![1, 2], vec![2, 1]]);
/// ```
pub fn for_each_permutation<T: Ord, F: FnMut(&[T])>(a: &mut [T], mut f: F) {
    a.sort();
    while {
        f(a);
        next_permutation(a)
    } {}
}

/// `a` の辞書順の全順列を返す。
///
/// # 例
///
/// ```
/// use next_permutation::permutations;
///
/// assert_eq!(permutations(vec![1, 2]), vec![vec![1, 2], vec![2, 1]]);
/// ```
pub fn permutations<T: Ord + Clone>(mut a: Vec<T>) -> Vec<Vec<T>> {
    let mut result = Vec::new();
    for_each_permutation(&mut a, |a| result.push(a.to_vec()));
    result
}

/// `a` を、`a[..k]` と `a[k..]` の内部の相対順序を保ったまま混ぜる方法（$(K, N-K)$-shuffle）
/// として辞書順で次のものに書き換える。次が無ければ `false` を返す。
///
/// # 例
///
/// ```
/// use next_permutation::next_shuffle;
///
/// let mut a = vec![0, 1, 2]; // k = 1: [0] と [1, 2] を混ぜる
/// assert!(next_shuffle(&mut a, 1));
/// assert_eq!(a, vec![1, 0, 2]);
/// ```
pub fn next_shuffle<T: Ord>(a: &mut [T], k: usize) -> bool {
    let n = a.len();
    if n == k {
        return false;
    }
    let (left, right) = a.split_at_mut(k);
    let Some(mut i) = left.iter().rposition(|x| x < right.last().unwrap()) else {
        return false;
    };
    let mut j = right.iter().position(|x| &left[i] < x).unwrap();
    std::mem::swap(&mut left[i], &mut right[j]);
    i += 1;
    j += 1;
    let swap_len = (k - i).min(n - k - j);
    left[k - swap_len..].swap_with_slice(&mut right[j..j + swap_len]);
    left[i..].rotate_left(k.saturating_sub(i + swap_len));
    right[j..].rotate_right((n - k).saturating_sub(j + swap_len));
    true
}

/// `a` をソートしてから、辞書順の全 $(K, N-K)$-shuffle それぞれについて、前半 `a[..k]` を
/// 引数に `f` を呼び出す。
///
/// # 例
///
/// ```
/// use next_permutation::for_each_shuffle;
///
/// let mut result = Vec::new();
/// for_each_shuffle(&mut [1, 0], 1, |a| result.push(a.to_vec()));
/// assert_eq!(result, vec![vec![0], vec![1]]);
/// ```
pub fn for_each_shuffle<T: Ord, F: FnMut(&[T])>(a: &mut [T], k: usize, mut f: F) {
    a.sort();
    while {
        f(&a[..k]);
        next_shuffle(a, k)
    } {}
}

/// `a` の辞書順の全 $(K, N-K)$-shuffle を、それぞれの前半部分（長さ $k$）の列として返す。
///
/// # 例
///
/// ```
/// use next_permutation::shuffles;
///
/// assert_eq!(shuffles(vec![0, 1], 1), vec![vec![0], vec![1]]);
/// ```
pub fn shuffles<T: Ord + Clone>(mut a: Vec<T>, k: usize) -> Vec<Vec<T>> {
    let mut result = Vec::new();
    for_each_shuffle(&mut a, k, |a| result.push(a.to_vec()));
    result
}

/// `a` をペアリング（$n$ 個の要素を $n/2$ 組のペアに分けたもの。各ペア内・各ペアの先頭同士は
/// 昇順）として辞書順で次のものに書き換える。次が無ければ `false` を返す。
///
/// `a.len()` は偶数かつ $32$ 以下であること（内部で `u32` のビットマスクを使うため）。
///
/// # 例
///
/// ```
/// use next_permutation::next_pairing;
///
/// let mut a = vec![0, 1, 2, 3]; // ペア (0,1), (2,3)
/// assert!(next_pairing(&mut a));
/// assert_eq!(a, vec![0, 2, 1, 3]); // ペア (0,2), (1,3)
/// ```
pub fn next_pairing(a: &mut [usize]) -> bool {
    assert!(a.len() % 2 == 0);
    assert!(a.len() <= 32);
    let n = a.len();
    let mut used = 0_u32;
    for i in (0..n).rev() {
        used |= 1 << a[i];
        if i % 2 == 1 && a[i] + 1 < (used + 1).next_power_of_two().trailing_zeros() as usize {
            a[i] = (used >> (a[i] + 1)).trailing_zeros() as usize + a[i] + 1;
            used ^= 1 << a[i];
            for x in &mut a[i + 1..n] {
                *x = used.trailing_zeros() as usize;
                used ^= 1 << *x;
            }
            return true;
        }
    }
    false
}

/// $0, \ldots, n-1$ の辞書順の全ペアリングそれぞれについて `f` を呼び出す。
///
/// # 例
///
/// ```
/// use next_permutation::for_each_pairing;
///
/// let mut result = Vec::new();
/// for_each_pairing(4, |a| result.push(a.to_vec()));
/// assert_eq!(result.len(), 3); // (0,1)(2,3), (0,2)(1,3), (0,3)(1,2)
/// ```
pub fn for_each_pairing<F: FnMut(&[usize])>(n: usize, mut f: F) {
    let mut a = (0..n).collect::<Vec<_>>();
    while {
        f(&a);
        next_pairing(&mut a)
    } {}
}

/// $0, \ldots, n-1$ の辞書順の全ペアリングを返す。
///
/// # 例
///
/// ```
/// use next_permutation::pairings;
///
/// assert_eq!(pairings(2), vec![vec![0, 1]]);
/// ```
pub fn pairings(n: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for_each_pairing(n, |a| result.push(a.to_vec()));
    result
}

/// `a`（総和一定の正整数の非増加列として整数の分割を表す）を辞書順で次の分割に書き換える。
/// 次が無ければ `false` を返す。
///
/// # 例
///
/// ```
/// use next_permutation::next_partition;
///
/// let mut a = vec![1, 1, 1, 1]; // 4 = 1+1+1+1
/// assert!(next_partition(&mut a));
/// assert_eq!(a, vec![2, 1, 1]); // 4 = 2+1+1
/// ```
pub fn next_partition(a: &mut Vec<usize>) -> bool {
    let Some(mut sum) = a.pop() else { return false };
    if a.is_empty() {
        return false;
    }
    while let Some(x) = a.pop() {
        sum += x;
        if a.last().is_none_or(|&last| last > x) {
            a.push(x + 1);
            a.extend(std::iter::repeat_n(1, sum - x - 1));
            break;
        }
    }
    true
}

/// $n$ の辞書順の全分割それぞれについて `f` を呼び出す。
///
/// # 例
///
/// ```
/// use next_permutation::for_each_partition;
///
/// let mut result = Vec::new();
/// for_each_partition(3, |a| result.push(a.to_vec()));
/// assert_eq!(result, vec![vec![1, 1, 1], vec![2, 1], vec![3]]);
/// ```
pub fn for_each_partition<F: FnMut(&[usize])>(n: usize, mut f: F) {
    let mut a = vec![1; n];
    while {
        f(&a);
        next_partition(&mut a)
    } {}
}

/// $n$ の辞書順の全分割を返す。
///
/// # 例
///
/// ```
/// use next_permutation::partitions;
///
/// assert_eq!(partitions(3), vec![vec![1, 1, 1], vec![2, 1], vec![3]]);
/// ```
pub fn partitions(n: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for_each_partition(n, |a| result.push(a.to_vec()));
    result
}

/// `a`（総和一定の正整数の非増加列として整数の分割を表す）を辞書順で前の分割に書き換える。
/// 前が無ければ `false` を返す。[`next_partition`][] のちょうど逆操作。
///
/// # 例
///
/// ```
/// use next_permutation::prev_partition;
///
/// let mut a = vec![3];
/// assert!(prev_partition(&mut a));
/// assert_eq!(a, vec![2, 1]);
/// ```
pub fn prev_partition(a: &mut Vec<usize>) -> bool {
    let Some(i) = a.iter().rposition(|&x| x != 1) else {
        return false;
    };
    let max = a[i] - 1;
    let mut sum = a.split_off(i).into_iter().sum::<usize>();
    while sum >= max {
        a.push(max);
        sum -= max;
    }
    if sum > 0 {
        a.push(sum);
    }
    true
}

/// $n$ の辞書順の逆順（[`partitions`][] と逆順）の全分割それぞれについて `f` を呼び出す。
///
/// # 例
///
/// ```
/// use next_permutation::for_each_partition_rev;
///
/// let mut result = Vec::new();
/// for_each_partition_rev(3, |a| result.push(a.to_vec()));
/// assert_eq!(result, vec![vec![3], vec![2, 1], vec![1, 1, 1]]);
/// ```
pub fn for_each_partition_rev<F: FnMut(&[usize])>(n: usize, mut f: F) {
    if n == 0 {
        f(&[]);
        return;
    }
    let mut a = vec![n];
    while {
        f(&a);
        prev_partition(&mut a)
    } {}
}

/// $n$ の辞書順の逆順（[`partitions`][] と逆順）の全分割を返す。
///
/// # 例
///
/// ```
/// use next_permutation::partitions_rev;
///
/// assert_eq!(partitions_rev(3), vec![vec![3], vec![2, 1], vec![1, 1, 1]]);
/// ```
pub fn partitions_rev(n: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for_each_partition_rev(n, |a| result.push(a.to_vec()));
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;

    #[test]
    fn test_permutations() {
        for n in 0..=5 {
            let result = permutations((0..n).collect::<Vec<_>>());
            assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
            assert_eq!(result.len(), (1..=n).product());
        }
    }

    #[test]
    fn test_shuffles() {
        for n in 0..=5 {
            for k in 0..=n {
                let result = shuffles((0..n).collect::<Vec<_>>(), k);
                for result in &result {
                    assert!(result[..k].iter().tuple_windows().all(|(a, b)| a < b));
                    assert!(result[k..].iter().tuple_windows().all(|(a, b)| a < b));
                }
                assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
                assert_eq!(
                    result.len(),
                    (1..=n).product::<usize>()
                        / (1..=k).product::<usize>()
                        / (1..=(n - k)).product::<usize>()
                );
            }
        }
    }

    #[test]
    fn test_pairings() {
        for n in (0..=10).step_by(2) {
            let result = pairings(n);
            assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
            for result in &result {
                assert!(result.chunks_exact(2).all(|x| x[0] < x[1]));
                assert!(result.iter().step_by(2).tuple_windows().all(|(a, b)| a < b));
            }
            assert_eq!(result.len(), (1..=n).step_by(2).product::<usize>());
        }
    }

    #[test]
    fn test_partitions() {
        let n = 10;
        let mut p = vec![1; n];
        for step in 2..n {
            for i in 0..n - step {
                p[i + step] += p[i];
            }
        }
        for (n, &p) in p.iter().enumerate() {
            let result = partitions(n);
            assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
            assert_eq!(result.len(), p);
            assert_eq!(result, partitions_rev(n).into_iter().rev().collect_vec());
        }
    }
}
