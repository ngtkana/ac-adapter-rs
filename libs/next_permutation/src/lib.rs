//! スライスの next-permutation アルゴリズムと、それによるイテレータを提供します。
//!
//! # `next_permutation` 系
//!
//! 次の置換が存在する場合は、受け取った可変スライス `state` をそれに変化させ、`true` を返します。
//! さもなくば、`state` には何も起こさず、`false` を返します。
//!
//! ## Examples
//!
//! ```
//! # use next_permutation::next_permutation;
//! let mut a = vec![1, 0, 2, 1];
//! assert_eq!(
//!     next_permutation(&mut a).map(|a| a.to_vec()),
//!     Some(vec![1, 1, 0, 2])
//! );
//! assert_eq!(a.as_slice(), &[1, 1, 0, 2]);
//! ```
//!
//! # `permutations` 系
//!
//! 受け取ったベクターの置換をすべて辞書順返すイテレータを返します。
//! 引数 `state` は必ずしもソートされていなくてもよいです。
//! （この関数の実装の最初に、自動的にソートされます。）
//!
//! ## Examples
//!
//! ```
//! # use next_permutation::permutations;
//! let a = vec![1, 0, 0];
//! let perms = permutations(a).collect::<Vec<_>>();
//! assert_eq!(perms, vec![vec![0, 0, 1], vec![0, 1, 0], vec![1, 0, 0]]);
//! ```
//!
//! # [`iter_by_next`] について
//!
//! [`next_permutation`] から [`permutations`] を作る操作を一般化したものです
//!
//! ## Examples
//!
//! 直積全探索の例です。
//!
//! ```
//! # use next_permutation::iter_by_next;
//! let n = 3;
//! let value_lim = 3;
//!
//! let result = iter_by_next(vec![0; n], |state: &mut [_]| {
//!     // `state` に型注釈が必要です。
//!     state.iter().rposition(|&x| x + 1 != value_lim).map(|i| {
//!         state[i] += 1;
//!         state[i + 1..].iter_mut().for_each(|x| *x = 0);
//!         state
//!     })
//! })
//! .collect::<Vec<_>>();
//!
//! let mut expected = Vec::new();
//! for i in 0..value_lim {
//!     for j in 0..value_lim {
//!         for k in 0..value_lim {
//!             expected.push(vec![i, j, k]);
//!         }
//!     }
//! }
//! assert_eq!(result, expected);
//! ```

use std::borrow::BorrowMut;
use std::cmp::Ordering;
use std::iter::once;
use std::iter::repeat;

/// 遷移関数からイテレータを作ります。
pub fn iter_by_next<T, U: ?Sized>(
    init: T,
    mut next: impl FnMut(&mut U) -> Option<&mut U>,
) -> impl Iterator<Item = T>
where
    T: BorrowMut<U> + Clone,
    U: ToOwned<Owned = T>,
{
    once(init.clone()).chain(repeat(()).scan(init, move |state, ()| {
        next(state.borrow_mut()).map(|state| state.to_owned())
    }))
}

/// 要素の [`Ord`] による比較により、受け取ったスライスを次の置換に遷移します。
///
/// # Returns
///
/// 次の置換が存在した場合、`true` を返します。
///
/// # Effects
///
/// 次の置換が存在した場合、次の置換に遷移します。
/// さもなくば何も起こりません。
pub fn next_permutation<T: Ord>(state: &mut [T]) -> Option<&mut [T]> {
    next_permutation_by(state, Ord::cmp)
}

pub fn next_permutation_by_key<T, U, F>(state: &mut [T], mut f: F) -> Option<&mut [T]>
where
    F: FnMut(&T) -> U,
    U: Ord,
{
    next_permutation_by(state, |x, y| f(x).cmp(&f(y)))
}

/// 引数の比較関数により比較して、受け取ったスライスを次の置換に遷移します。
///
/// # Returns
///
/// 次の置換が存在した場合、`true` を返します。
///
/// # Effects
///
/// 次の置換が存在した場合、次の置換に遷移します。
/// さもなくば何も起こりません。
pub fn next_permutation_by<T>(
    state: &mut [T],
    mut cmp: impl FnMut(&T, &T) -> Ordering,
) -> Option<&mut [T]> {
    (0..state.len() - 1)
        .rfind(|&i| cmp(&state[i], &state[i + 1]) == Ordering::Less)
        .map(|i| {
            state[i + 1..].reverse();
            let j = i
                + 1
                + state[i + 1..]
                    .iter()
                    .position(|x| cmp(&state[i], x) == (Ordering::Less))
                    .unwrap();
            state.swap(i, j);
            state
        })
}

/// 要素を射影して、受け取ったベクターの置換をすべて辞書順返すイテレータを返します。
///
/// 引数 `state` は必ずしもソートされていなくてもよいです。
/// （この関数の実装の最初に、自動的にソートされます。）
pub fn permutations<T>(mut state: Vec<T>) -> impl Iterator<Item = Vec<T>>
where
    T: Clone + Ord,
{
    state.sort();
    iter_by_next(state, next_permutation)
}

/// 要素の [`Ord`] による比較により、
/// 受け取ったベクターの置換をすべて辞書順返すイテレータを返します。
///
/// 引数 `state` は必ずしもソートされていなくてもよいです。
/// （この関数の実装の最初に、自動的にソートされます。）
pub fn permutations_by_key<T, U, F>(mut state: Vec<T>, f: F) -> impl Iterator<Item = Vec<T>>
where
    T: Clone,
    U: Ord,
    F: FnMut(&T) -> U + Copy,
{
    state.sort_by_key(f);
    iter_by_next(state, move |state| next_permutation_by_key(state, f))
}

/// 引数の比較関数により比較して、受け取ったベクターの置換をすべて辞書順返すイテレータを返します。
///
/// 引数 `state` は必ずしもソートされていなくてもよいです。
/// （この関数の実装の最初に、自動的にソートされます。）
pub fn permutations_by<T, C>(mut state: Vec<T>, cmp: C) -> impl Iterator<Item = Vec<T>>
where
    T: Clone,
    C: FnMut(&T, &T) -> Ordering + Copy,
{
    state.sort_by(cmp);
    iter_by_next(state, move |state| next_permutation_by(state, cmp))
}

#[cfg(tests)]
mod tests {
    use super::*;
    use itertools::Itertools;

    fn make_perms() -> Vec<Vec<usize>> {
        vec![
            vec![0, 1, 1, 2],
            vec![0, 1, 2, 1],
            vec![0, 2, 1, 1],
            vec![1, 0, 1, 2],
            vec![1, 0, 2, 1],
            vec![1, 1, 0, 2],
            vec![1, 1, 2, 0],
            vec![1, 2, 0, 1],
            vec![1, 2, 1, 0],
            vec![2, 0, 1, 1],
            vec![2, 1, 0, 1],
            vec![2, 1, 1, 0],
        ]
    }

    #[test]
    fn test_next_permutation() {
        let perms = make_perms();
        for v in perms.windows(2) {
            let mut from = v[0].clone();
            let to = &v[1];
            next_permutation(&mut from);
            assert_eq!(&from, to);
        }
    }

    #[test]
    fn test_next_permutation_by_key() {
        let perms = make_perms();
        for v in perms.windows(2) {
            let mut from = v[0].clone();
            let to = &v[1];
            next_permutation_by_key(&mut from, |x| x);
            assert_eq!(&from, to);
        }
    }

    #[test]
    fn test_next_permutation_by() {
        let perms = make_perms();
        for v in perms.windows(2) {
            let mut from = v[0].clone();
            let to = &v[1];
            next_permutation_by(&mut from, |x, y| x.cmp(&y));
            assert_eq!(&from, to);
        }
    }

    #[test]
    fn test_permutations() {
        let a = vec![1, 0, 1, 2];
        let perms = permutations(a).collect_vec();
        let expected = make_perms();
        assert_eq!(expected, perms);
    }

    #[test]
    fn test_permutations_by_key() {
        let a = vec![1, 0, 1, 2];
        let perms = permutations_by_key(a, |x| x).collect_vec();
        let expected = make_perms();
        assert_eq!(expected, perms);
    }

    #[test]
    fn test_permutations_by() {
        let a = vec![1, 0, 1, 2];
        let perms = permutations_by(a, |x, y| x.cmp(&y)).collect_vec();
        let expected = make_perms();
        assert_eq!(expected, perms);
    }
}
