//! 多重 for 文の代わりに、skew な多次元インデックスの列を遅延イテレータとして列挙するマクロ。
//!
//! 内側の次元の長さが外側のインデックスに依存する場合（例：$i + j + k < n$ を満たす
//! $(i, j, k)$ の列挙）でも、ネストした for 文を手書きせずに `Iterator` として扱える。
//! 各次元の長さはクロージャで指定し、`flat_map` を入れ子に展開することで、
//! 手書きの多重 for 文と同じ順序・同じ列を生成する。[`jagged_vec!`](https://docs.rs/jagged_vec)
//! と同じクロージャ列の構文を採用した姉妹クレート。
//!
//! # 仕様
//!
//! - [`jagged_iproduct!`]：マクロ本体。構文・意味論は同マクロのドキュメント参照
//!
//! # 例
//!
//! ```
//! use jagged_iproduct::jagged_iproduct;
//!
//! let n = 3;
//! let v = jagged_iproduct![n, |i| n - i, |i, j| n - i - j].collect::<Vec<_>>();
//! assert_eq!(v, vec![
//!     [0, 0, 0], [0, 0, 1], [0, 0, 2],
//!     [0, 1, 0], [0, 1, 1],
//!     [0, 2, 0],
//!     [1, 0, 0], [1, 0, 1],
//!     [1, 1, 0],
//!     [2, 0, 0],
//! ]);
//! ```
//!
//! # 計算量
//!
//! - 要素の生成：1 要素あたり $O(1)$ ならし

/// skew な多次元インデックスの列を、多重 for 文の代わりに列挙する。
///
/// 各次元の長さを決めるクロージャ $f_1, \ldots, f_k$ をそのまま引数に並べる。
/// `fj` は外側 $j$ 個のインデックス $(i_0, \ldots, i_{j-1})$ を引数に取り、$j$ 次元目の
/// 長さを返す。展開後は `flat_map` の $k$ 重の入れ子になり、次のネストした for 文と
/// 同じ順序で同じ列を、生成した要素 1 個あたり $O(1)$ ならし時間で列挙する。
///
/// ```text
/// for i0 in 0..len0 {
///     for i1 in 0..f1(i0) {
///         ...
///             for ik in 0..fk(i0, ..., i_{k-1}) {
///                 yield [i0, i1, ..., ik];
///             }
///     }
/// }
/// ```
///
/// # 仕様
///
/// `jagged_iproduct![len0, f1, ..., fk]`
///
/// - `len0`：最外次元（0 次元目）の長さ
/// - `f1, ..., fk`：各次元の長さを決めるクロージャ。省略すると `0..len0` と同じ
///   1 次元のイテレータになる
/// - 返り値：`[usize; D]`（`D` はマクロの引数の個数）を生成する遅延イテレータ
///
/// # 例
///
/// 1 次元（`0..len0` と同じ）：
///
/// ```
/// use jagged_iproduct::jagged_iproduct;
///
/// let v = jagged_iproduct![3].collect::<Vec<_>>();
/// assert_eq!(v, vec![[0], [1], [2]]);
/// ```
///
/// 2 次元（三角形、$0 \le i_1 \le i_0$）：
///
/// ```
/// use jagged_iproduct::jagged_iproduct;
///
/// let v = jagged_iproduct![3, |i| i + 1].collect::<Vec<_>>();
/// assert_eq!(v, vec![[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [2, 2]]);
/// ```
///
/// 3 次元（$i_0 + i_1 + i_2 < n$ を満たす skew な列。三重 for 文の代わりに使える）：
///
/// ```
/// use jagged_iproduct::jagged_iproduct;
///
/// let n = 3;
/// let v = jagged_iproduct![n, |i| n - i, |i, j| n - i - j].collect::<Vec<_>>();
/// assert_eq!(v, vec![
///     [0, 0, 0], [0, 0, 1], [0, 0, 2],
///     [0, 1, 0], [0, 1, 1],
///     [0, 2, 0],
///     [1, 0, 0], [1, 0, 1],
///     [1, 1, 0],
///     [2, 0, 0],
/// ]);
/// ```
///
/// # 計算量
///
/// 要素の生成：1 要素あたり $O(1)$ ならし
#[macro_export]
macro_rules! jagged_iproduct {
    ($len0:expr $(, $f:expr)* $(,)?) => {{
        $crate::__jagged_iproduct_body!(
            $len0;
            [];
            [__hip0, __hip1, __hip2, __hip3, __hip4, __hip5, __hip6, __hip7];
            $($f),*
        )
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __jagged_iproduct_body {
    ($len:expr; [$($acc:ident),*]; [$($pool:ident),*]; ) => {{
        let __hip_len: usize = $len;
        (0..__hip_len).map(move |__hip_last| [$($acc,)* __hip_last])
    }};
    ($len:expr; [$($acc:ident),*]; [$pool_head:ident $(, $pool_tail:ident)*]; $head:expr $(, $tail:expr)*) => {{
        let __hip_len: usize = $len;
        (0..__hip_len).flat_map(move |$pool_head| {
            let __hip_next_len: usize = ($head)($($acc,)* $pool_head);
            $crate::__jagged_iproduct_body!(
                __hip_next_len;
                [$($acc,)* $pool_head];
                [$($pool_tail),*];
                $($tail),*
            )
        })
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_1d() {
        let v = jagged_iproduct![3].collect::<Vec<_>>();
        assert_eq!(v, vec![[0], [1], [2]]);
    }

    #[test]
    fn test_1d_empty() {
        let v = jagged_iproduct![0].collect::<Vec<_>>();
        assert_eq!(v, Vec::<[usize; 1]>::new());
    }

    #[test]
    fn test_2d_triangular() {
        let v = jagged_iproduct![3, |i| i + 1].collect::<Vec<_>>();
        assert_eq!(v, vec![[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [2, 2]]);
    }

    #[test]
    fn test_3d_skew() {
        let n = 3;
        let v = jagged_iproduct![n, |i| n - i, |i, j| n - i - j].collect::<Vec<_>>();
        assert_eq!(
            v,
            vec![
                [0, 0, 0],
                [0, 0, 1],
                [0, 0, 2],
                [0, 1, 0],
                [0, 1, 1],
                [0, 2, 0],
                [1, 0, 0],
                [1, 0, 1],
                [1, 1, 0],
                [2, 0, 0],
            ]
        );
    }

    #[test]
    fn test_trailing_comma() {
        let v = jagged_iproduct![3, |i| i + 1,].collect::<Vec<_>>();
        assert_eq!(v, vec![[0, 0], [1, 0], [1, 1], [2, 0], [2, 1], [2, 2]]);
    }

    #[test]
    fn test_matches_manual_nested_for_loop() {
        let pos = 4;
        let mut expected = Vec::new();
        for i in 0..=pos {
            for j in 0..=pos - i {
                for k in 0..=pos - i - j {
                    expected.push([i, j, k]);
                }
            }
        }
        let actual =
            jagged_iproduct![pos + 1, |i| pos + 1 - i, |i, j| pos + 1 - i - j].collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_matches_itertools_iproduct_when_rectangular() {
        use itertools::iproduct;
        let (n, m, l) = (3, 4, 2);
        let expected = iproduct!(0..n, 0..m, 0..l)
            .map(|(i, j, k)| [i, j, k])
            .collect::<Vec<_>>();
        let actual = jagged_iproduct![n, |_| m, |_, _| l].collect::<Vec<_>>();
        assert_eq!(actual, expected);
    }
}
