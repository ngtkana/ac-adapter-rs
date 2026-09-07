//! インデックス依存の長さを持つ、skew な多次元 `Vec` を生成するマクロです。
//!
//! # Examples
//!
//! ```
//! use higher_vec::higher_vec;
//!
//! let n = 3;
//! let v = higher_vec![0, n, |i| n - i, |i, j| n - i - j];
//! assert_eq!(v, vec![
//!     vec![vec![0, 0, 0], vec![0, 0], vec![0]],
//!     vec![vec![0, 0], vec![0]],
//!     vec![vec![0]],
//! ]);
//! ```

/// skew な多次元 `Vec` を生成します。
///
/// # 構文
///
/// `higher_vec![init, len0, f1, ..., fk]`
///
/// - `init`: 末端要素の初期値（`Clone`）。1 度だけ評価され、各要素に `clone` されます
/// - `len0`: 最外次元（0 次元目）の長さ
/// - `f1, ..., fk`: 各次元の長さを決めるクロージャ。`fj` は外側 `j` 個のインデックス
///   `(i0, ..., i_{j-1})` を引数に取り、`j` 次元目の長さを `usize` で返す
///
/// クロージャを省略すると、`vec![init; len0]` と同じ 1 次元 `Vec` になります。
///
/// 依存関係が型では表現できない可変個・可変引数のクロージャ列を扱うため、
/// ネストしたループの組み立てはマクロが担い、各次元の長さ計算・要素の複製は
/// 通常の Rust の型（クロージャ・`Clone`）に委ねています。
///
/// # Examples
///
/// 1 次元（通常の `vec!` と同じ）:
///
/// ```
/// use higher_vec::higher_vec;
///
/// let v = higher_vec![0, 3];
/// assert_eq!(v, vec![0, 0, 0]);
/// ```
///
/// 2 次元（三角形）:
///
/// ```
/// use higher_vec::higher_vec;
///
/// let v = higher_vec![0, 3, |i| i + 1];
/// assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
/// ```
///
/// 3 次元（`i + j + k < n` を満たす形の skew な `Vec`）:
///
/// ```
/// use higher_vec::higher_vec;
///
/// let n = 3;
/// let v = higher_vec![0, n, |i| n - i, |i, j| n - i - j];
/// assert_eq!(v, vec![
///     vec![vec![0, 0, 0], vec![0, 0], vec![0]],
///     vec![vec![0, 0], vec![0]],
///     vec![vec![0]],
/// ]);
/// ```
#[macro_export]
macro_rules! higher_vec {
    ($init:expr, $len0:expr $(, $f:expr)* $(,)?) => {{
        let __higher_vec_init = $init;
        $crate::__higher_vec_body!(
            &__higher_vec_init;
            $len0;
            [];
            [__hv0, __hv1, __hv2, __hv3, __hv4, __hv5, __hv6, __hv7];
            $($f),*
        )
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __higher_vec_body {
    ($init:expr; $len:expr; [$($acc:ident),*]; [$($pool:ident),*]; ) => {{
        let __hv_len: usize = $len;
        ::std::vec![::std::clone::Clone::clone($init); __hv_len]
    }};
    ($init:expr; $len:expr; [$($acc:ident),*]; [$pool_head:ident $(, $pool_tail:ident)*]; $head:expr $(, $tail:expr)*) => {{
        let __hv_len: usize = $len;
        (0..__hv_len)
            .map(|$pool_head| {
                let __hv_next_len: usize = ($head)($($acc,)* $pool_head);
                $crate::__higher_vec_body!(
                    $init;
                    __hv_next_len;
                    [$($acc,)* $pool_head];
                    [$($pool_tail),*];
                    $($tail),*
                )
            })
            .collect::<::std::vec::Vec<_>>()
    }};
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_1d() {
        let v = higher_vec![0, 3];
        assert_eq!(v, vec![0, 0, 0]);
    }

    #[test]
    fn test_1d_empty() {
        let v: Vec<i32> = higher_vec![0, 0];
        assert_eq!(v, Vec::<i32>::new());
    }

    #[test]
    fn test_2d_triangular() {
        let v = higher_vec![0, 3, |i| i + 1];
        assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
    }

    #[test]
    fn test_3d_skew() {
        let n = 3;
        let v = higher_vec![0, n, |i| n - i, |i, j| n - i - j];
        assert_eq!(v, vec![
            vec![vec![0, 0, 0], vec![0, 0], vec![0]],
            vec![vec![0, 0], vec![0]],
            vec![vec![0]],
        ]);
    }

    #[test]
    fn test_init_evaluated_once() {
        use std::cell::Cell;
        let calls = Cell::new(0);
        let make = || {
            calls.set(calls.get() + 1);
            0
        };
        let v = higher_vec![make(), 3, |i| i + 1];
        assert_eq!(calls.get(), 1);
        assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
    }

    #[test]
    fn test_non_copy_init() {
        let v = higher_vec![String::from("x"), 2, |i| i + 1];
        assert_eq!(v, vec![vec!["x".to_string()], vec!["x".into(), "x".into()]]);
    }

    #[test]
    fn test_trailing_comma() {
        let v = higher_vec![0, 3, |i| i + 1,];
        assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
    }
}
