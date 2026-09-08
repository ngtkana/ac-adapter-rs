//! 各次元の長さが外側の添字に依存する、ジャグ配列（skew な多次元 `Vec`）を生成する。
//!
//! ジャグ配列の次元数は静的に決まるが各次元の長さは値に依存するため、型だけでは
//! ループ構造を表現できない。マクロがネストしたループの組み立てを引き受け、
//! 各次元の長さ計算・末端要素の複製は通常の Rust の値（クロージャ・`Clone`）に委ねる。
//!
//! # 仕様
//!
//! [`jagged_vec!`] のみを公開する。
//!
//! # 例
//!
//! ```
//! use jagged_vec::jagged_vec;
//!
//! let n = 3;
//! let v = jagged_vec![0, n, |i| n - i, |i, j| n - i - j];
//! assert_eq!(v, vec![
//!     vec![vec![0, 0, 0], vec![0, 0], vec![0]],
//!     vec![vec![0, 0], vec![0]],
//!     vec![vec![0]],
//! ]);
//! ```
//!
//! # 計算量
//!
//! - 生成: 生成される要素数の総和を $M$ として $O(M)$

/// ジャグ配列（skew な多次元 `Vec`）を生成する。
///
/// `jagged_vec![init, len0, f1, ..., fk]` の形で呼び出す。`init` は末端要素の初期値
/// （`Clone` 制約）で 1 度だけ評価され、各要素に複製される。`len0` は 0 次元目の長さ。
/// $j$ 番目のクロージャ $f_j$ は外側の添字 $(i_0, \ldots, i_{j-1})$ を引数に取り、
/// $j$ 次元目の長さを `usize` で返す。クロージャをすべて省略すると
/// `vec![init; len0]` と同じ 1 次元 `Vec` になる。
///
/// # 例
///
/// 1 次元（`vec!` と同じ）:
///
/// ```
/// use jagged_vec::jagged_vec;
///
/// let v = jagged_vec![0, 3];
/// assert_eq!(v, vec![0, 0, 0]);
/// ```
///
/// 2 次元（三角形。$i$ 行目の長さが $i + 1$）:
///
/// ```
/// use jagged_vec::jagged_vec;
///
/// let v = jagged_vec![0, 3, |i| i + 1];
/// assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
/// ```
///
/// 3 次元（$i + j + k < n$ を満たす形の skew な `Vec`）:
///
/// ```
/// use jagged_vec::jagged_vec;
///
/// let n = 3;
/// let v = jagged_vec![0, n, |i| n - i, |i, j| n - i - j];
/// assert_eq!(v, vec![
///     vec![vec![0, 0, 0], vec![0, 0], vec![0]],
///     vec![vec![0, 0], vec![0]],
///     vec![vec![0]],
/// ]);
/// ```
///
/// # 計算量
///
/// 生成される要素数の総和を $M$ として $O(M)$
#[macro_export]
macro_rules! jagged_vec {
    ($init:expr, $len0:expr $(, $f:expr)* $(,)?) => {{
        let __jagged_vec_init = $init;
        $crate::__jagged_vec_body!(
            &__jagged_vec_init;
            $len0;
            [];
            [__jv0, __jv1, __jv2, __jv3, __jv4, __jv5, __jv6, __jv7];
            $($f),*
        )
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __jagged_vec_body {
    ($init:expr; $len:expr; [$($acc:ident),*]; [$($pool:ident),*]; ) => {{
        let __jv_len: usize = $len;
        ::std::vec![::std::clone::Clone::clone($init); __jv_len]
    }};
    ($init:expr; $len:expr; [$($acc:ident),*]; [$pool_head:ident $(, $pool_tail:ident)*]; $head:expr $(, $tail:expr)*) => {{
        let __jv_len: usize = $len;
        (0..__jv_len)
            .map(|$pool_head| {
                let __jv_next_len: usize = ($head)($($acc,)* $pool_head);
                $crate::__jagged_vec_body!(
                    $init;
                    __jv_next_len;
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
        let v = jagged_vec![0, 3];
        assert_eq!(v, vec![0, 0, 0]);
    }

    #[test]
    fn test_1d_empty() {
        let v: Vec<i32> = jagged_vec![0, 0];
        assert_eq!(v, Vec::<i32>::new());
    }

    #[test]
    fn test_2d_triangular() {
        let v = jagged_vec![0, 3, |i| i + 1];
        assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
    }

    #[test]
    fn test_3d_skew() {
        let n = 3;
        let v = jagged_vec![0, n, |i| n - i, |i, j| n - i - j];
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
        let v = jagged_vec![make(), 3, |i| i + 1];
        assert_eq!(calls.get(), 1);
        assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
    }

    #[test]
    fn test_non_copy_init() {
        let v = jagged_vec![String::from("x"), 2, |i| i + 1];
        assert_eq!(v, vec![vec!["x".to_string()], vec!["x".into(), "x".into()]]);
    }

    #[test]
    fn test_trailing_comma() {
        let v = jagged_vec![0, 3, |i| i + 1,];
        assert_eq!(v, vec![vec![0], vec![0, 0], vec![0, 0, 0]]);
    }
}
