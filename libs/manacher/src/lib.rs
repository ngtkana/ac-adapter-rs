//! 文字列の全中心について最長回文の半径を線形時間で求める（Manacher's algorithm）。
//!
//! 中心ごとに愚直に回文を伸ばすと $O(n^2)$ かかるが、確定済みの回文の対称性を利用すると
//! 多くの中心で伸長処理を省略できる。中心 $i$ が既知の回文の内側にあれば、対称な中心の
//! 結果をそのまま折り返して使え、外側にはみ出す部分だけ愚直に文字比較すればよい。
//! この比較回数が amortized で定数回に抑えられるため、全体で $O(n)$ になる。
//!
//! # 仕様
//!
//! [`manacher`] が唯一の公開関数。文字列 $s$（長さ $n$）を受け取り、長さ $2n + 1$ の
//! 配列 $A$ を返す。
//!
//! $$
//! A_i = \max \left\{ r - l \;\middle|\; 0 \le l \le r \le n,\ l + r = i,\ s[l..r] \text{ は回文} \right\}
//! $$
//!
//! $i$ が偶数のとき中心は文字 $s_{i / 2}$ 上、奇数のとき文字と文字の間にある。
//!
//! # 例
//!
//! ```
//! use manacher::manacher;
//! let s = "mississippi";
//! let a = manacher(s.as_bytes());
//! assert_eq!(a, vec![
//!     0, 1, 0, 1, 0, 1, 4, 1, 0, 7, 0, 1, 4, 1, 0, 1, 0, 1, 4, 1, 0, 1, 0
//! ]);
//! ```
//!
//! # 計算量
//!
//! - [`manacher`][]: $O(n)$

/// 文字列 $s$ の全中心について、最長回文の半径を格納した配列を返す。
///
/// 中心ごとに愚直に伸ばすと $O(n^2)$ かかるが、確定済みの回文の対称性を利用して
/// 多くの中心の計算を省略し、$O(n)$ で求める。
///
/// # 仕様
///
/// $n = $ `s.len()` として、長さ $2n + 1$ の配列 $A$ を返す。
///
/// $$
/// A_i = \max \left\{ r - l \;\middle|\; 0 \le l \le r \le n,\ l + r = i,\ s[l..r] \text{ は回文} \right\}
/// $$
///
/// $i$ が偶数のとき中心は文字 $s_{i / 2}$ 上、奇数のとき文字と文字の間にある。
///
/// # 例
///
/// $s = $ "mississippi" のとき、中心 $i$ ごとの最長回文の半径 $A_i$ は次の通り
/// （`_` は文字と文字の間の中心）。
///
/// | $i$ | 中心 | $A_i$ | 対応する回文 |
/// | --- | --- | --- | --- |
/// | 0 | (前端) | 0 | |
/// | 1 | m | 1 | m |
/// | 2 | _ | 0 | |
/// | 3 | i | 1 | i |
/// | 4 | _ | 0 | |
/// | 5 | s | 1 | s |
/// | 6 | _ | 4 | issi |
/// | 7 | s | 1 | s |
/// | 8 | _ | 0 | |
/// | 9 | i | 7 | ississi |
/// | 10 | _ | 0 | |
///
/// ```
/// use manacher::manacher;
/// let s = "mississippi";
/// let a = manacher(s.as_bytes());
/// assert_eq!(a, vec![
///     0, 1, 0, 1, 0, 1, 4, 1, 0, 7, 0, 1, 4, 1, 0, 1, 0, 1, 4, 1, 0, 1, 0
/// ]);
/// ```
///
/// # 計算量
///
/// $O(n)$
pub fn manacher<T: Eq>(s: &[T]) -> Vec<usize> {
    let n = s.len();
    let mut a = vec![0; 2 * n + 1];
    let mut i = 1;
    let mut j = 1;
    while i <= 2 * n {
        while j < i && i + j < 2 * n && s[(i - j) / 2 - 1] == s[usize::midpoint(i, j)] {
            j += 2;
        }
        a[i] = j;
        if j == 0 {
            i += 1;
            j = 1;
            continue;
        }
        let mut k = 1;
        while k <= i && k + a[i - k] < j {
            a[i + k] = a[i - k];
            k += 1;
        }
        i += k;
        j -= k;
    }
    a
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[test]
    fn test_manacher() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..10);
            let s = (0..n).map(|_| rng.gen_range(0..4)).collect::<Vec<_>>();
            let result = manacher(&s);
            for (i, &result) in result.iter().enumerate() {
                let mut l = i / 2;
                let mut r = i - l;
                while 0 < l && r < n && s[l - 1] == s[r] {
                    l -= 1;
                    r += 1;
                }
                assert_eq!(result, r - l);
            }
        }
    }
}
