//! 文字列と各接尾辞との最長共通接頭辞長を線形時間で求める Z algorithm。
//!
//! 既知の一致区間（過去に見つけた $[l, r)$ で `s[l..r]` が `s` の接頭辞と一致）を使い回すことで、
//! 各添字での比較開始位置を後戻りさせずに済ませ、全体の比較回数を $O(n)$ に抑える。
//! 具体的には、区間内にある添字 $i$ の $z_i$ は「区間内で対応する接頭辞の値」と
//! 「区間の残り長さ」の小さい方まではコピーで確定でき、一致するかもしれない残りだけを
//! 実際に文字比較して区間を更新する。
//!
//! # 仕様
//!
//! [`z_algo`]`(s)` は長さ $n$ の列 `s` に対し、長さ $n$ の Z 配列 `z` を返す。
//! `z[i]` は `s` と `s[i..]` の最長共通接頭辞の長さ（$z_0 = n$）。
//!
//! # 例
//!
//! ```
//! use z_algo::z_algo;
//! let z = z_algo("abcabca".as_bytes());
//! assert_eq!(z, vec![7, 0, 0, 4, 0, 0, 1]);
//! ```
//!
//! # 計算量
//!
//! - [`z_algo`][]: $O(n)$

/// 長さ $n$ の列 `s` の Z 配列を計算する。仕様は [crate レベルドキュメント](self) を参照。
///
/// # 例
///
/// ```
/// use z_algo::z_algo;
/// let z = z_algo("aaa".as_bytes());
/// assert_eq!(z, vec![3, 2, 1]); // z[1] = "aa" と "aaa" の共通接頭辞長
/// ```
///
/// # 計算量
///
/// $O(n)$
pub fn z_algo<T: Eq>(s: &[T]) -> Vec<usize> {
    if s.is_empty() {
        return Vec::new();
    }
    let n = s.len();
    let mut z = vec![0; n];
    z[0] = n;
    let mut left = 1;
    let mut right = left;
    while left < n {
        while right < n && s[right - left] == s[right] {
            right += 1;
        }
        z[left] = right - left;
        if left == right {
            left += 1;
            right += 1;
            continue;
        }
        let mut next = left + 1;
        while next < n && next + z[next - left] < right {
            z[next] = z[next - left];
            next += 1;
        }
        left = next;
    }
    z
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use std::iter;
    use test_case::test_case;

    fn z_brute<T: Ord>(s: &[T]) -> Vec<usize> {
        let n = s.len();
        (0..n)
            .map(|i| {
                s.iter()
                    .zip(s[i..].iter())
                    .take_while(|&(c, d)| c == d)
                    .count()
            })
            .collect()
    }

    #[allow(clippy::unused_unit)]
    #[test_case("abcabca")]
    #[test_case("abracadabra")]
    #[test_case("mississippi")]
    fn test_hand(s: &str) {
        let expected = z_brute(s.as_bytes());
        let result = z_algo(s.as_bytes());
        assert_eq!(expected, result);
    }

    #[test]
    fn test_random() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(10..40);
            let s = iter::repeat_with(|| rng.sample(rand::distributions::Alphanumeric))
                .map(|c| c as char)
                .take(n)
                .collect::<String>();
            println!("s = {s}");

            let expected = z_brute(s.as_bytes());
            let result = z_algo(s.as_bytes());
            assert_eq!(expected, result);
        }
    }
}
