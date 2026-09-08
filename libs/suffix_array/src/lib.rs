//! 接尾辞配列 (Suffix Array) と LCP 配列を計算する。
//!
//! 接尾辞配列は文字列の全接尾辞を辞書順に並べたときの開始位置の列であり、
//! 文字列検索・最長共通部分文字列などの土台になるデータ構造。
//! [`suffix_array`] は倍加法（prefix doubling）で構築する：長さ $d$ の接頭辞に基づく
//! 順位を保ったまま $d = 1, 2, 4, \ldots$ と倍加させ、各段階でバケットソートにより
//! 長さ $2d$ の接頭辞での順位に更新する。
//! [`lcp_array`] は接尾辞配列上で隣接する接尾辞どうしの最長共通接頭辞の長さを、
//! Kasai のアルゴリズムにより $O(n)$ で計算する。
//!
//! # 仕様
//!
//! - [`suffix_array`][]: 長さ $n$ の列 `s` に対し、`s[sa[0]..], s[sa[1]..], ..., s[sa[n-1]..]`
//!   が辞書順に並ぶような添字列 `sa` を返す
//! - [`lcp_array`][]: `sa` に対し、`s[sa[i]..]` と `s[sa[i+1]..]` の最長共通接頭辞の長さを
//!   並べた長さ $n - 1$ の列を返す
//!
//! # 例
//!
//! ```
//! use suffix_array::lcp_array;
//! use suffix_array::suffix_array;
//! let s = "abracadabra";
//! let sa = suffix_array(s.as_bytes());
//! assert_eq!(sa, vec![10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
//! let lcp = lcp_array(s.as_bytes(), &sa);
//! assert_eq!(lcp, vec![1, 4, 1, 1, 0, 3, 0, 0, 0, 2]);
//! ```
//!
//! # 計算量
//!
//! - [`suffix_array`][]: $O(n \log n)$
//! - [`lcp_array`][]: $O(n)$

/// 接尾辞配列を構築する。
///
/// 長さ $d$ の接頭辞に基づく順位を保ちながら $d = 1, 2, 4, \ldots$ と倍加させる
/// 倍加法で構築する。各段階で $(\mathrm{rank}_i, \mathrm{rank}_{i+d})$ をキーに
/// バケットソートし直すことで、`s[i..]` どうしの辞書順比較を長さ $2d$ の
/// 接頭辞の比較に帰着させる。
///
/// # 仕様
///
/// `s[sa[0]..], s[sa[1]..], ..., s[sa[n-1]..]` が辞書順に並ぶような添字列 `sa` を返す。
///
/// # 例
///
/// ```
/// use suffix_array::suffix_array;
/// let s = "abracadabra";
/// let sa = suffix_array(s.as_bytes());
/// assert_eq!(sa, vec![10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
/// ```
///
/// # 計算量
///
/// $O(n \log n)$
pub fn suffix_array<T: Ord>(s: &[T]) -> Vec<usize> {
    let n = s.len();
    let mut ord: Vec<usize> = (0..n).collect();
    ord.sort_by_key(|&i| &s[i]);
    let mut cmp = vec![0; n];
    for i in 1..n {
        cmp[i] = if s[ord[i - 1]] == s[ord[i]] { cmp[i - 1] } else { cmp[i - 1] + 1 };
    }
    for d in std::iter::successors(Some(1), |x| Some(x * 2)).take_while(|&x| x <= n) {
        let mut ord_inverse = vec![0; n];
        (0..n).for_each(|i| ord_inverse[ord[i]] = i);
        let cmp_count = *cmp.last().unwrap() + 1;
        let mut pos = vec![0; cmp_count];
        for (i, &c) in cmp.iter().enumerate().rev() {
            pos[c] = i;
        }

        let mut ord_swp = vec![0; n];
        let mut insert = |i| {
            let c = cmp[ord_inverse[i]];
            ord_swp[pos[c]] = i;
            pos[c] += 1;
        };
        (n - d..n).for_each(&mut insert);
        ord.iter()
            .filter(|&&i| d <= i)
            .map(|i| i - d)
            .for_each(insert);

        let mut cmp_swp = vec![0; n];
        for i in 1..n {
            let l = ord_swp[i - 1];
            let r = ord_swp[i];
            cmp_swp[i] = if cmp[ord_inverse[l]] == cmp[ord_inverse[r]]
                && ord_inverse.get(l + d).map_or(n, |&ld| cmp[ld])
                    == ord_inverse.get(r + d).map_or(n, |&rd| cmp[rd])
            {
                cmp_swp[i - 1]
            } else {
                cmp_swp[i - 1] + 1
            };
        }

        ord = ord_swp;
        cmp = cmp_swp;
    }
    ord
}

/// LCP 配列を構築する。
///
/// 接尾辞配列上を辞書順に走査しながら、直前に処理した接尾辞との共通接頭辞長を
/// 使い回す Kasai のアルゴリズムにより、各文字の比較回数を償却定数回に抑えて
/// $O(n)$ で計算する。
///
/// # 仕様
///
/// 接尾辞配列 `sa`（[`suffix_array`] の出力）に対し、`s[sa[i]..]` と `s[sa[i+1]..]`
/// の最長共通接頭辞の長さを `lcp[i]` とする長さ $n - 1$ の列を返す。
///
/// # 例
///
/// ```
/// use suffix_array::lcp_array;
/// use suffix_array::suffix_array;
/// let s = "abracadabra";
/// let sa = suffix_array(s.as_bytes());
/// let lcp = lcp_array(s.as_bytes(), &sa);
/// assert_eq!(lcp, vec![1, 4, 1, 1, 0, 3, 0, 0, 0, 2]);
/// ```
///
/// # 計算量
///
/// $O(n)$
pub fn lcp_array<T: Ord>(s: &[T], sa: &[usize]) -> Vec<usize> {
    assert_eq!(s.len(), sa.len());
    assert!(!s.is_empty());
    assert!(!sa.is_empty());

    let n = s.len();
    let rnk = make_rank(sa);
    let mut h = 0_usize;
    let mut lcp = vec![0; n - 1];
    for (i, &r) in rnk.iter().enumerate() {
        h = h.saturating_sub(1);
        if r != 0 {
            let j = sa[r - 1];
            h = s[i..]
                .iter()
                .zip(&s[j..])
                .position(|(c, d)| c != d)
                .unwrap_or_else(|| s[i..].len().min(s[j..].len()));
            lcp[r - 1] = h;
        }
    }
    lcp
}

fn make_rank(a: &[usize]) -> Vec<usize> {
    let n = a.len();
    let mut b = vec![n; n];
    for (i, &x) in a.iter().enumerate() {
        assert_eq!(b[x], n);
        b[x] = i;
    }
    b
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use std::iter;
    use test_case::test_case;

    fn sa_brute<T: Ord>(s: &[T]) -> Vec<usize> {
        let mut ord: Vec<_> = (0..s.len()).collect();
        ord.sort_by_key(|&i| &s[i..]);
        ord
    }

    fn lcp_brute<T: Ord>(s: &[T], sa: &[usize]) -> Vec<usize> {
        let n = s.len();
        (0..n - 1)
            .map(|i| {
                s[sa[i]..]
                    .iter()
                    .zip(s[sa[i + 1]..].iter())
                    .take_while(|&(c, d)| c == d)
                    .count()
            })
            .collect()
    }

    #[allow(clippy::unused_unit)]
    #[test_case("abcbcba"; "yosupo 1")]
    #[test_case("mississippi"; "yosupo 2")]
    #[test_case("ababacaca"; "yosupo 3")]
    #[test_case("aaaaa"; "yosupo 4")]
    fn test_hand(s: &str) {
        let expected = sa_brute(s.as_bytes());
        let result = suffix_array(s.as_bytes());
        assert_eq!(expected, result);

        let expected = lcp_brute(s.as_bytes(), &expected);
        let result = lcp_array(s.as_bytes(), &result);
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

            let expected = sa_brute(s.as_bytes());
            let result = suffix_array(s.as_bytes());
            assert_eq!(expected, result);

            let expected = lcp_brute(s.as_bytes(), &expected);
            let result = lcp_array(s.as_bytes(), &result);
            assert_eq!(expected, result);
        }
    }
}
