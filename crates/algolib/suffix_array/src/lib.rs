#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! Suffix Array を計算します。

/// Surrix Array を計算します。
///
/// TODO: 実装を短くできるような気がします。
///
/// # Examples
///
/// ```
/// use suffix_array::suffix_array;
/// let s = "abracadabra";
/// let sa = suffix_array(s.as_bytes());
/// assert_eq!(sa, vec![10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
/// ```
pub fn suffix_array<T: Ord>(s: &[T]) -> Vec<usize> {
    let n = s.len();
    let mut ord: Vec<usize> = (0..n).collect();
    ord.sort_by_key(|&i| &s[i]);
    let mut cmp = vec![0; n];
    for i in 1..n {
        cmp[i] = if s[ord[i - 1]] == s[ord[i]] {
            cmp[i - 1]
        } else {
            cmp[i - 1] + 1
        };
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
            cmp_swp[i] = if (
                cmp[ord_inverse[l]],
                ord_inverse.get(l + d).map(|&ld| cmp[ld]).unwrap_or(n),
            ) == (
                cmp[ord_inverse[r]],
                ord_inverse.get(r + d).map(|&rd| cmp[rd]).unwrap_or(n),
            ) {
                cmp_swp[i - 1]
            } else {
                cmp_swp[i - 1] + 1
            }
        }

        ord = ord_swp;
        cmp = cmp_swp;
    }
    ord
}

/// LCP 配列を計算します。
///
/// # 戻り値
///
/// `s[sa[i]..]` と `s[sa[i + 1]..]` の最小共通部分列のの長さ `lcp[i]` を並べた、長さ `n - 1`
/// の配列 `lcp` を返します。
pub fn lcp_array<T: Ord>(s: &[T], sa: &[usize]) -> Vec<usize> {
    assert_eq!(s.len(), sa.len());
    assert!(!s.is_empty());
    assert!(!sa.is_empty());

    let n = s.len();
    let rnk = make_rank(&sa);
    let mut h = 0usize;
    let mut lcp = vec![0; n - 1];
    for (i, &r) in rnk.iter().enumerate() {
        h = h.saturating_sub(1);
        if r != 0 {
            let j = sa[r - 1];
            h = (h..)
                .find(|&h| j + h == n || i + h == n || s[j + h] != s[i + h])
                .unwrap();
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
            let n = rng.gen_range(10, 40);
            let s = iter::repeat_with(|| rng.sample(rand::distributions::Alphanumeric))
                .take(n)
                .collect::<String>();
            println!("s = {}", s);

            let expected = sa_brute(s.as_bytes());
            let result = suffix_array(s.as_bytes());
            assert_eq!(expected, result);

            let expected = lcp_brute(s.as_bytes(), &expected);
            let result = lcp_array(s.as_bytes(), &result);
            assert_eq!(expected, result);
        }
    }
}
