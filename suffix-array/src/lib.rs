#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! Suffix Array を計算します。

/// Surrix Array を計算します。
///
/// # Examples
///
/// ```
/// use suffix_array::suffix_array;
/// let s = "abracadabra";
/// let sa = suffix_array(s.as_bytes());
/// assert_eq!(sa, vec![10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
/// ```
///
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

#[cfg(test)]
mod tests {
    use super::*;

    fn brute<T: Ord>(s: &[T]) -> Vec<usize> {
        let mut ord: Vec<_> = (0..s.len()).collect();
        ord.sort_by_key(|&i| &s[i..]);
        ord
    }

    fn check_str(s: &str) {
        assert_eq!(suffix_array(s.as_bytes()), brute(s.as_bytes()));
    }

    #[test]
    fn test() {
        check_str("abracadabra");
        check_str("ababaababa");
        check_str("ngtkana");
        check_str("nagatakana");
        check_str("a");
        check_str("");
        check_str("aaaa");
    }

    #[test]
    fn test_yosupo_judge_sample() {
        check_str("abcbcba");
        check_str("mississippi");
        check_str("ababacaca");
        check_str("aaaaa");
    }
}
