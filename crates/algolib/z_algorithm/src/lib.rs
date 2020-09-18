use std::cmp;

/// Z-アルゴリズムをします。
///
/// # 戻り値
///
/// `s` と `s[i..]` の最長共通部分列の長さ `z[i]` を並べた長さ `n` の配列 `z` を返します。
pub fn z_algorithm<T: Ord>(s: &[T]) -> Vec<usize> {
    let n = s.len();
    if n == 0 {
        Vec::new()
    } else {
        let mut z = vec![0; n];
        let mut j = 0;
        for i in 1..n {
            z[i] = (if j + z[j] <= i {
                0
            } else {
                cmp::min(j + z[j] - i, z[i - j])
            }..)
                .find(|&k| i + k == n || s[k] != s[i + k])
                .unwrap();
            if j + z[j] < i + z[i] {
                j = i;
            }
        }
        z[0] = n;
        z
    }
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

    #[test_case("abcabca")]
    #[test_case("abracadabra")]
    #[test_case("mississippi")]
    fn test_hand(s: &str) {
        let expected = z_brute(s.as_bytes());
        let result = z_algorithm(s.as_bytes());
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

            let expected = z_brute(s.as_bytes());
            let result = z_algorithm(s.as_bytes());
            assert_eq!(expected, result);
        }
    }
}
