/// Z-algorithm
///
/// # Parameters
///
/// * `a`: An array to test
///
/// # Returns
///
/// The Z-array `z` of `a`.
/// `z[i]` is the length of longest common prefix of `a` and `a[i..]`.
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
            println!("s = {}", s);

            let expected = z_brute(s.as_bytes());
            let result = z_algo(s.as_bytes());
            assert_eq!(expected, result);
        }
    }
}
