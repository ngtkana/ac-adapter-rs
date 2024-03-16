//! # Manacher's algorithm

/// Returns the palindrome array $A$ of the given string $s$.
///
/// # Definition
///
/// $A$ is an array of length $2n + 1$ where $n$ is the length of $s$.
///
/// $A_i = \max \left\\{
///     r - l \middle |
///     \begin{array}{l}
///         0 \le l \le r \le n, \ l + r = i, \\\\
///         s[l..r] \text{ is a palindrome}
///     \end{array}
/// \right\\}$.
///
/// # Example
///
/// If $s = \text{"mississippi"}$, then
/// $A = [0, 1, 0, 1, 0, 1, 4, 1, 0, 7, 0, 1, 4, 1, 0, 1, 0, 1, 4, 1, 0, 1, 0]$.
///
/// ```
/// # use manacher::manacher;
/// let s = "mississippi";
/// let a = manacher(s.as_bytes());
/// assert_eq!(a,, vec![0, 1, 0, 1, 0, 1, 4, 1, 0, 7, 0, 1, 4, 1, 0, 1, 0, 1, 4, 1, 0, 1, 0]);
/// ```
///
/// | $i$ | $s_{(i - 1) / 2}$ | $A_i$ | $s_{(i - A_i) / 2..(i + A_i) / 2}$ |
/// | --- | ------ | ------ | --------- |
/// | 0   |        | 0      |           |
/// | 1   | m      | 1      | m         |
/// | 2   |        | 0      |           |
/// | 3   | i      | 1      | i         |
/// | 4   |        | 0      |           |
/// | 5   | s      | 1      | s         |
/// | 6   |        | 4      | issi      |
/// | 7   | s      | 1      | s         |
/// | 8   |        | 0      |           |
/// | 9   | i      | 7      | ississi   |
/// | 10  |        | 0      |           |
/// | 11  | s      | 1      | s         |
/// | 12  |        | 4      | issi      |
/// | 13  | s      | 1      | s         |
/// | 14  |        | 0      |           |
/// | 15  | i      | 1      | i         |
/// | 16  |        | 0      |           |
/// | 17  | p      | 1      | p         |
/// | 18  |        | 4      | ippi      |
/// | 19  | p      | 1      | p         |
/// | 20  |        | 0      |           |
/// | 21  | i      | 1      | i         |
/// | 22  |        | 0      |           |
pub fn manacher<T: Eq + std::fmt::Debug>(s: &[T]) -> Vec<usize> {
    let n = s.len();
    let mut a = vec![0; 2 * n + 1];
    let mut i = 1;
    let mut j = 0;
    while i <= 2 * n {
        j += (i + j) % 2;
        while j < i && i + j < 2 * n && s[(i - j) / 2 - 1] == s[(i + j) / 2] {
            j += 2;
        }
        a[i] = j;
        if j == 0 {
            i += 1;
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
