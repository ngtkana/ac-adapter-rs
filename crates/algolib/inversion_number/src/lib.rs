//! Calculates the number of inversions.
//!
//! [See the document of `inversion_number](inversion_number)
//!

/// Takes a sequence of numbers in `0..value_limit` and returns the number of (strong) inversions.
///
/// A strong inversion is a pair `i < j` satisfying `a[i] > a[j]`.
///
/// # Examples
///
/// Basic usage:
/// ```
/// use inversion_number::inversion_number;
///
/// assert_eq!(inversion_number(4, &[2, 1, 3, 0]), 4);
/// assert_eq!(inversion_number(4, &[2, 3, 2, 2]), 2);
/// ```
///
pub fn inversion_number(value_limit: usize, a: &[usize]) -> u64 {
    let mut inv = 0_u64;
    let mut used = vec![0; value_limit + 1];
    for (i, &x) in a.iter().enumerate() {
        inv += i as u64;
        {
            let mut x = x + 1;
            while x != 0 {
                inv -= used[x];
                x -= x & x.wrapping_neg();
            }
        }
        {
            let mut x = x + 1;
            while x <= value_limit {
                used[x] += 1;
                x += x & x.wrapping_neg();
            }
        }
    }
    inv
}

#[cfg(test)]
mod tests {
    use {super::inversion_number, test_case::test_case};

    #[test_case(3, &[0, 1, 2] => 0)]
    #[test_case(3, &[0, 2, 1] => 1)]
    #[test_case(3, &[1, 0, 2] => 1)]
    #[test_case(3, &[1, 2, 0] => 2)]
    #[test_case(3, &[2, 0, 1] => 2)]
    #[test_case(3, &[2, 1, 0] => 3)]
    fn test_hand(n: usize, a: &[usize]) -> u64 {
        inversion_number(n, &a)
    }
}
