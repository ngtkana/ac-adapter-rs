use super::Unsigned;

/// Returns an iterator over k-subsets of `(T::one() << n) - T::one()`.
///
/// # Examples
///
/// Basic usage:
/// ```
/// use bitset::combinations;
///
/// assert_eq!(
///     combinations::<u32>(3, 2).collect::<Vec<_>>(),
///     vec![3, 5, 6],
/// );
/// ```
pub fn combinations<T: Unsigned>(n: u32, k: u32) -> Combinations<T> {
    assert!(k < T::bit_length() && k < T::bit_length());
    Combinations {
        n,
        bs: (T::one() << k) - T::one(),
    }
}

/// [See the document of `combinations`](combinations)
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Combinations<T> {
    n: u32,
    bs: T,
}
impl<T: Unsigned> Iterator for Combinations<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if (T::one() << self.n) <= self.bs {
            return None;
        }
        let res = Some(self.bs);
        self.bs = if self.bs == T::zero() {
            T::one() << self.n
        } else {
            let x = self.bs & self.bs.wrapping_neg();
            let y = self.bs + x;
            (((self.bs & !y) / x) >> 1) | y
        };
        res
    }
}

#[cfg(test)]
mod tests {
    use {super::combinations, itertools::Itertools, test_case::test_case};

    #[test_case(0, 0 => vec![0])]
    #[test_case(1, 0 => vec![0])]
    #[test_case(1, 1 => vec![1])]
    #[test_case(2, 0 => vec![0])]
    #[test_case(2, 1 => vec![1, 2])]
    #[test_case(2, 2 => vec![3])]
    #[test_case(3, 0 => vec![0])]
    #[test_case(3, 1 => vec![1, 2, 4])]
    #[test_case(3, 2 => vec![3, 5, 6])]
    #[test_case(3, 3 => vec![7])]
    fn test_combinations(n: u32, k: u32) -> Vec<u32> {
        combinations(n, k).collect_vec()
    }
}
