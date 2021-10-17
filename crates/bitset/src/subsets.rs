use super::Unsigned;

/// Returns an iterator over subsets of `bs`.
///
/// # Examples
///
/// Basic usage:
/// ```
/// use bitset::subsets;
///
/// assert_eq!(
///     subsets(10u32).collect::<Vec<_>>(),
///     vec![0, 2, 8, 10],
/// );
/// ```
pub fn subsets<T: Unsigned>(bs: T) -> Subsets<T> {
    Subsets {
        bs,
        full: bs,
        finished: false,
    }
}

/// [See the document of `subsets`](subsets)
#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Subsets<T> {
    bs: T,
    full: T,
    finished: bool,
}
impl<T: Unsigned> Iterator for Subsets<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let res = Some(self.bs ^ self.full);
        if self.bs == T::zero() {
            self.finished = true;
        } else {
            self.bs -= T::one();
            self.bs &= self.full;
        }
        res
    }
}

#[cfg(test)]
mod tests {
    use {super::subsets, itertools::Itertools, test_case::test_case};

    #[test_case(0 => vec![0])]
    #[test_case(1 => vec![0, 1])]
    #[test_case(2 => vec![0, 2])]
    #[test_case(3 => vec![0, 1, 2, 3])]
    #[test_case(4 => vec![0, 4])]
    #[test_case(5 => vec![0, 1, 4, 5])]
    #[test_case(6 => vec![0, 2, 4, 6])]
    #[test_case(7 => vec![0, 1, 2, 3, 4, 5, 6, 7])]
    #[test_case(8 => vec![0, 8])]
    #[test_case(9 => vec![0, 1, 8, 9])]
    #[test_case(10 => vec![0, 2, 8, 10])]
    #[test_case(11 => vec![0, 1, 2, 3, 8, 9, 10, 11])]
    #[test_case(12 => vec![0, 4, 8, 12])]
    #[test_case(13 => vec![0, 1, 4, 5, 8, 9, 12, 13])]
    #[test_case(14 => vec![0, 2, 4, 6, 8, 10, 12, 14])]
    #[test_case(15 => vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15])]
    fn test_subsets(bs: u32) -> Vec<u32> {
        subsets(bs).collect_vec()
    }
}
