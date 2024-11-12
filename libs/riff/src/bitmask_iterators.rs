use super::numeric_traits::Unsigned;

/// Generates all the $k$-subsets of $[0, N[$
///
/// # Examples
///
/// Basic usage:
/// ```
/// use riff::bitmask_combinations;
///
/// assert_eq!(bitmask_combinations::<u32>(3, 2).collect::<Vec<_>>(), vec![
///     3, 5, 6
/// ]);
/// ```
pub fn bitmask_combinations<T: Unsigned>(n: u32, k: u32) -> BitmaskCombinations<T> {
    assert!(k < T::bit_length() && k < T::bit_length());
    BitmaskCombinations {
        n,
        bs: (T::one() << k) - T::one(),
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct BitmaskCombinations<T> {
    n: u32,
    bs: T,
}
impl<T: Unsigned> Iterator for BitmaskCombinations<T> {
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

/// Generates all the subsets of `bs`.
///
/// # Examples
///
/// Basic usage:
/// ```
/// use riff::bitmask_subsets;
///
/// assert_eq!(bitmask_subsets(10u32).collect::<Vec<_>>(), vec![
///     0, 2, 8, 10
/// ]);
/// ```
pub fn bitmask_subsets<T: Unsigned>(bs: T) -> BitmaskSubsets<T> {
    BitmaskSubsets {
        bs,
        full: bs,
        finished: false,
    }
}

#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct BitmaskSubsets<T> {
    bs: T,
    full: T,
    finished: bool,
}
impl<T: Unsigned> Iterator for BitmaskSubsets<T> {
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
