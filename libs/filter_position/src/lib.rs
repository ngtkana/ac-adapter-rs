//! 条件を満たす位置を返すイテレータです。
//!
//! # 使い方
//!
//! トレイト [`TFilterPosition`] を use してメソッドを呼びましょう。
//!
//!
//! # Examples
//!
//! ```
//! use filter_position::TFilterPosition;
//!
//! let result = [10, 11, 12]
//!     .iter()
//!     .filter_position_by(|&x| x % 2 == 0)
//!     .collect::<Vec<_>>();
//! let expected = vec![0, 2];
//! assert_eq!(result, expected);
//! ```

use std::convert::identity;

impl<T: Iterator> TFilterPosition for T {}

/// 条件を満たす位置を返すイテレータを作るトレイトです。
pub trait TFilterPosition: Sized + Iterator {
    /// 条件を満たす位置を返すイテレータを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use filter_position::TFilterPosition;
    ///
    /// let result = [10, 11, 12]
    ///     .iter()
    ///     .filter_position_by(|&x| x % 2 == 0)
    ///     .collect::<Vec<_>>();
    /// let expected = vec![0, 2];
    /// assert_eq!(result, expected);
    /// ```
    fn filter_position_by<F>(self, f: F) -> FilterPosition<Self, F>
    where
        F: Fn(Self::Item) -> bool,
    {
        FilterPosition {
            iter: self,
            pos: 0,
            f,
        }
    }
    /// `true` の位置を返すイテレータを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use filter_position::TFilterPosition;
    ///
    /// let result = [true, false, true]
    ///     .iter()
    ///     .copied()
    ///     .filter_position()
    ///     .collect::<Vec<_>>();
    /// let expected = vec![0, 2];
    /// assert_eq!(result, expected);
    /// ```
    fn filter_position(self) -> FilterPosition<Self, fn(bool) -> bool>
    where
        Self: Iterator<Item = bool>,
    {
        self.filter_position_by(identity)
    }
}

/// [`TFilterPosition::filter_position_by`] の作るイテレータです。
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct FilterPosition<I, F> {
    iter: I,
    pos: usize,
    f: F,
}

impl<I: Iterator, F: Fn(I::Item) -> bool> Iterator for FilterPosition<I, F> {
    type Item = usize;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if (self.f)(self.iter.next()?) {
                let pos = self.pos;
                self.pos += 1;
                return Some(pos);
            }
            self.pos += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use {super::TFilterPosition, itertools::assert_equal};

    #[test]
    fn test_filter_position() {
        assert_equal(
            [false, false, false].iter().copied().filter_position(),
            Vec::<usize>::new().into_iter(),
        );
        assert_equal(
            [true, false, false].iter().copied().filter_position(),
            vec![0],
        );
        assert_equal(
            [false, true, false].iter().copied().filter_position(),
            vec![1],
        );
        assert_equal(
            [true, true, false].iter().copied().filter_position(),
            vec![0, 1],
        );
        assert_equal(
            [false, false, true].iter().copied().filter_position(),
            vec![2],
        );
        assert_equal(
            [true, false, true].iter().copied().filter_position(),
            vec![0, 2],
        );
        assert_equal(
            [false, true, true].iter().copied().filter_position(),
            vec![1, 2],
        );
        assert_equal(
            [true, true, true].iter().copied().filter_position(),
            vec![0, 1, 2],
        );
    }

    #[test]
    fn test_filter_position_by() {
        assert_equal(
            [10, 11, 12].iter().filter_position_by(|&x| x % 2 == 0),
            vec![0, 2],
        );
    }
}
