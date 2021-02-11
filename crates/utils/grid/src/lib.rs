mod dihedral;

pub use dihedral::Dihedral;

use std::{
    iter::FromIterator,
    ops::{Index, IndexMut},
};

#[derive(Clone, Debug, PartialEq)]
pub struct Grid<T> {
    h: usize,
    w: usize,
    elm: Box<[T]>,
}
impl<T> Grid<T> {
    /// Creates a new grid from an iterator and lengths of two sides.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new("01234567".chars(), 2, 4);
    /// assert_eq!(&grid[0], &['0', '1', '2', '3'] as &[char]);
    /// assert_eq!(&grid[1], &['4', '5', '6', '7'] as &[char]);
    /// ```
    pub fn new(iter: impl Iterator<Item = T>, h: usize, w: usize) -> Self {
        let elm = iter.collect::<Vec<_>>().into_boxed_slice();
        assert_eq!(elm.len(), h * w);
        Self { h, w, elm }
    }
    /// Returns an iterator to generate all the rows of a grid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new("01234567".chars(), 2, 4);
    /// let mut iter = grid.iter();
    /// assert_eq!(iter.next(), Some(&vec!['0', '1', '2', '3'] as &[char]));
    /// assert_eq!(iter.next(), Some(&vec!['4', '5', '6', '7'] as &[char]));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = &[T]> {
        self.elm.chunks(self.w)
    }
    /// Returns a mutable iterator to generate all the rows of a grid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let mut grid = Grid::new("01234567".chars(), 2, 4);
    /// grid.iter_mut().for_each(|v| v[1] = '$');
    /// assert_eq!(&grid[0], &['0', '$', '2', '3']);
    /// assert_eq!(&grid[1], &['4', '$', '6', '7']);
    /// ```
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut [T]> {
        self.elm.chunks_mut(self.w)
    }
    /// Returns an iterator to generate all the rows of a grid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new("01234567".chars(), 2, 4);
    /// let mut iter = grid.iter_flat();
    /// assert_eq!(iter.next(), Some(&'0'));
    /// assert_eq!(iter.next(), Some(&'1'));
    /// assert_eq!(iter.next(), Some(&'2'));
    /// assert_eq!(iter.next(), Some(&'3'));
    /// assert_eq!(iter.next(), Some(&'4'));
    /// assert_eq!(iter.next(), Some(&'5'));
    /// assert_eq!(iter.next(), Some(&'6'));
    /// assert_eq!(iter.next(), Some(&'7'));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_flat(&self) -> impl Iterator<Item = &T> {
        self.elm.iter()
    }
    /// Returns a mutable iterator to generate all the rows of a grid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let mut grid = Grid::new("01234567".chars(), 2, 4);
    /// grid.iter_flat_mut().for_each(|c| *c = ((*c as u8) + 1) as char);
    /// assert_eq!(&grid[0], &['1', '2', '3', '4']);
    /// assert_eq!(&grid[1], &['5', '6', '7', '8']);
    /// ```
    pub fn iter_flat_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.elm.iter_mut()
    }
    /// Converts into a boxed slice.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid /*: Box<[char]>*/ = Grid::new("01234567".chars(), 2, 4).into_boxed_slice();
    /// assert_eq!(&*grid, &['0', '1', '2', '3', '4', '5', '6', '7'] as &[char]);
    /// ```
    pub fn into_boxed_slice(self) -> Box<[T]> {
        self.elm
    }
    /// Converts into a vector.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid /*: Vec<char>*/ = Grid::new("01234567".chars(), 2, 4).into_vec();
    /// assert_eq!(grid, vec!['0', '1', '2', '3', '4', '5', '6', '7']);
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.elm.into_vec()
    }
}
impl<T> Index<usize> for Grid<T> {
    type Output = [T];
    fn index(&self, index: usize) -> &Self::Output {
        &self.elm[self.w * index..self.w * (index + 1)]
    }
}
impl<T> IndexMut<usize> for Grid<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.elm[self.w * index..self.w * (index + 1)]
    }
}

pub struct GridBuilder<T>(Box<[T]>);
impl<T> FromIterator<T> for GridBuilder<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self(iter.into_iter().collect::<Vec<_>>().into_boxed_slice())
    }
}
impl<T> GridBuilder<T> {
    pub fn width(self, w: usize) -> Grid<T> {
        let elm = self.0;
        let h = elm.len() / w;
        assert_eq!(elm.len(), h * w, "Failed to build a grid.");
        Grid { h, w, elm }
    }
}

#[cfg(test)]
mod tests {
    use super::GridBuilder;

    #[test]
    fn test_build_grid() {
        let grid = "01234567".chars().collect::<GridBuilder<_>>().width(4);
        assert_eq!(&grid[0], &['0', '1', '2', '3']);
        assert_eq!(&grid[1], &['4', '5', '6', '7']);
        assert_eq!(grid[0][0], '0');
        assert_eq!(grid[0][1], '1');
        assert_eq!(grid[0][2], '2');
        assert_eq!(grid[0][3], '3');
        assert_eq!(grid[1][0], '4');
        assert_eq!(grid[1][1], '5');
        assert_eq!(grid[1][2], '6');
        assert_eq!(grid[1][3], '7');
    }
}
