use std::ops::{Index, IndexMut};

use super::{coord, swap_size, Coord, Dihedral, Rows};

/// A wrapper to rotate/reflect a grid logically.
///
/// Use [`Dihedral`] to act this. An affine representation of `Dihedral` on Map(ℤ², T) is defined by
///
/// * [`R1`](Dihedral::R1) is a 90-degrees rotation, that is `(R1 * f)(i, j) = f(w - 1 - j, h)`.
/// * [`R0S`](Dihedral::R0S) is a transposition, that is `(R0S * f)(i, j) = f(j, i)`.
///
/// Thus each the element acts like this:
///
/// * [`R0`](Dihedral::R0): identity.
/// * [`R1`](Dihedral::R1): rotate left.
/// * [`R2`](Dihedral::R2): anti-position.
/// * [`R3`](Dihedral::R3): rotate right.
/// * [`R0S`](Dihedral::R0S): transposition.
/// * [`R1S`](Dihedral::R1S): reflection through `i = (h - 1) / 2`.
/// * [`R2S`](Dihedral::R2S): anti-transposition.
/// * [`R3S`](Dihedral::R3S): reflections through `j = (w - 1) / 2`.
///
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grid<T> {
    elm: Vec<T>,
    raw_h: usize,
    raw_w: usize,
    d: Dihedral,
    default: Option<T>,
}
impl<T> Grid<T> {
    /// Creates a new `Grid`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new(vec![0, 1, 2, 3], 2, 2);
    /// assert_eq!(grid.h(), 2);
    /// ```
    pub fn new(elm: Vec<T>, h: usize, w: usize) -> Self {
        assert_eq!(elm.len(), h * w);
        Self {
            elm,
            raw_h: h,
            raw_w: w,
            d: Dihedral::R0,
            default: None,
        }
    }
    /// Returns a `Grid` object surround by infinite `default` logically.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new(vec![0, 1, 2, 3], 2, 2).surround(std::u32::MAX);
    /// assert_eq!(grid.iget_or_default(0, 0), 0);
    /// assert_eq!(grid.iget_or_default(1, 0), 2);
    /// assert_eq!(grid.iget_or_default(-1, 0), std::u32::MAX);
    /// ```
    pub fn surround(mut self, default: T) -> Self {
        self.default = Some(default);
        self
    }
    /// Returns a logical height of a grid.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::{Grid, Dihedral};
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2);
    /// assert_eq!(grid.h(), 1);
    ///
    /// grid.apply(Dihedral::R0S);
    /// assert_eq!(grid.h(), 2);
    /// ```
    pub fn h(&self) -> usize {
        if swap_size(self.d) {
            self.raw_w
        } else {
            self.raw_h
        }
    }
    /// Returns a logical width of a grid.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::{Grid, Dihedral};
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2);
    /// assert_eq!(grid.w(), 2);
    ///
    /// grid.apply(Dihedral::R0S);
    /// assert_eq!(grid.w(), 1);
    /// ```
    pub fn w(&self) -> usize {
        if swap_size(self.d) {
            self.raw_h
        } else {
            self.raw_w
        }
    }
    /// If `(i, j)` is within the domain, returns the corresponding value, while otherwise returns the
    /// "default value" specified via [`Grid::surround`].
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2).surround(-1);
    /// assert_eq!(grid.iget_or_default(0, 0), 0);
    /// assert_eq!(grid.iget_or_default(9, 0), -1);
    /// ```
    pub fn iget_or_default(&self, i: isize, j: isize) -> T
    where
        T: Copy,
    {
        self.iget(i, j)
            .copied()
            .or(self.default)
            .unwrap_or_else(|| {
                panic!(
                    "Called `iget_or_default` with no-default grid. (i, j) = ({i}, {j})",
                    i = i,
                    j = j,
                )
            })
    }
    /// If `(i, j)` is within the domain, returns a reference to the corresponding value,
    /// while otherwise returns `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2).surround(-1);
    /// assert_eq!(grid.iget(0, 0), Some(&0));
    /// assert_eq!(grid.iget(9, 0), None);
    /// ```
    pub fn iget(&self, i: isize, j: isize) -> Option<&T> {
        index(i, j, self.raw_h, self.raw_w, self.d).map(|k| &self.elm[k])
    }
    /// If `(i, j)` is within the domain, returns a mutable reference to the corresponding value,
    /// while otherwise returns `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2).surround(-1);
    /// assert_eq!(grid[(0, 0)], 0);
    /// *grid.iget_mut(0, 0).unwrap() = 3;
    /// assert_eq!(grid[(0, 0)], 3);
    /// ```
    pub fn iget_mut(&mut self, i: isize, j: isize) -> Option<&mut T> {
        let k = index(i, j, self.raw_h, self.raw_w, self.d)?;
        Some(&mut self.elm[k])
    }
    /// If `(i, j)` is within the domain, returns a reference to the corresponding value,
    /// while otherwise returns `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2).surround(-1);
    /// assert_eq!(grid.get(0, 0), Some(&0));
    /// assert_eq!(grid.get(9, 0), None);
    /// ```
    pub fn get(&self, i: usize, j: usize) -> Option<&T> {
        self.iget(i as isize, j as isize)
    }
    /// If `(i, j)` is within the domain, returns a mutable reference to the corresponding value,
    /// while otherwise returns `None`.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2).surround(-1);
    /// assert_eq!(grid[(0, 0)], 0);
    /// *grid.get_mut(0, 0).unwrap() = 3;
    /// assert_eq!(grid[(0, 0)], 3);
    /// ```
    pub fn get_mut(&mut self, i: isize, j: isize) -> Option<&mut T> {
        self.iget_mut(i, j)
    }
    /// Apply a dihedral element to a grid logically.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::{Grid, Dihedral};
    ///
    /// let mut grid = Grid::new(vec![0, 1], 1, 2);
    /// assert_eq!(grid.get(0, 1), Some(&1));
    /// assert_eq!(grid.get(1, 0), None);
    /// grid.apply(Dihedral::R0S);
    /// assert_eq!(grid.get(0, 1), None);
    /// assert_eq!(grid.get(1, 0), Some(&1));
    /// ```
    pub fn apply(&mut self, d: Dihedral) {
        self.d *= d;
    }
    /// Returns a grid applied a dihedral element logically.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use grid::{Grid, Dihedral};
    ///
    /// let grid = Grid::new(vec![0, 1], 1, 2);
    /// assert_eq!(grid.get(0, 1), Some(&1));
    /// assert_eq!(grid.get(1, 0), None);
    /// let grid = grid.applied(Dihedral::R0S);
    /// assert_eq!(grid.get(0, 1), None);
    /// assert_eq!(grid.get(1, 0), Some(&1));
    /// ```
    pub fn applied(mut self, d: Dihedral) -> Self {
        self.d *= d;
        self
    }
    /// Returns an iterator over the *logical* rows of this grid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new("01234567".chars().collect::<Vec<_>>(), 2, 4);
    /// let mut rows = grid.rows();
    /// assert_eq!(rows.next().unwrap().iter().copied().collect::<Vec<_>>(), vec!['0', '1', '2', '3']);
    /// assert_eq!(rows.next().unwrap().iter().copied().collect::<Vec<_>>(), vec!['4', '5', '6', '7']);
    /// assert_eq!(rows.next(), None);
    /// ```
    pub fn rows(&self) -> Rows<'_, T> {
        Rows::new(coord(self.raw_h, self.raw_w, self.d), &self.elm)
    }
    /// Returns an iterator over the *logical* rows of this grid.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new("01234567".chars().collect::<Vec<_>>(), 2, 4);
    /// let mut rows = grid.rows();
    /// assert_eq!(rows.next().unwrap().iter().copied().collect::<Vec<_>>(), vec!['0', '1', '2', '3']);
    /// assert_eq!(rows.next().unwrap().iter().copied().collect::<Vec<_>>(), vec!['4', '5', '6', '7']);
    /// assert_eq!(rows.next(), None);
    /// ```
    pub fn cells(&self) -> impl Iterator<Item = &T> {
        Rows::new(coord(self.raw_h, self.raw_w, self.d), &self.elm).flatten()
    }
    /// Converts into a 2d vector.
    ///
    /// # Examples
    ///
    /// Basic usage:
    /// ```
    /// use grid::Grid;
    ///
    /// let grid = Grid::new("01234567".chars().collect::<Vec<_>>(), 2, 4);
    /// let mut rows = grid.rows();
    /// assert_eq!(rows.next().unwrap().iter().copied().collect::<Vec<_>>(), vec!['0', '1', '2', '3']);
    /// assert_eq!(rows.next().unwrap().iter().copied().collect::<Vec<_>>(), vec!['4', '5', '6', '7']);
    /// assert_eq!(rows.next(), None);
    /// ```
    pub fn collect_vec2(&self) -> Vec<Vec<T>>
    where
        T: Clone,
    {
        self.rows()
            .map(|row| row.into_iter().cloned().collect::<Vec<_>>())
            .collect()
    }
}

fn index(i: isize, j: isize, raw_h: usize, raw_w: usize, d: Dihedral) -> Option<usize> {
    let Coord { origin, x, y, h, w } = coord(raw_h, raw_w, d);
    if (0..h as isize).contains(&i) && (0..w as isize).contains(&j) {
        Some((origin + i * x + j * y) as usize)
    } else {
        None
    }
}

fn index_panic(i: isize, j: isize, raw_h: usize, raw_w: usize, d: Dihedral) -> usize {
    let Coord { origin, x, y, h, w } = coord(raw_h, raw_w, d);
    assert!(
        (0..h as isize).contains(&i) && (0..w as isize).contains(&j),
        "Out of grid. (i, j) = ({i}, {j}), while (h, w) = ({h}, {w})",
        i = i,
        j = j,
        h = h,
        w = w
    );
    (origin + i * x + j * y) as usize
}

impl<T> Index<(usize, usize)> for Grid<T> {
    type Output = T;
    fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
        &self.elm[index_panic(i as isize, j as isize, self.raw_h, self.raw_w, self.d)]
    }
}
impl<T> IndexMut<(usize, usize)> for Grid<T> {
    fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
        &mut self.elm[index_panic(i as isize, j as isize, self.raw_h, self.raw_w, self.d)]
    }
}

#[cfg(test)]
mod tests {
    use {
        crate::{Dihedral, Grid},
        test_case::test_case,
    };

    fn sample() -> Grid<u8> {
        Grid::new(vec![0, 1, 2, 3, 4, 5], 2, 3)
    }

    const ALL_DIHEDRAL: [Dihedral; 8] = [
        Dihedral::R0,
        Dihedral::R1,
        Dihedral::R2,
        Dihedral::R3,
        Dihedral::R0S,
        Dihedral::R1S,
        Dihedral::R2S,
        Dihedral::R3S,
    ];

    #[test_case(Dihedral::R0 => vec![vec![0, 1, 2], vec![3, 4, 5]])]
    #[test_case(Dihedral::R1 => vec![vec![2, 5], vec![1, 4], vec![0, 3]])]
    #[test_case(Dihedral::R2 => vec![vec![5, 4, 3], vec![2, 1, 0]])]
    #[test_case(Dihedral::R3 => vec![vec![3, 0], vec![4, 1], vec![5, 2]])]
    #[test_case(Dihedral::R0S => vec![vec![0, 3], vec![1, 4], vec![2, 5]])]
    #[test_case(Dihedral::R1S => vec![vec![2, 1, 0], vec![5, 4, 3]])]
    #[test_case(Dihedral::R2S => vec![vec![5, 2], vec![4, 1], vec![3, 0]])]
    #[test_case(Dihedral::R3S => vec![vec![3, 4, 5], vec![0, 1, 2]])]
    fn test_handle_collect_vec2(d: Dihedral) -> Vec<Vec<u8>> {
        sample().applied(d).collect_vec2()
    }

    #[test]
    fn test_representation() {
        let grid = sample();
        for &d in &ALL_DIHEDRAL {
            for &e in &ALL_DIHEDRAL {
                let f = d * e;
                assert_eq!(
                    grid.clone().applied(d).applied(e).collect_vec2(),
                    grid.clone().applied(f).collect_vec2()
                );
            }
        }
    }
}
