use super::Coord;
use std::ops::Index;

/// An iterator over all the rows of [`Grid`](super::Grid).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Rows<'a, T> {
    elm: &'a [T],
    crr: isize,
    step: isize,
    count: usize,
    small_step: isize,
    chunk_size: usize,
}
impl<'a, T> Rows<'a, T> {
    pub fn new(coord: Coord, elm: &'a [T]) -> Self {
        let Coord { origin, x, y, h, w } = coord;
        Rows {
            elm,
            crr: origin,
            step: x,
            count: h,
            small_step: y,
            chunk_size: w,
        }
    }
}
impl<'a, T> Iterator for Rows<'a, T> {
    type Item = Row<'a, T>;
    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 0 {
            None
        } else {
            self.count -= 1;
            let head = self.crr;
            self.crr += self.step;
            Some(Row {
                elm: self.elm,
                head,
                len: self.chunk_size,
                step: self.small_step,
            })
        }
    }
}

/// The item type of a iterable type [`Rows`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Row<'a, T> {
    elm: &'a [T],
    len: usize,
    head: isize,
    step: isize,
}
impl<T> Index<usize> for Row<'_, T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        assert!(index < self.len, "Index out of range.");
        &self.elm[(self.head + self.step * index as isize) as usize]
    }
}
impl<'a, T> Row<'a, T> {
    pub fn iter(&self) -> RowIter<'a, T> {
        let Self {
            elm,
            len,
            head,
            step,
        } = self;
        RowIter {
            elm,
            count: *len,
            crr: *head,
            step: *step,
        }
    }
}
impl<'a, T> IntoIterator for Row<'a, T> {
    type Item = &'a T;
    type IntoIter = RowIter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        let Self {
            elm,
            len,
            head,
            step,
        } = self;
        RowIter {
            elm,
            count: len,
            crr: head,
            step,
        }
    }
}

/// An iterator over all the cells of a grid.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RowIter<'a, T> {
    elm: &'a [T],
    count: usize,
    crr: isize,
    step: isize,
}
impl<'a, T> Iterator for RowIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.count == 0 {
            None
        } else {
            self.count -= 1;
            let crr = self.crr as usize;
            self.crr += self.step;
            Some(&self.elm[crr])
        }
    }
}
