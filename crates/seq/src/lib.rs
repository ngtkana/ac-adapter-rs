#![warn(missing_docs, missing_doc_code_examples)]
//! イテレータのユーティルです。
//!
//! 詳しくは [`Seq`] までです。
//!
//! [`Seq`]: trait.Seq.html
//!

impl<I: Iterator> Seq for I {}

/// イテレータのユーティルです。
pub trait Seq: Iterator + Sized {
    /// 隣りあう 2 つの項のタプルを走査です。
    ///
    /// # Examples
    ///
    /// ```
    /// use seq::Seq;
    /// let mut iter = [0, 1, 2].iter().copied().adjacent();
    /// assert_eq!(iter.next(), Some((0, 1)));
    /// assert_eq!(iter.next(), Some((1, 2)));
    /// assert_eq!(iter.next(), None);
    /// ```
    ///
    /// 要素が 1 個以下のときには空イテレータになります。
    ///
    /// ```
    /// use seq::Seq;
    /// let mut iter = [0].iter().adjacent();
    /// assert_eq!(iter.next(), None);
    /// ```
    fn adjacent(self) -> Adjacent<Self, Self::Item>
    where
        Self::Item: Clone,
    {
        adjacent(self)
    }

    /// 隣接するグリッドを走査できます。
    ///
    /// # Examples
    ///
    /// ```
    /// use seq::Seq;
    /// const KNIGHT: [(i64, i64); 8] = [
    ///     (1, 2),
    ///     (2, 1),
    ///     (1, -2),
    ///     (2, -1),
    ///     (-1, 2),
    ///     (-2, 1),
    ///     (-1, -2),
    ///     (-2, -1),
    /// ];
    /// let mut result = KNIGHT
    ///     .iter()
    ///     .copied()
    ///     .grid_next((1, 2), 4, 3)
    ///     .collect::<Vec<_>>();
    /// let expected = vec![(2, 0),(3, 1), (0, 0)];
    /// assert_eq!(result, expected);
    /// ```
    fn grid_next(self, ij: (usize, usize), h: usize, w: usize) -> GridNext<Self>
    where
        Self: Iterator<Item = (i64, i64)>,
    {
        GridNext {
            i: ij.0 as i64,
            j: ij.1 as i64,
            h: h as i64,
            w: w as i64,
            difference: self,
        }
    }
}

#[allow(missing_docs)]
pub struct Adjacent<I, T>
where
    I: Iterator<Item = T>,
{
    iter: I,
    prv: Option<T>,
}

/// [`Adjacent`] のフリー関数版です。
///
/// [`adjacent`]: trait.Seq.html#method.adjacent
pub fn adjacent<I, T>(mut iter: I) -> Adjacent<I, T>
where
    I: Iterator<Item = T>,
    T: Clone,
{
    if let Some(first) = iter.next() {
        Adjacent {
            iter,
            prv: Some(first),
        }
    } else {
        Adjacent { iter, prv: None }
    }
}

impl<I, T> Iterator for Adjacent<I, T>
where
    I: Iterator<Item = T>,
    T: Clone,
{
    type Item = (T, T);

    fn next(&mut self) -> Option<(T, T)> {
        self.prv.as_ref().cloned().and_then(|first| {
            self.iter.next().map(|second| {
                self.prv = Some(second.clone());
                (first, second)
            })
        })
    }
}

#[allow(missing_docs)]
#[derive(Debug, Clone)]
pub struct GridNext<T> {
    i: i64,
    j: i64,
    h: i64,
    w: i64,
    difference: T,
}

impl<T> Iterator for GridNext<T>
where
    T: Iterator<Item = (i64, i64)>,
{
    type Item = (usize, usize);

    fn next(&mut self) -> Option<(usize, usize)> {
        while let Some((di, dj)) = self.difference.next() {
            let ni = self.i + di;
            let nj = self.j + dj;
            if 0 <= ni && ni < self.h && 0 <= nj && nj < self.w {
                return Some((ni as usize, nj as usize));
            }
        }
        None
    }
}
