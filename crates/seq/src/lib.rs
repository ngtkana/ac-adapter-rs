#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]
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
}

/// 詳しくは [`adjacent`] までです。
///
/// [`adjacent`]: trait.Seq.html#method.adjacent
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

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
