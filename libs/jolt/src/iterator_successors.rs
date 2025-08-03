/// `successors` for `Iterator`
pub trait IteratorSuccessors: Iterator {
    /// Creates an iterator like [`std::iter::successors`], but unlike it, uses an iterator to
    /// calculate the next element.
    ///
    /// # Specification
    ///
    /// Returns an iterator that generates the sequence $b_0, b_1, \ldots$ where:
    ///
    /// * `self`: $a_0, a_1, \ldots, a_{n - 1}$
    /// * `first`: $b_0$
    /// * `succ`: $f(a_i, b_i) = b_{i + 1}$
    ///
    ///
    /// # Example
    ///
    /// ```
    /// # use riff::IteratorSuccessors;
    /// let a = (1..=3)
    ///     .successors(Some([0]), |x, &[y]| Some([x + y]))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(a.as_slice(), &[[0], [1], [3], [6]]);
    /// ```
    fn successors<T, F>(self, first: Option<T>, succ: F) -> IterSuccessors<Self, T, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, &T) -> Option<T>,
    {
        IterSuccessors {
            iter: self,
            next: first,
            succ,
        }
    }
}
impl<I: Iterator> IteratorSuccessors for I {}

pub struct IterSuccessors<I, T, F> {
    iter: I,
    next: Option<T>,
    succ: F,
}
impl<I, T, F> Iterator for IterSuccessors<I, T, F>
where
    I: Iterator,
    F: FnMut(I::Item, &T) -> Option<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.next.take()?;
        let next2 = self.iter.next().and_then(|x| (self.succ)(x, &item));
        self.next = next2;
        Some(item)
    }
}
