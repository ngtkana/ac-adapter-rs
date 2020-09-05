#![warn(missing_docs, missing_doc_code_examples)]
//! イテレータのユーティルです。
//!
//! 詳しくは [`Seq`] までです。
//!
//! [`Seq`]: trait.Seq.html
//!

pub use self::accumulate::{accumulate, Accumulate};
pub use self::adjacent::{adjacent, Adjacent};
pub use self::aoj_copied::AojCopied;
pub use self::cartesian_product::{cartesian_product, CartesianProduct};
pub use self::format_intersparse::format_intersparse;
pub use self::grid_next::{grid_next, GridNext};
pub use self::intersperse::{intersperse, Intersperse};
pub use self::mul_step::{mul_step, MulStep};
pub use self::repeat_with::{repeat_with, RepeatWith};
pub use self::step::{step, Step};

use std::{fmt, ops};

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
        grid_next(self, ij, h, w)
    }

    /// `std::iter::copied` とほぼ同じ機能です。
    fn aoj_copied<'a, T: 'a>(self) -> AojCopied<Self>
    where
        Self: Sized + Iterator<Item = &'a T>,
        T: Copy,
    {
        AojCopied { iter: self }
    }

    /// `itertools` の同名のメソッドと同じです。
    fn cartesian_product<J>(self, other: J) -> CartesianProduct<Self, J::IntoIter>
    where
        Self: Sized,
        Self::Item: Clone,
        J: IntoIterator,
        J::IntoIter: Clone,
    {
        cartesian_product::cartesian_product(self, other.into_iter())
    }

    /// 累積和です。
    fn accumulate<T>(self, init: T) -> Accumulate<Self, T>
    where
        T: Clone + ops::AddAssign<Self::Item>,
    {
        accumulate::accumulate(self, init)
    }

    /// `itertools` の同名のメソッドと同じです。
    fn intersperse(self, elt: Self::Item) -> Intersperse<Self> {
        intersperse::intersperse(self, elt)
    }

    /// アイテムをフォーマットして、間に `separator` をはさみます。
    fn format_intersparse<T>(self, separator: T) -> String
    where
        Self::Item: fmt::Display,
        T: fmt::Display,
    {
        self.map(|x| format!("{}", x))
            .intersperse(format!("{}", separator))
            .collect::<String>()
    }
}

mod aoj_copied {
    use std::iter::DoubleEndedIterator;

    #[allow(missing_docs)]
    #[derive(Debug, Clone)]
    pub struct AojCopied<I> {
        pub iter: I,
    }

    impl<'a, I, T: 'a> Iterator for AojCopied<I>
    where
        I: Iterator<Item = &'a T>,
        T: Copy,
    {
        type Item = T;

        fn next(&mut self) -> Option<T> {
            self.iter.next().map(|&x| x)
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            self.iter.size_hint()
        }

        fn fold<Acc, F>(self, initer: Acc, mut f: F) -> Acc
        where
            F: FnMut(Acc, Self::Item) -> Acc,
        {
            self.iter.fold(initer, move |acc, &elt| f(acc, elt))
        }

        fn nth(&mut self, n: usize) -> Option<T> {
            self.iter.nth(n).map(|&x| x)
        }

        fn last(self) -> Option<T> {
            self.iter.last().map(|&x| x)
        }

        fn count(self) -> usize {
            self.iter.count()
        }
    }

    impl<'a, I, T: 'a> DoubleEndedIterator for AojCopied<I>
    where
        I: DoubleEndedIterator<Item = &'a T>,
        T: Copy,
    {
        fn next_back(&mut self) -> Option<T> {
            self.iter.next_back().map(|&x| x)
        }
    }

    impl<'a, I, T: 'a> ExactSizeIterator for AojCopied<I>
    where
        I: ExactSizeIterator<Item = &'a T>,
        T: Copy,
    {
        fn len(&self) -> usize {
            self.iter.len()
        }
    }
}

mod adjacent {
    #[allow(missing_docs)]
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

    #[allow(missing_docs)]
    pub struct Adjacent<I, T>
    where
        I: Iterator<Item = T>,
    {
        iter: I,
        prv: Option<T>,
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
}

mod grid_next {
    #[allow(missing_docs)]
    pub fn grid_next<T>(difference: T, ij: (usize, usize), h: usize, w: usize) -> GridNext<T>
    where
        T: Iterator<Item = (i64, i64)>,
    {
        GridNext {
            i: ij.0 as i64,
            j: ij.1 as i64,
            h: h as i64,
            w: w as i64,
            difference,
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
}

mod step {
    #[allow(missing_docs)]
    pub fn step<T, U>(init: T, step: U) -> Step<T, U>
    where
        T: Copy,
        U: Copy,
        T: ::std::ops::Add<U, Output = T>,
    {
        Step { now: init, step }
    }

    #[allow(missing_docs)]
    #[derive(Debug, Clone)]
    pub struct Step<T, U> {
        now: T,
        step: U,
    }

    #[allow(missing_docs)]
    impl<T, U> Iterator for Step<T, U>
    where
        T: Copy,
        U: Copy,
        T: ::std::ops::Add<U, Output = T>,
    {
        type Item = T;

        fn next(&mut self) -> Option<T> {
            let next = self.now + self.step;
            Some(::std::mem::replace(&mut self.now, next))
        }
    }
}

mod mul_step {
    #[allow(missing_docs)]
    pub fn mul_step<T, U>(init: T, step: U) -> MulStep<T, U>
    where
        T: Copy,
        U: Copy,
        T: ::std::ops::Mul<U, Output = T>,
    {
        MulStep { now: init, step }
    }

    #[allow(missing_docs)]
    #[derive(Debug, Clone)]
    pub struct MulStep<T, U> {
        now: T,
        step: U,
    }

    #[allow(missing_docs)]
    impl<T, U> Iterator for MulStep<T, U>
    where
        T: Copy,
        U: Copy,
        T: ::std::ops::Mul<U, Output = T>,
    {
        type Item = T;

        fn next(&mut self) -> Option<T> {
            let next = self.now * self.step;
            Some(::std::mem::replace(&mut self.now, next))
        }
    }
}

mod repeat_with {
    #[allow(missing_docs)]
    pub fn repeat_with<A, F: FnMut() -> A>(repeater: F) -> RepeatWith<F> {
        RepeatWith { repeater }
    }

    #[allow(missing_docs)]
    #[derive(Debug, Clone)]
    pub struct RepeatWith<F> {
        repeater: F,
    }

    impl<A, F: FnMut() -> A> Iterator for RepeatWith<F> {
        type Item = A;

        #[inline]
        fn next(&mut self) -> Option<A> {
            Some((self.repeater)())
        }

        #[inline]
        fn size_hint(&self) -> (usize, Option<usize>) {
            (::std::usize::MAX, None)
        }
    }
}

mod accumulate {
    use super::*;

    #[allow(missing_docs)]
    #[derive(Debug, Clone)]
    pub struct Accumulate<I, T> {
        prev: Option<T>,
        iter: I,
    }

    #[allow(missing_docs)]
    pub fn accumulate<I, T>(iter: I, init: T) -> Accumulate<I, T>
    where
        I: Iterator,
        T: Clone + ops::AddAssign<I::Item>,
    {
        Accumulate {
            prev: Some(init),
            iter,
        }
    }

    impl<I, T> Iterator for Accumulate<I, T>
    where
        I: Iterator,
        T: Clone + ops::AddAssign<I::Item>,
    {
        type Item = T;

        fn next(&mut self) -> Option<T> {
            let res = self.prev.clone();
            if let Some(prev) = self.prev.as_mut() {
                if let Some(next) = self.iter.next() {
                    *prev += next;
                } else {
                    self.prev = None;
                }
            }
            res
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            size_hint::add_scalar(self.iter.size_hint(), 1)
        }
    }
}

mod cartesian_product {
    #[allow(missing_docs)]
    #[derive(Debug, Clone)]
    pub struct CartesianProduct<I, J>
    where
        I: Iterator,
    {
        a: I,
        a_cur: Option<I::Item>,
        b: J,
        b_orig: J,
    }

    #[allow(missing_docs)]
    pub fn cartesian_product<I, J>(mut i: I, j: J) -> CartesianProduct<I, J>
    where
        I: Iterator,
        J: Clone + Iterator,
        I::Item: Clone,
    {
        CartesianProduct {
            a_cur: i.next(),
            a: i,
            b_orig: j.clone(),
            b: j,
        }
    }

    impl<I, J> Iterator for CartesianProduct<I, J>
    where
        I: Iterator,
        J: Clone + Iterator,
        I::Item: Clone,
    {
        type Item = (I::Item, J::Item);

        fn next(&mut self) -> Option<(I::Item, J::Item)> {
            let elt_b = match self.b.next() {
                None => {
                    self.b = self.b_orig.clone();
                    match self.b.next() {
                        None => return None,
                        Some(x) => {
                            self.a_cur = self.a.next();
                            x
                        }
                    }
                }
                Some(x) => x,
            };
            match self.a_cur {
                None => None,
                Some(ref a) => Some((a.clone(), elt_b)),
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            let has_cur = self.a_cur.is_some() as usize;
            // Not ExactSizeIterator because size may be larger than usize
            let (b_min, b_max) = self.b.size_hint();

            // Compute a * b_orig + b for both lower and upper bound
            super::size_hint::add(
                super::size_hint::mul(self.a.size_hint(), self.b_orig.size_hint()),
                (b_min * has_cur, b_max.map(move |x| x * has_cur)),
            )
        }

        fn fold<Acc, G>(mut self, mut accum: Acc, mut f: G) -> Acc
        where
            G: FnMut(Acc, Self::Item) -> Acc,
        {
            if let Some(mut a) = self.a_cur.take() {
                let mut b = self.b;
                loop {
                    accum = b.fold(accum, |acc, elt| f(acc, (a.clone(), elt)));

                    // we can only continue iterating a if we had a first element;
                    if let Some(next_a) = self.a.next() {
                        b = self.b_orig.clone();
                        a = next_a;
                    } else {
                        break;
                    }
                }
            }
            accum
        }
    }
}

#[allow(missing_docs)]
mod intersperse {
    use super::size_hint;
    use std::iter;

    #[derive(Debug, Clone)]
    #[must_use = "iterator adaptors are lazy and do nothing unless consumed"]
    pub struct Intersperse<I>
    where
        I: Iterator,
    {
        element: I::Item,
        iter: iter::Fuse<I>,
        peek: Option<I::Item>,
    }

    pub fn intersperse<I>(iter: I, elt: I::Item) -> Intersperse<I>
    where
        I: Iterator,
    {
        let mut iter = iter.fuse();
        Intersperse {
            peek: iter.next(),
            iter,
            element: elt,
        }
    }

    impl<I> Iterator for Intersperse<I>
    where
        I: Iterator,
        I::Item: Clone,
    {
        type Item = I::Item;
        #[inline]
        fn next(&mut self) -> Option<I::Item> {
            if self.peek.is_some() {
                self.peek.take()
            } else {
                self.peek = self.iter.next();
                if self.peek.is_some() {
                    Some(self.element.clone())
                } else {
                    None
                }
            }
        }

        fn size_hint(&self) -> (usize, Option<usize>) {
            // 2 * SH + { 1 or 0 }
            let has_peek = self.peek.is_some() as usize;
            let sh = self.iter.size_hint();
            size_hint::add_scalar(size_hint::add(sh, sh), has_peek)
        }

        fn fold<B, F>(mut self, init: B, mut f: F) -> B
        where
            Self: Sized,
            F: FnMut(B, Self::Item) -> B,
        {
            let mut accum = init;

            if let Some(x) = self.peek.take() {
                accum = f(accum, x);
            }

            let element = &self.element;

            self.iter.fold(accum, |accum, x| {
                let accum = f(accum, element.clone());
                f(accum, x)
            })
        }
    }
}

#[allow(missing_docs)]
mod format_intersparse {
    use super::Seq;
    use std::fmt;

    pub fn format_intersparse<I, T>(iter: I, separator: T) -> String
    where
        I: Iterator,
        I::Item: fmt::Display,
        T: fmt::Display,
    {
        iter.map(|x| format!("{}", x))
            .intersperse(format!("{}", separator))
            .collect::<String>()
    }
}

mod size_hint {
    //! Arithmetic on **Iterator** *.size_hint()* values.
    //!

    use std::cmp;
    use std::usize;

    /// **SizeHint** is the return type of **Iterator::size_hint()**.
    pub type SizeHint = (usize, Option<usize>);

    /// Add **SizeHint** correctly.
    #[inline]
    pub fn add(a: SizeHint, b: SizeHint) -> SizeHint {
        let min = a.0.saturating_add(b.0);
        let max = match (a.1, b.1) {
            (Some(x), Some(y)) => x.checked_add(y),
            _ => None,
        };

        (min, max)
    }

    /// Add **x** correctly to a **SizeHint**.
    #[inline]
    #[allow(dead_code)]
    pub fn add_scalar(sh: SizeHint, x: usize) -> SizeHint {
        let (mut low, mut hi) = sh;
        low = low.saturating_add(x);
        hi = hi.and_then(|elt| elt.checked_add(x));
        (low, hi)
    }

    /// Sub **x** correctly to a **SizeHint**.
    #[inline]
    #[allow(dead_code)]
    pub fn sub_scalar(sh: SizeHint, x: usize) -> SizeHint {
        let (mut low, mut hi) = sh;
        low = low.saturating_sub(x);
        hi = hi.map(|elt| elt.saturating_sub(x));
        (low, hi)
    }

    /// Multiply **SizeHint** correctly
    ///
    /// ```ignore
    /// use std::usize;
    /// use itertools::size_hint;
    ///
    /// assert_eq!(size_hint::mul((3, Some(4)), (3, Some(4))),
    ///            (9, Some(16)));
    ///
    /// assert_eq!(size_hint::mul((3, Some(4)), (usize::MAX, None)),
    ///            (usize::MAX, None));
    ///
    /// assert_eq!(size_hint::mul((3, None), (0, Some(0))),
    ///            (0, Some(0)));
    /// ```
    #[inline]
    #[allow(dead_code)]
    pub fn mul(a: SizeHint, b: SizeHint) -> SizeHint {
        let low = a.0.saturating_mul(b.0);
        let hi = match (a.1, b.1) {
            (Some(x), Some(y)) => x.checked_mul(y),
            (Some(0), None) | (None, Some(0)) => Some(0),
            _ => None,
        };
        (low, hi)
    }

    /// Multiply **x** correctly with a **SizeHint**.
    #[inline]
    #[allow(dead_code)]
    pub fn mul_scalar(sh: SizeHint, x: usize) -> SizeHint {
        let (mut low, mut hi) = sh;
        low = low.saturating_mul(x);
        hi = hi.and_then(|elt| elt.checked_mul(x));
        (low, hi)
    }

    /// Return the maximum
    #[inline]
    #[allow(dead_code)]
    pub fn max(a: SizeHint, b: SizeHint) -> SizeHint {
        let (a_lower, a_upper) = a;
        let (b_lower, b_upper) = b;

        let lower = cmp::max(a_lower, b_lower);

        let upper = match (a_upper, b_upper) {
            (Some(x), Some(y)) => Some(cmp::max(x, y)),
            _ => None,
        };

        (lower, upper)
    }

    /// Return the minimum
    #[inline]
    #[allow(dead_code)]
    pub fn min(a: SizeHint, b: SizeHint) -> SizeHint {
        let (a_lower, a_upper) = a;
        let (b_lower, b_upper) = b;
        let lower = cmp::min(a_lower, b_lower);
        let upper = match (a_upper, b_upper) {
            (Some(u1), Some(u2)) => Some(cmp::min(u1, u2)),
            _ => a_upper.or(b_upper),
        };
        (lower, upper)
    }
}
