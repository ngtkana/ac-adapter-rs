use std::{
    fmt::{self, Debug, Formatter},
    ops::{Bound, Range, RangeBounds},
};

/// A range aggregation data structure by SWAG algorithm.
///
/// It processes many [`fold`](SwagSpan::fold) queries in linear time in total.
///
/// It requires the [`fold`](SwagSpan::fold) queries are given in a "monotone" order, that is both
/// the ends of `range` should be weakly increasing.
///
#[derive(Clone, PartialEq)]
pub struct SwagSpan<'a, T, Op, Identity> {
    slice: &'a [T],
    range: Range<usize>,
    front: Vec<T>,
    fold: T,
    op: Op,
    identity: Identity,
}
impl<T, Op, Identity> Debug for SwagSpan<'_, T, Op, Identity>
where
    T: Debug,
{
    fn fmt(&self, w: &mut Formatter) -> fmt::Result {
        let Self {
            slice,
            range,
            front,
            fold,
            ..
        } = self;
        w.debug_struct("SwagSpan")
            .field("slice", slice)
            .field("range", range)
            .field("front", front)
            .field("fold", fold)
            .finish()
    }
}
impl<'a, T, Op, Identity> SwagSpan<'a, T, Op, Identity>
where
    T: Clone + Debug,
    Op: Fn(T, T) -> T,
    Identity: Fn() -> T,
{
    /// Makes a new `SwagSpan` referencing the `slice` with range `0..0`.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use swag::SwagSpan;
    ///
    /// let mut swag = SwagSpan::new(&[10, 20], std::ops::Add::add, || 0);
    ///
    /// assert_eq!(swag.fold(..), 30);
    /// ```
    pub fn new(slice: &'a [T], op: Op, identity: Identity) -> Self {
        Self {
            slice,
            range: 0..0,
            front: Vec::new(),
            fold: identity(),
            op,
            identity,
        }
    }

    /// Returns `slice[range]`.
    ///
    /// It requires that the query is given in a "monotone" order. [See the struct level
    /// documuent.](SwagSpan)
    ///
    /// # Panics
    ///
    /// - if `range.start > range.end` (reversed empty range)
    /// - or if `len <= range.end` (out of range)
    /// - or if query is not monotone.
    ///
    /// # Examples
    ///
    /// ```
    /// use swag::SwagSpan;
    ///
    /// let mut swag = SwagSpan::new(
    ///     &[10, 11, 12, 13, 14, 15],
    ///     std::ops::Add::add,
    ///     || 0
    /// );
    ///
    /// assert_eq!(swag.fold(..2), 21);
    /// assert_eq!(swag.fold(..3), 33);
    /// assert_eq!(swag.fold(1..3), 23);
    /// assert_eq!(swag.fold(1..), 65);
    /// assert_eq!(swag.fold(3..=5), 42);
    /// ```
    pub fn fold(&mut self, range: impl RangeBounds<usize>) -> T {
        let Range { start, end } = open(range, self.slice.len());
        assert!(
            start <= end,
            "Attempted to fold a swag by a reversed empty range {:?}.",
            start..end
        );
        assert!(
            start <= end,
            "Attempted to fold a swag by a range {:?}, but out of range. Length is {:?}",
            start..end,
            self.slice.len()
        );
        assert!(
            start <= self.range.start || self.range.end <= end,
            "Attempted to fold a swag by a range {:?}, but the previous folding range was {:?}.",
            start..end,
            &self.range,
        );
        self.locate(start, end);
        self.fold_here()
    }

    // Calculate `slice[range]`.
    fn fold_here(&self) -> T {
        let Self {
            front, op, fold, ..
        } = self;
        front
            .last()
            .map_or_else(|| fold.clone(), |f| op(f.clone(), fold.clone()))
    }

    // Repeat `extend` and `shrink` to move `range` to `s..t`
    fn locate(&mut self, s: usize, e: usize) {
        while e != self.range.end {
            self.extend();
        }
        while s != self.range.start {
            self.shrink();
        }
    }

    // Almost the same implementation as `SwagQueue::push`.
    fn extend(&mut self) {
        let Self {
            slice,
            range: Range { end, .. },
            fold,
            op,
            ..
        } = self;
        *fold = op(fold.clone(), slice[*end].clone());
        *end += 1;
    }

    // Almost the same implementation as `SwagQueue::pop`.
    fn shrink(&mut self) {
        let Self {
            front,
            slice,
            range: Range { start, end },
            op,
            identity,
            fold,
            ..
        } = self;
        if front.is_empty() {
            for x in slice[*start..*end].iter().rev().cloned() {
                let x = if let Some(y) = front.last() {
                    op(x, y.clone())
                } else {
                    x
                };
                front.push(x);
            }
            *fold = identity();
        }
        *start += 1;
        front.pop().unwrap();
    }
}

fn open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
    (match range.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    })..match range.end_bound() {
        Bound::Excluded(&x) => x,
        Bound::Included(&x) => x + 1,
        Bound::Unbounded => len,
    }
}

#[cfg(test)]
mod tests {
    use {super::*, rand::prelude::*, std::ops::Add};

    #[test]
    #[should_panic]
    fn test_panics_if_out_of_range() {
        let mut swag = SwagSpan::new(&[], Add::add, || 0);
        swag.fold(0..1);
    }

    #[test]
    #[should_panic]
    fn test_panics_if_illegal_range() {
        let mut swag = SwagSpan::new(&[0], Add::add, || 0);
        #[allow(clippy::reversed_empty_ranges)]
        swag.fold(1..0);
    }

    #[test]
    #[should_panic]
    fn test_panics_if_start_is_not_monotone() {
        let mut swag = SwagSpan::new(&[0, 1, 2], Add::add, || 0);
        swag.fold(1..2);
        swag.fold(0..3);
    }

    #[test]
    #[should_panic]
    fn test_panics_if_end_is_not_monotone() {
        let mut swag = SwagSpan::new(&[0, 1, 2], Add::add, || 0);
        swag.fold(0..3);
        swag.fold(1..2);
    }

    #[test]
    fn test_rand_sliding_strcat() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..5 {
            let n = rng.gen_range(1..20);
            let k = rng.gen_range(1..=n);
            let a = rand::distributions::Alphanumeric
                .sample_iter(&mut rng)
                .map(|c| c.to_string())
                .take(n)
                .collect::<Vec<_>>();
            let mut test = Test::new(
                &a,
                |s, t| s.chars().chain(t.chars()).collect::<String>(),
                String::new,
            );
            for i in 0..=n - k {
                test.fold(i..i + k);
            }
        }
    }

    struct Test<'a, T, Op, Identity> {
        swag: SwagSpan<'a, T, Op, Identity>,
    }
    impl<'a, T, Op, Identity> Test<'a, T, Op, Identity>
    where
        T: Clone + Debug + PartialEq,
        Op: Fn(T, T) -> T,
        Identity: Fn() -> T,
    {
        pub fn new(slice: &'a [T], op: Op, identity: Identity) -> Self {
            Self {
                swag: SwagSpan::new(slice, op, identity),
            }
        }

        pub fn fold(&mut self, range: Range<usize>) {
            println!("fold({:?}), now = {:?}", &range, &self.swag);
            let result = self.swag.fold(range.clone());
            let expected = self.swag.slice[range]
                .iter()
                .cloned()
                .fold((self.swag.identity)(), |x, y| (self.swag.op)(x, y));
            assert_eq!(result, expected);
        }
    }
}
