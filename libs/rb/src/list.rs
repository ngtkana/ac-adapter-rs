use crate::tree::Tree;
use crate::Callback;
use crate::Len;
use crate::Op;
use crate::Ptr;
use std::cmp::Ordering;
use std::marker::PhantomData;
use std::ops;
use std::ops::RangeBounds;

pub(super) struct Irreversible<O: Op> {
    marker: PhantomData<O>,
}

pub(super) struct Reversible<O: Op> {
    marker: PhantomData<O>,
}

#[allow(dead_code)]
pub(super) struct IrreversibleData<O: Op> {
    len: usize,
    value: O::Value,
    acc: O::Acc,
    #[allow(dead_code)]
    lazy: O::Action,
}
impl<O: Op> IrreversibleData<O> {
    pub(super) fn new(value: O::Value) -> Self {
        let acc = O::to_acc(&value);
        Self {
            len: 1,
            value,
            acc,
            lazy: O::identity_action(),
        }
    }
}

#[allow(dead_code)]
pub(super) struct ReversibleData<O: Op> {
    len: usize,
    value: O::Value,
    acc: O::Acc,
    #[allow(dead_code)]
    lazy: O::Action,
    reverse: bool,
}

#[allow(dead_code)]
impl<O: Op> Callback for Irreversible<O> {
    type Data = IrreversibleData<O>;

    fn push(_node: crate::Ptr<Self>) {}

    fn update(mut node: crate::Ptr<Self>) {
        let mut len = 1;
        let mut acc = O::to_acc(&node.data.value);
        if let Some(left) = node.left {
            acc = O::mul(&left.data.acc, &acc);
            len += left.data.len;
        }
        if let Some(right) = node.right {
            acc = O::mul(&acc, &right.data.acc);
            len += right.data.len;
        }
        node.data.len = len;
        node.data.acc = acc;
    }
}

#[allow(dead_code)]
impl<O: Op> Len for IrreversibleData<O> {
    fn len(&self) -> usize { self.len }
}

#[allow(dead_code)]
impl<O: Op> Callback for Reversible<O> {
    type Data = ReversibleData<O>;

    fn push(_node: crate::Ptr<Self>) {}

    fn update(mut node: crate::Ptr<Self>) {
        let mut len = 1;
        let mut acc = O::to_acc(&node.data.value);
        if let Some(left) = node.left {
            acc = O::mul(&left.data.acc, &acc);
            len += left.data.len;
        }
        if let Some(right) = node.right {
            acc = O::mul(&acc, &right.data.acc);
            len += right.data.len;
        }
        node.data.len = len;
        node.data.acc = acc;
    }
}

/// A list based on a red-black tree.
#[allow(dead_code)]
pub struct RbList<O: Op> {
    tree: Tree<Irreversible<O>>,
}
impl<O: Op> RbList<O> {
    /// Constructs a new, empty list.
    pub fn new() -> Self { Self::default() }

    /// Returns the length of the list.
    pub fn is_empty(&self) -> bool { self.tree.is_empty() }

    /// Returns the length of the list.
    pub fn len(&self) -> usize { self.tree.len() }

    /// Provides a reference to the front element, or None if the deque is empty.
    pub fn front(&self) -> Option<&O::Value> {
        self.tree.front().map(|p| &p.as_ref_longlife().data.value)
    }

    /// Returns the last element of the list.
    pub fn back(&self) -> Option<&O::Value> {
        self.tree.back().map(|p| &p.as_ref_longlife().data.value)
    }

    /// Returns the first element of the list.
    pub fn front_mut(&mut self) -> Option<&mut O::Value> {
        self.tree
            .front()
            .map(|p| &mut p.as_mut_longlife().data.value)
    }

    /// Returns the last element of the list.
    pub fn back_mut(&mut self) -> Option<&mut O::Value> {
        self.tree
            .back()
            .map(|p| &mut p.as_mut_longlife().data.value)
    }

    /// Prepends an element to `self`.
    pub fn push_front(&mut self, value: O::Value) {
        self.tree.push_front(Ptr::new(IrreversibleData::new(value)));
    }

    /// Appends an element to `self`.
    pub fn push_back(&mut self, value: O::Value) {
        self.tree.push_back(Ptr::new(IrreversibleData::new(value)));
    }

    /// Removes the first element and returns it, or `None` if the deque is empty.
    pub fn pop_front(&mut self) -> Option<O::Value> {
        self.tree.pop_front().map(|p| p.into_box().data.value)
    }

    /// Removes the last element and returns it, or `None` if the deque is empty.
    pub fn pop_back(&mut self) -> Option<O::Value> {
        self.tree.pop_back().map(|p| p.into_box().data.value)
    }

    /// Moves all elements from other into `self`, leaving `other` empty.
    pub fn append(&mut self, other: &mut Self) { self.tree.append(&mut other.tree); }

    /// Splits `self` into two at the given index.
    pub fn split_off(&mut self, index: usize) -> Self {
        let mut other = Self::new();
        other.tree = self.tree.split_off_at(index);
        other
    }

    /// Returns the index of the partition point according to the given predicate (the index of the first element of the second partition).
    pub fn partition_point<P>(&self, mut pred: P) -> usize
    where
        P: FnMut(&O::Value) -> bool,
    {
        self.tree
            .partition_point_index(|p| pred(&p.as_ref().data.value))
    }

    /// Binary searches `self` for a given element
    pub fn binary_search<F>(&self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&O::Value) -> Ordering,
    {
        self.tree.binary_search_index(|p| f(&p.as_ref().data.value))
    }

    /// Iterates over the list.
    pub fn iter(&self) -> Range<'_, O> {
        Range {
            len: self.tree.len(),
            start: self.tree.front(),
            end: self.tree.back(),
            marker: PhantomData,
        }
    }

    /// Returns the product of all the elements within the `range`.
    pub fn fold<R: RangeBounds<usize>>(&self, range: R) -> Option<O::Acc> {
        let _range = into_slice_range(self.len(), range);
        // TODO: Implement `fold()`.
        todo!()
    }
}
impl<O: Op> Drop for RbList<O> {
    fn drop(&mut self) { self.tree.drop_all_nodes(); }
}
impl<O: Op> Default for RbList<O> {
    fn default() -> Self {
        Self {
            tree: Tree::default(),
        }
    }
}
impl<O: Op> FromIterator<O::Value> for RbList<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let nodes = iter
            .into_iter()
            .map(|value| Ptr::new(IrreversibleData::new(value)))
            .collect::<Vec<_>>();
        Self {
            tree: Tree::from_slice(&nodes),
        }
    }
}
impl<O: Op> From<Vec<O::Value>> for RbList<O> {
    fn from(values: Vec<O::Value>) -> Self { values.into_iter().collect() }
}
impl<const N: usize, O: Op> From<[O::Value; N]> for RbList<O> {
    fn from(values: [O::Value; N]) -> Self { values.into_iter().collect() }
}

/// An iterator over a list.
pub struct Range<'a, O: Op> {
    len: usize,
    start: Option<Ptr<Irreversible<O>>>,
    end: Option<Ptr<Irreversible<O>>>,
    // To make sure `O` outlives `'a`.
    marker: PhantomData<&'a O>,
}

impl<'a, O: Op> Iterator for Range<'a, O> {
    type Item = &'a O::Value;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start.as_ref()?.clone();
        self.len -= 1;
        if self.len == 0 {
            self.start = None;
            self.end = None;
        } else {
            self.start = Some(start.next().unwrap());
        }
        Some(&start.as_ref_longlife().data.value)
    }

    fn size_hint(&self) -> (usize, Option<usize>) { (self.len, Some(self.len)) }

    fn count(self) -> usize { self.len }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let mut start = self.start.as_ref()?.clone();
        if n < self.len {
            start = start.advance_by(n).unwrap();
            self.len -= n + 1;
            if self.len == 0 {
                self.start = None;
                self.end = None;
            } else {
                self.start = start.next();
            }
            Some(&start.as_ref_longlife().data.value)
        } else {
            self.start = None;
            self.end = None;
            self.len = 0;
            None
        }
    }
}
impl<'a, O: Op> DoubleEndedIterator for Range<'a, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let end = self.end.as_ref()?.clone();
        self.len -= 1;
        if self.len == 0 {
            self.start = None;
            self.end = None;
        } else {
            self.end = Some(end.prev().unwrap());
        }
        Some(&end.as_ref_longlife().data.value)
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let mut end = self.end.as_ref()?.clone();
        if n < self.len {
            end = end.retreat_by(n).unwrap();
            self.len -= n + 1;
            if self.len == 0 {
                self.start = None;
                self.end = None;
            } else {
                self.end = end.prev();
            }
            Some(&end.as_ref_longlife().data.value)
        } else {
            self.start = None;
            self.end = None;
            self.len = 0;
            None
        }
    }
}

impl<'a, O: Op> ExactSizeIterator for Range<'a, O> {}

/// A list based on a red-black tree.
#[allow(dead_code)]
pub struct RbReversibleList<O: Op> {
    root: Tree<Reversible<O>>,
}

fn into_slice_range(len: usize, range: impl RangeBounds<usize>) -> ops::Range<usize> {
    use ops::Bound;
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start
            .checked_add(1)
            .unwrap_or_else(|| slice_start_index_overflow_fail()),
        Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
        Bound::Included(&end) => end
            .checked_add(1)
            .unwrap_or_else(|| slice_end_index_overflow_fail()),
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };

    // Don't bother with checking `start < end` and `end <= len`
    // since these checks are handled by `Range` impls

    start..end
}
const fn slice_start_index_overflow_fail() -> ! {
    panic!("attempted to index slice from after maximum usize");
}
const fn slice_end_index_overflow_fail() -> ! {
    panic!("attempted to index slice up to maximum usize");
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::rc::Rc;

    struct TestOp;
    impl Op for TestOp {
        type Acc = ();
        type Action = ();
        type Value = usize;

        fn mul(_lhs: &Self::Acc, _rhs: &Self::Acc) -> Self::Acc {}

        fn to_acc(_value: &Self::Value) -> Self::Acc {}

        fn apply(_value: &mut Self::Value, _lazy: &Self::Action) {}

        fn apply_acc(_acc: &mut Self::Acc, _lazy: &Self::Action) {}

        fn compose(_lhs: &Self::Action, _rhs: &Self::Action) -> Self::Action {}

        fn identity_action() -> Self::Action {}
    }

    #[test]
    fn test_drop() {
        struct RcOp;
        impl Op for RcOp {
            type Acc = ();
            type Action = ();
            type Value = Rc<()>;

            fn mul(_lhs: &Self::Acc, _rhs: &Self::Acc) -> Self::Acc {}

            fn to_acc(_value: &Self::Value) -> Self::Acc {}

            fn apply(_value: &mut Self::Value, _lazy: &Self::Action) {}

            fn apply_acc(_acc: &mut Self::Acc, _lazy: &Self::Action) {}

            fn compose(_lhs: &Self::Action, _rhs: &Self::Action) -> Self::Action {}

            fn identity_action() -> Self::Action {}
        }

        let pointer = Rc::new(());
        assert_eq!(Rc::strong_count(&pointer), 1);
        {
            let _list = std::iter::once(Rc::clone(&pointer)).collect::<RbList<RcOp>>();
            assert_eq!(Rc::strong_count(&pointer), 2);
        }
        assert_eq!(Rc::strong_count(&pointer), 1);
    }

    #[test]
    fn test_iterator() {
        let mut rng = StdRng::seed_from_u64(42);
        for len in 0..10 {
            // Test `next()`.
            let list = (0..len).collect::<RbList<TestOp>>();
            let mut iter = list.iter();
            for i in 0..len {
                assert_eq!(iter.next(), Some(&i));
                assert_eq!(iter.len(), len - i - 1); // Test `size_hint()`.
            }
            assert_eq!(iter.len(), 0); // Test `size_hint()`.
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);
            assert_eq!(iter.next(), None);

            // Test `next_back()`.
            let mut iter = list.iter();
            for i in (0..len).rev() {
                assert_eq!(iter.next_back(), Some(&i));
                assert_eq!(iter.len(), i); // Test `size_hint()`.
            }
            assert_eq!(iter.len(), 0); // Test `size_hint()`.
            assert_eq!(iter.next_back(), None);
            assert_eq!(iter.next_back(), None);
            assert_eq!(iter.next_back(), None);

            // Test `nth()`.
            for _ in 0..4 * len {
                let mut iter = list.iter();
                let n = rng.gen_range(0..=len);
                assert_eq!(iter.nth(n), Some(&n).filter(|&&i| i < len));
                assert_eq!(iter.len(), len.saturating_sub(n + 1)); // Test `size_hint()`.
                let m = rng.gen_range(0..=len);
                assert_eq!(iter.nth(m), Some(&(m + n + 1)).filter(|&&i| i < len));
                assert_eq!(iter.len(), len.saturating_sub(m + n + 2)); // Test `size_hint()`.
            }

            // Test `nth_back()`.
            for _ in 0..4 * len {
                let mut iter = list.iter();
                let n = rng.gen_range(0..=len);
                assert_eq!(iter.nth_back(n), len.checked_sub(n + 1).as_ref());
                assert_eq!(iter.len(), len.saturating_sub(n + 1)); // Test `size_hint()`.
                let m = rng.gen_range(0..=len);
                assert_eq!(iter.nth_back(m), len.checked_sub(m + n + 2).as_ref());
                assert_eq!(iter.len(), len.saturating_sub(m + n + 2)); // Test `size_hint()`.
            }
        }
    }
}
