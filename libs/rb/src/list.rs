use crate::node_ptr_eq;
use crate::tree::Tree;
use crate::Callback;
use crate::Len;
use crate::Op;
use crate::Ptr;
use std::cmp::Ordering;
use std::fmt;
use std::marker::PhantomData;
use std::ops;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Index;
use std::ops::RangeBounds;

// TODO: add `RbSortedList`?
// This problem:
// https://atcoder.jp/contests/arc033/tasks/arc033_3
//
// TODO: add .max_right()
// Example:
// https://atcoder.jp/contests/arc033/submissions/46249626

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

    /// Returns a deligated entry, which is a mutable reference to the element at the given index.
    pub fn entry(&mut self, index: usize) -> Entry<'_, O> {
        debug_assert!(index < self.len());
        Entry {
            ptr: self.tree.get_at(index),
            marker: PhantomData,
        }
    }

    /// Removes the first element and returns it, or `None` if the deque is empty.
    pub fn pop_front(&mut self) -> Option<O::Value> {
        self.tree.pop_front().map(|p| p.into_box().data.value)
    }

    /// Removes the last element and returns it, or `None` if the deque is empty.
    pub fn pop_back(&mut self) -> Option<O::Value> {
        self.tree.pop_back().map(|p| p.into_box().data.value)
    }

    /// Inserts an element at the given index.
    pub fn insert(&mut self, index: usize, value: O::Value) {
        self.tree
            .insert_at(index, Ptr::new(IrreversibleData::new(value)));
    }

    /// Removes the element at the given index.
    pub fn remove(&mut self, index: usize) -> O::Value {
        self.tree.remove_at(index).into_box().data.value
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

    /// Returns an iterator over the given range.
    pub fn range(&self, range: impl RangeBounds<usize>) -> Range<'_, O> {
        let Some((start, end)) = into_range_inclusive(self.len(), range) else {
            return Range {
                len: 0,
                start: None,
                end: None,
                marker: PhantomData,
            };
        };
        debug_assert!(start <= end);
        assert!(end < self.len());
        Range {
            len: end - start + 1,
            start: Some(self.tree.get_at(start)),
            end: Some(self.tree.get_at(end)),
            marker: PhantomData,
        }
    }

    /// Returns the product of all the elements within the `range`.
    // TODO: stop use the internal structure of `Tree` here.
    pub fn fold<R: RangeBounds<usize>>(&self, range: R) -> Option<O::Acc> {
        let (start, end) = into_range_inclusive(self.len(), range)?;
        debug_assert!(start <= end);
        assert!(
            end < self.len(),
            "Out of range: {}..={}, while len={}",
            start,
            end,
            self.len()
        );
        // Invariants:
        // * fold: [start, z]
        // * len: ]z, end]
        let mut z = self.tree.get_at(start);
        let mut fold = O::to_acc(&z.data.value);
        let mut len = end - start;
        // Search up.
        while len > 0 {
            // 1. Try to append the right subtree.
            if let Some(r) = z.right {
                if len <= r.data.len {
                    break;
                }
                fold = O::mul(&fold, &r.data.acc);
                len -= r.data.len;
            }
            // 2. Move to the first right ancestor.
            loop {
                let p = z.parent.unwrap();
                if node_ptr_eq(p.left, z) {
                    z = p;
                    break;
                }
                z = p;
            }
            // 3. Push back the value of the node.
            fold = O::mul(&fold, &O::to_acc(&z.data.value));
            len -= 1;
        }
        // Search down.
        while len > 0 {
            // 1. Move to the right.
            z = z.right.unwrap();
            // 2. Repeatedly move to the left.
            while let Some(l) = z.left {
                if l.data.len < len {
                    break;
                }
                z = l;
            }
            // 3. Append the left subtree and push front the value of the node.
            if let Some(l) = z.left {
                fold = O::mul(&fold, &l.data.acc);
                len -= l.data.len;
            }
            fold = O::mul(&fold, &O::to_acc(&z.data.value));
            len -= 1;
        }
        Some(fold)
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
impl<O: Op> fmt::Debug for RbList<O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl<O: Op> Index<usize> for RbList<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        &self.tree.get_at(index).as_ref_longlife().data.value
    }
}
impl<O: Op> PartialEq for RbList<O>
where
    O::Value: PartialEq,
{
    fn eq(&self, other: &Self) -> bool { self.iter().eq(other.iter()) }
}
impl<O: Op> Eq for RbList<O> where O::Value: Eq {}
impl<O: Op> FromIterator<O::Value> for RbList<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        Self {
            tree: iter
                .into_iter()
                .map(|value| Ptr::new(IrreversibleData::new(value)))
                .collect(),
        }
    }
}
impl<'a, O: Op> IntoIterator for &'a RbList<O> {
    type IntoIter = Range<'a, O>;
    type Item = &'a O::Value;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}
impl<O: Op> From<Vec<O::Value>> for RbList<O> {
    fn from(values: Vec<O::Value>) -> Self { values.into_iter().collect() }
}
impl<const N: usize, O: Op> From<[O::Value; N]> for RbList<O> {
    fn from(values: [O::Value; N]) -> Self { values.into_iter().collect() }
}

/// An entry in a list.
/// The node and its ancestors are updated when the entry is dropped.
pub struct Entry<'a, O: Op> {
    ptr: Ptr<Irreversible<O>>,
    marker: PhantomData<&'a O>,
}
impl<'a, O: Op> Drop for Entry<'a, O> {
    fn drop(&mut self) {
        self.ptr.update();
        self.ptr.update_ancestors();
    }
}
impl<'a, O: Op> Deref for Entry<'a, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target { &self.ptr.as_ref_longlife().data.value }
}
impl<'a, O: Op> DerefMut for Entry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.ptr.as_mut_longlife().data.value }
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
        let start = self.start?;
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
        let mut start = self.start?;
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
        let end = self.end?;
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
        let mut end = self.end?;
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

/// Converts a range to a range inclusive.
/// If the range is invalid, returns `None`.
fn into_range_inclusive(len: usize, range: impl RangeBounds<usize>) -> Option<(usize, usize)> {
    use ops::Bound;
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start + 1,
        Bound::Unbounded => 0,
    };

    let end = match range.end_bound() {
        Bound::Included(&end) => end,
        Bound::Excluded(&end) => end.checked_sub(1)?,
        Bound::Unbounded => len.checked_sub(1)?,
    };
    (start <= end).then_some(())?;
    Some((start, end))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;
    use std::iter::repeat_with;
    use std::rc::Rc;

    struct ConcatOp;
    impl Op for ConcatOp {
        type Acc = String;
        type Action = ();
        type Value = char;

        fn mul(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc {
            lhs.chars().chain(rhs.chars()).collect()
        }

        fn to_acc(value: &Self::Value) -> Self::Acc { value.to_string() }

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
        struct UsizeOp;
        impl Op for UsizeOp {
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

        let mut rng = StdRng::seed_from_u64(42);
        for len in 0..10 {
            // Test `next()`.
            let list = (0..len).collect::<RbList<UsizeOp>>();
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

            // Test `range()`
            for _ in 0..4 * len {
                let start = rng.gen_range(0..=len);
                let end = rng.gen_range(0..=len);
                let (start, end) = (start.min(end), start.max(end));
                let result = list.range(start..end).copied().collect::<Vec<_>>();
                let expected = (start..end).collect::<Vec<_>>();
                assert_eq!(result, expected);
            }
        }
    }

    #[rstest]
    #[case(0.1)]
    #[case(0.5)]
    #[case(0.9)]
    fn test_insert_remove_fold_random(#[case] remove_ratio: f64) {
        let mut rng = StdRng::seed_from_u64(42);
        let mut list = RbList::<ConcatOp>::new();
        for _ in 0..200 {
            // Remove
            if rng.gen_bool(remove_ratio) && !list.is_empty() {
                let index = rng.gen_range(0..list.len());
                list.tree.remove_at(index);
            }
            // Insert
            else {
                let index = rng.gen_range(0..=list.len());
                list.insert(index, rng.gen_range('a'..='z'));
            }
            // Fold
            let start = rng.gen_range(0..=list.len());
            let end = rng.gen_range(0..=list.len());
            let (start, end) = (start.min(end), start.max(end));
            let expected = list.range(start..end).collect::<String>();
            let result = list.fold(start..end).unwrap_or_default();
            assert_eq!(result, expected, "{:?}.fold({}..{})", &list, start, end,);
        }
    }

    #[test]
    // https://atcoder.jp/contests/soundhound2018-summer-final-open/tasks/soundhound2018_summer_final_e
    fn test_hash_swapping() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = 5;
            let mut s = repeat_with(|| rng.gen_range(b'a'..=b'z') as char)
                .take(n)
                .collect::<String>();
            let mut list = s.chars().collect::<RbList<ConcatOp>>();
            for _ in 0..100 {
                // Rebuild
                {
                    let mut l = rng.gen_range(0..n - 1);
                    let mut r = rng.gen_range(0..n);
                    if l >= r {
                        std::mem::swap(&mut l, &mut r);
                        r += 1;
                    }
                    // String
                    {
                        let i2 = s.split_off(r);
                        let i1 = s.split_off(l);
                        s.push_str(&i1);
                        s.push_str(&i2);
                    }
                    // Tree
                    {
                        let mut list2 = list.split_off(r);
                        let mut list1 = list.split_off(l);
                        list.append(&mut list1);
                        list.append(&mut list2);
                    }
                }
                assert_eq!(list.iter().collect::<String>(), s);
                // Fold
                for _ in 0..10 {
                    let mut l = rng.gen_range(0..n - 1);
                    let mut r = rng.gen_range(0..n);
                    if l >= r {
                        std::mem::swap(&mut l, &mut r);
                        r += 1;
                    }
                    let ans = list.fold(l..r).unwrap_or_default();
                    let expected = s.chars().skip(l).take(r - l).collect::<String>();
                    assert_eq!(ans, expected);
                }
            }
        }
    }
}
