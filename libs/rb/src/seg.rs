#![allow(dead_code)]
use crate::tree::Callback;
use crate::tree::Color;
use crate::tree::Node;
use crate::tree::Ptr;
use crate::tree::Tree;
use crate::Op;
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops::Bound;
use std::ops::RangeBounds;

/// A seg based on a red-black tree.
pub struct Seg<O: Op> {
    tree: Tree<ListCallback<O>>,
}
impl<O: Op> Seg<O> {
    /// Create a new empty seg.
    pub fn new() -> Self { Self::default() }

    /// Returns the length of the seg.
    pub fn len(&self) -> usize {
        match self.tree.root {
            Some(p) => p.data.len,
            None => 0,
        }
    }

    /// Returns `true` if the seg is empty.
    pub fn is_empty(&self) -> bool { self.tree.root.is_none() }

    /// Returns an iterator over the seg.
    pub fn iter(&self) -> Iter<'_, O> {
        Iter {
            marker: PhantomData,
            start: self.get_leaf_ptr(0),
            end: self.get_leaf_ptr(self.len()),
            len: self.len(),
        }
    }

    /// Folds the `range` into a single value by `O::mul`.
    /// If `range` is empty, returns `None`.
    ///
    /// # Panics
    ///
    /// Panics if `range` is out of bounds.
    ///
    /// TODO: Move the pointer-based implementation to `tree.rs`.
    pub fn fold<B: RangeBounds<usize>>(&self, range: B) -> Option<O::Value>
    where
        O::Value: Clone,
    {
        let (mut start, end) = into_range(range, self.len());
        assert!(start <= end && end <= self.len(), "index out of bounds");
        (start < end).then_some(())?;

        let x = self.get_leaf_ptr(start).unwrap();
        let mut acc = x.data.value.clone();
        start += 1;
        if start == end {
            return Some(acc);
        }
        x.max_right(|data| {
            let new_acc = O::mul(&acc, &data.value);
            let new_start = start + data.len;
            if new_start <= end {
                acc = new_acc;
                start = new_start;
                true
            } else {
                false
            }
        });
        Some(acc)
    }

    /// Returns the maximum `i` such that `f(self.fold(0..i))` is `true`.
    pub fn max_right<F>(&self, mut start: usize, mut f: F) -> usize
    where
        O::Value: Clone,
        F: FnMut(&O::Value) -> bool,
    {
        assert!(start <= self.len(), "index out of bounds");
        if start == self.len() {
            return start;
        }

        let x = self.get_leaf_ptr(start).unwrap();
        if !f(&x.data.value) {
            return start;
        }
        start += 1;
        let mut acc = x.data.value.clone();
        x.max_right(|data| {
            let new_acc = O::mul(&acc, &data.value);
            if f(&new_acc) {
                start += data.len;
                acc = new_acc;
                true
            } else {
                false
            }
        });
        start
    }

    /// Returns the minimum `i` such that `f(self.fold(i..self.len()))` is `true`.
    pub fn min_left<F>(&self, mut end: usize, mut f: F) -> usize
    where
        O::Value: Clone,
        F: FnMut(&O::Value) -> bool,
    {
        assert!(end <= self.len(), "index out of bounds");
        if end == 0 {
            return end;
        }

        let x = self.get_leaf_ptr(end - 1).unwrap();
        if !f(&x.data.value) {
            return end;
        }
        end -= 1;
        let mut acc = x.data.value.clone();
        x.min_left(|data| {
            let new_acc = O::mul(&data.value, &acc);
            if f(&new_acc) {
                end -= data.len;
                acc = new_acc;
                true
            } else {
                false
            }
        });
        end
    }

    /// Insert a value at the `i`th position.
    ///
    /// # Panics
    ///
    /// Panics if `i > self.data.len`.
    pub fn insert(&mut self, i: usize, x: O::Value) {
        assert!(i <= self.len(), "index out of bounds");
        let position = self.get_leaf_ptr(i).map(|p| (p, i == self.len()));
        self.tree
            .insert(position, Ptr::new_leaf(Data::new(x)), Data::mul);
    }

    /// Remove the `i`th value and return it.
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.data.len`.
    pub fn remove(&mut self, i: usize) -> O::Value {
        assert!(i < self.len(), "index out of bounds");
        let p = self.get_leaf_ptr(i).unwrap();
        self.tree.remove(p);
        p.free().value
    }

    /// Append all the elements in `other`, leaving `other` empty.
    pub fn append(&mut self, other: &mut Self) {
        let other = &mut other.tree;
        self.tree.append(other, Data::mul);
    }

    /// Split the seg into two at the given index.
    pub fn split_off(&mut self, mut at: usize) -> Self {
        assert!(at <= self.len(), "index out of bounds");
        if at == 0 {
            return mem::take(self);
        }
        if at == self.len() {
            return Self::default();
        }
        let mut x = self.tree.root.unwrap();
        let mut black_height = self.tree.black_height;
        loop {
            let left_len = x.left.unwrap().data.len;
            if x.color == Color::Black {
                black_height -= 1;
            }
            x = match at.cmp(&left_len) {
                std::cmp::Ordering::Less => x.left.unwrap(),
                std::cmp::Ordering::Equal => break,
                std::cmp::Ordering::Greater => {
                    at -= left_len;
                    x.right.unwrap()
                }
            };
        }
        Self {
            tree: self.tree.split_off(x, black_height, Data::mul),
        }
    }

    /// Returns the `i`th leaf pointer if `i < self.data.len`, and the rightmost leaf pointer otherwise or `None` if the seg is empty.
    fn get_leaf_ptr(&self, mut i: usize) -> Option<Ptr<ListCallback<O>>> {
        Some(self.tree.root?.binary_search_for_leaf(|b| {
            let left_len = b.left.unwrap().data.len;
            if left_len <= i {
                i -= left_len;
                true
            } else {
                false
            }
        }))
    }
}

fn into_range<B: RangeBounds<usize>>(range: B, len: usize) -> (usize, usize) {
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end + 1,
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };
    (start, end)
}

impl<O: Op> Default for Seg<O> {
    fn default() -> Self {
        Self {
            tree: Tree::default(),
        }
    }
}

impl<O: Op> FromIterator<O::Value> for Seg<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut leaves = iter
            .into_iter()
            .map(|value| Ptr::new_leaf(Data::new(value)))
            .collect::<Vec<_>>();
        Seg {
            tree: Tree::from_slice_of_leaves(&mut leaves, Data::mul),
        }
    }
}

/// An iterator over the seg.
pub struct Iter<'a, O: Op> {
    marker: PhantomData<&'a O>,
    start: Option<Ptr<ListCallback<O>>>,
    end: Option<Ptr<ListCallback<O>>>,
    len: usize,
}
impl<'a, O: Op> Iterator for Iter<'a, O> {
    type Item = &'a O::Value;

    fn next(&mut self) -> Option<Self::Item> {
        let start = self.start?;
        self.len -= 1;
        if self.len == 0 {
            self.start = None;
            self.end = None;
        } else {
            self.start = start.max_right(|_| false);
        }
        Some(&start.as_longlife_ref().data.value)
    }

    /// `advance_by` is better, but it is unstable now
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if n == 0 {
            return self.next();
        }
        if self.len <= n {
            self.start = None;
            self.end = None;
            self.len = 0;
            None
        } else {
            self.len -= n + 1;
            let mut i = n - 1;
            let start = self
                .start
                .unwrap()
                .max_right(|data| {
                    if i < data.len {
                        false
                    } else {
                        i -= data.len;
                        true
                    }
                })
                .unwrap();
            if self.len == 0 {
                self.start = None;
                self.end = None;
            } else {
                self.start = Some(start.max_right(|_| false).unwrap());
            }
            Some(&start.as_longlife_ref().data.value)
        }
    }
}
impl<'a, O: Op> DoubleEndedIterator for Iter<'a, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let end = self.end?;
        let result = &end.as_longlife_ref().data.value;
        self.len -= 1;
        if self.len == 0 {
            self.start = None;
            self.end = None;
        } else {
            self.end = end.min_left(|_| false);
        }
        Some(result)
    }

    /// `advance_back_by` is better, but it is unstable now
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if n == 0 {
            return self.next_back();
        }
        if self.len <= n {
            self.start = None;
            self.end = None;
            self.len = 0;
            None
        } else {
            self.len -= n + 1;
            let mut i = n - 1;
            let end = self
                .end
                .unwrap()
                .min_left(|data| {
                    if i < data.len {
                        false
                    } else {
                        i -= data.len;
                        true
                    }
                })
                .unwrap();
            if self.len == 0 {
                self.start = None;
                self.end = None;
            } else {
                self.end = Some(end.min_left(|_| false).unwrap());
            }
            Some(&end.as_longlife_ref().data.value)
        }
    }
}
impl<'a, O: Op> IntoIterator for &'a Seg<O> {
    type IntoIter = Iter<'a, O>;
    type Item = &'a O::Value;

    fn into_iter(self) -> Self::IntoIter { self.iter() }
}

impl<O: Op> fmt::Debug for Seg<O>
where
    O::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Data<O: Op> {
    len: usize,
    value: O::Value,
    lazy: O::Lazy,
}
impl<O: Op> Data<O> {
    fn new(value: O::Value) -> Self {
        Self {
            len: 1,
            value,
            lazy: O::identity(),
        }
    }

    fn mul(left: &Self, right: &Self) -> Self {
        Self {
            len: left.len + right.len,
            value: O::mul(&left.value, &right.value),
            lazy: O::identity(),
        }
    }
}

struct ListCallback<O> {
    marker: PhantomData<O>,
}
impl<O: Op> Callback for ListCallback<O> {
    type Data = Data<O>;

    fn update(x: &mut Node<Self>) {
        debug_assert!(O::is_identity(&x.data.lazy));
        x.data.len = x.left.unwrap().data.len + x.right.unwrap().data.len;
        x.data.value = O::mul(&x.left.unwrap().data.value, &x.right.unwrap().data.value);
    }

    fn push(x: &mut Node<Self>) {
        if !O::is_identity(&x.data.lazy) {
            let lazy = O::swap_with_identity(&mut x.data.lazy);
            O::apply(&mut x.data.value, &lazy);
            if !x.is_leaf() {
                O::compose(&mut x.left.unwrap().data.lazy, &lazy);
                O::compose(&mut x.right.unwrap().data.lazy, &lazy);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util;
    use crate::test_util::Concat;
    use itertools::assert_equal;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;
    use std::iter;

    fn random_seg(rng: &mut StdRng, black_height: u8) -> Seg<Concat> {
        fn value(rng: &mut StdRng) -> Data<Concat> { Data::new(vec![rng.gen_range(0..20)]) }
        let tree = test_util::random_tree(rng, black_height, value, Data::mul);
        test_util::validate_with_data(&tree);
        Seg { tree }
    }

    fn to_vec<O: Op>(seg: &Seg<O>) -> Vec<O::Value>
    where
        O::Value: Clone,
    {
        fn to_vec<O: Op>(p: Ptr<ListCallback<O>>, result: &mut Vec<O::Value>)
        where
            O::Value: Clone,
        {
            if p.is_leaf() {
                result.push(p.data.value.clone());
            } else {
                to_vec(p.left.unwrap(), result);
                to_vec(p.right.unwrap(), result);
            }
        }
        let mut result = Vec::new();
        if let Some(root) = seg.tree.root {
            to_vec(root, &mut result);
        }
        result
    }

    // Choose two numbers from `range` with reputation.
    fn choose2_with_reputation(rng: &mut StdRng, range: impl RangeBounds<usize>) -> (usize, usize) {
        let (start, end) = into_range(range, !0);
        let mut i = rng.gen_range(start..end + 1);
        let mut j = rng.gen_range(start..end);
        if i > j {
            std::mem::swap(&mut i, &mut j);
            j -= 1;
        }
        assert!(start <= i && i <= j && j < end);
        (i, j)
    }

    #[test]
    fn test_iter() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..10 {
            let h = rng.gen_range(0..=6);
            let seg = random_seg(&mut rng, h);
            let vec = to_vec(&seg);
            assert_equal(&seg, &vec);
            assert_equal(seg.iter().rev(), vec.iter().rev());

            // Call `next` and `next_back` at random
            {
                let mut iter = seg.iter();
                let mut vec_iter = vec.iter();
                for _ in 0..100 {
                    match rng.gen_range(0..=1) {
                        0 => assert_eq!(iter.next(), vec_iter.next()),
                        1 => assert_eq!(iter.next_back(), vec_iter.next_back()),
                        _ => unreachable!(),
                    }
                }
            }

            // Call `nth` and `nth_back` at random
            {
                let mut iter = seg.iter();
                let mut vec_iter = vec.iter();
                for _ in 0..100 {
                    let n = rng.gen_range(0..=seg.len());
                    assert_eq!(iter.nth(n), vec_iter.nth(n));
                    assert_eq!(iter.nth_back(n), vec_iter.nth_back(n));
                }
            }

            // Applications: `step`
            if h != 0 {
                let n = rng.gen_range(1..=seg.len());
                assert_equal(seg.iter().step_by(n), vec.iter().step_by(n));
                assert_equal(seg.iter().rev().step_by(n), vec.iter().rev().step_by(n));
            }
        }
    }

    #[test]
    fn test_from_iter() {
        fn height<C: Callback>(p: Ptr<C>) -> u8 {
            if p.is_leaf() {
                1
            } else {
                height(p.left.unwrap()).max(height(p.right.unwrap())) + 1
            }
        }
        for n in 0..100 {
            let seg = (0..n).map(|x| vec![x]).collect::<Seg<Concat>>();
            test_util::validate_with_data(&seg.tree);
            let vec = (0..n).map(|x| vec![x]).collect::<Vec<_>>();
            assert_eq!(to_vec(&seg), vec);
            let height = seg.tree.root.map_or(0, height);
            let expected_height = if n == 0 { 0 } else { (2 * n - 1).ilog2() as u8 + 1 };
            assert_eq!(
                height, expected_height,
                "Expected height for length {} is {}, but the actual height is {}:\n{:?}\n",
                n, expected_height, height, &seg.tree,
            );
        }
    }

    #[test]
    fn test_fold() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let black_height = rng.gen_range(0..=6);
            let seg = random_seg(&mut rng, black_height);
            let vec = to_vec(&seg);
            for _ in 0..200 {
                let (start, end) = choose2_with_reputation(&mut rng, 0..=seg.len());
                let result = seg.fold(start..end);
                let expected = vec[start..end].iter().fold(None::<Vec<u64>>, |value, x| {
                    Some(match value {
                        None => x.clone(),
                        Some(value) => Concat::mul(&value, &x),
                    })
                });
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_max_right_min_left() {
        #[derive(Clone, Copy, Debug, PartialEq)]
        enum Affine {}
        impl Op for Affine {
            type Lazy = ();
            type Value = (u64, u64);

            fn mul(&(a, b): &Self::Value, &(c, d): &Self::Value) -> Self::Value {
                let a = a as u128;
                let b = b as u128;
                let c = c as u128;
                let d = d as u128;
                let mut e = a * c;
                let mut f = a * d + b;
                e += f >> 64;
                f &= (1 << 64) - 1;
                if (u64::MAX as u128) < e {
                    (u64::MAX, u64::MAX)
                } else {
                    (e as u64, f as u64)
                }
            }

            fn apply(_: &mut Self::Value, _: &Self::Lazy) {}

            fn compose(_: &mut Self::Lazy, _: &Self::Lazy) {}

            fn identity() -> Self::Lazy {}
        }
        fn value(rng: &mut StdRng) -> Data<Affine> {
            Data::new((rng.gen_range(1..4), rng.gen_range(0..4)))
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let black_height = rng.gen_range(0..=6);
            let tree = test_util::random_tree(&mut rng, black_height, value, Data::mul);
            test_util::validate_with_data(&tree);
            let seg = Seg { tree };
            let vec = to_vec(&seg);

            let sum = seg.fold(..).unwrap_or((1, 0));

            for _ in 0..200 {
                // max_right
                {
                    let start = rng.gen_range(0..=seg.len());
                    let acc = (rng.gen_range(0..=sum.0), rng.gen_range(0..=sum.1));
                    let result = seg.max_right(start, |&s| s <= acc);
                    let expected = start
                        + vec[start..]
                            .iter()
                            .scan((1, 0), |acc, &x| {
                                *acc = Affine::mul(acc, &x);
                                Some(*acc)
                            })
                            .take_while(|&a| a <= acc)
                            .count();
                    assert_eq!(result, expected);
                }
                // min_left
                {
                    let end = rng.gen_range(0..=seg.len());
                    let acc = (rng.gen_range(0..=sum.0), rng.gen_range(0..=sum.1));
                    let result = seg.min_left(end, |&s| s <= acc);
                    let expected = end
                        - vec[..end]
                            .iter()
                            .rev()
                            .scan((1, 0), |acc, &x| {
                                *acc = Affine::mul(&x, acc);
                                Some(*acc)
                            })
                            .take_while(|&a| a <= acc)
                            .count();
                    assert_eq!(result, expected);
                }
            }
        }
    }

    #[rstest]
    #[case(3)]
    #[case(40)]
    #[case(200)]
    fn test_insert_remove(#[case] max_length: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut seg = Seg::<Concat>::new();
            let mut vec = Vec::new();
            for _ in 0..200 {
                match rng.gen_range(0..=max_length) {
                    // Insert
                    x if vec.len() <= x => {
                        let i = rng.gen_range(0..=vec.len());
                        let value = vec![rng.gen_range(0..20)];
                        seg.insert(i, value.clone());
                        vec.insert(i, value.clone());
                    }
                    // Remove
                    x if x < vec.len() => {
                        if vec.is_empty() {
                            continue;
                        }
                        let i = rng.gen_range(0..vec.len());
                        let result = seg.remove(i);
                        let expected = vec.remove(i);
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
                assert_eq!(&to_vec(&seg), &vec);
                test_util::validate_with_data(&seg.tree);
            }
        }
    }

    #[test]
    fn test_append() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = 8;
            let mut segs = iter::repeat_with(|| {
                let h = rng.gen_range(0..=6);
                random_seg(&mut rng, h)
            })
            .take(n)
            .collect::<Vec<_>>();
            let mut vecs = segs.iter().map(to_vec).collect::<Vec<_>>();
            while segs.len() > 1 {
                let i = rng.gen_range(0..=segs.len() - 2);
                let seg = {
                    let mut lhs = segs.remove(i);
                    let mut rhs = segs.remove(i);
                    lhs.append(&mut rhs);
                    assert!(rhs.is_empty());
                    test_util::validate_with_data(&lhs.tree);
                    lhs
                };
                let vec = {
                    let mut lhs = vecs.remove(i);
                    let mut rhs = vecs.remove(i);
                    lhs.append(&mut rhs);
                    assert!(rhs.is_empty());
                    lhs
                };
                assert_eq!(to_vec(&seg), vec);
                segs.insert(i, seg);
                vecs.insert(i, vec);
            }
        }
    }

    #[test]
    fn test_split_off() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let h = rng.gen_range(0..=6);
            let mut segs = vec![random_seg(&mut rng, h)];
            let mut vecs = vec![to_vec(&segs[0])];
            for _ in 0..20 {
                let i = rng.gen_range(0..segs.len());
                let j = rng.gen_range(0..=segs[i].len());
                let seg = segs[i].split_off(j);
                let vec = vecs[i].split_off(j);
                test_util::validate_with_data(&segs[i].tree);
                test_util::validate_with_data(&seg.tree);
                assert_eq!((&to_vec(&segs[i]), &to_vec(&seg)), (&vecs[i], &vec));
                segs.insert(i + 1, seg);
                vecs.insert(i + 1, vec);
            }
        }
    }
}
