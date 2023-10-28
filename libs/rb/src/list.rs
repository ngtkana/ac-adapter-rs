#![allow(dead_code)]
use crate::tree::Callback;
use crate::tree::Color;
use crate::tree::Node;
use crate::tree::Ptr;
use crate::tree::Tree;
use crate::Op;
use std::marker::PhantomData;
use std::mem;
use std::ops::Bound;
use std::ops::RangeBounds;

/// A list based on a red-black tree.
pub struct List<O: Op> {
    tree: Tree<ListCallback<O>>,
}
impl<O: Op> List<O> {
    /// Create a new empty list.
    pub fn new() -> Self { Self::default() }

    /// Returns the length of the list.
    pub fn len(&self) -> usize {
        match self.tree.root {
            Some(p) => p.data.len,
            None => 0,
        }
    }

    /// Returns `true` if the list is empty.
    pub fn is_empty(&self) -> bool { self.tree.root.is_none() }

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
        self.tree.max_right(x, |data| {
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
        self.tree.max_right(x, |data| {
            let new_acc = O::mul(&data.value, &acc);
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
        self.tree.min_left(x, |data| {
            let new_acc = O::mul(&acc, &data.value);
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
        let position = self.get_leaf_ptr(i).map(|p| (p, i < self.len()));
        let leaf = Ptr::new_leaf(Data::new(x));
        self.tree.insert(position, leaf, Data::mul);
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

    /// Split the list into two at the given index.
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

    /// Returns the `i`th leaf pointer if `i < self.data.len`, and the rightmost leaf pointer otherwise or `None` if the list is empty.
    fn get_leaf_ptr(&self, mut i: usize) -> Option<Ptr<ListCallback<O>>> {
        Some(self.tree.root?.binary_search_for_leaf(|b| {
            let left_len = b.left.unwrap().data.len;
            if i < left_len {
                true
            } else {
                i -= left_len;
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

impl<O: Op> Default for List<O> {
    fn default() -> Self {
        Self {
            tree: Tree::default(),
        }
    }
}

impl<O: Op> FromIterator<O::Value> for List<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut leaves = iter
            .into_iter()
            .map(|value| Ptr::new_leaf(Data::new(value)))
            .collect::<Vec<_>>();
        List {
            tree: Tree::from_slice_of_leaves(&mut leaves, Data::mul),
        }
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
    use crate::tree::test_util;
    use crate::tree::test_util::validate;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;
    use std::iter;

    const P: u64 = 998244353;

    #[derive(Clone, Copy, Debug, PartialEq)]
    enum Concat {}
    impl Op for Concat {
        type Lazy = ();
        type Value = Vec<u64>;

        fn mul(left: &Self::Value, right: &Self::Value) -> Self::Value {
            left.iter().chain(right.iter()).copied().collect()
        }

        fn compose(_: &mut Self::Lazy, _: &Self::Lazy) {}

        fn identity() -> Self::Lazy {}

        fn apply(_: &mut Self::Value, _: &Self::Lazy) {}
    }
    type C = ListCallback<Concat>;

    fn random_list(rng: &mut StdRng, black_height: u8) -> List<Concat> {
        fn value(rng: &mut StdRng) -> Data<Concat> { Data::new(vec![rng.gen_range(0..20)]) }
        fn mul(left: Ptr<C>, right: Ptr<C>) -> Data<Concat> {
            Data {
                len: left.data.len + right.data.len,
                value: Concat::mul(&left.data.value, &right.data.value),
                lazy: (),
            }
        }
        let tree = test_util::random_tree(rng, black_height, value, Data::mul);
        test_util::validate(&tree);
        List { tree }
    }

    fn to_vec<O: Op>(list: &List<O>) -> Vec<O::Value>
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
        if let Some(root) = list.tree.root {
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
    fn test_from_iter() {
        fn height(p: Ptr<C>) -> u8 {
            if p.is_leaf() {
                1
            } else {
                height(p.left.unwrap()).max(height(p.right.unwrap())) + 1
            }
        }
        for n in 0..100 {
            let list = (0..n).map(|x| vec![x]).collect::<List<Concat>>();
            validate(&list.tree);
            let vec = (0..n).map(|x| vec![x]).collect::<Vec<_>>();
            assert_eq!(to_vec(&list), vec);
            let height = list.tree.root.map_or(0, height);
            let expected_height = if n == 0 { 0 } else { (2 * n - 1).ilog2() as u8 + 1 };
            assert_eq!(
                height,
                expected_height,
                "Expected height for length {} is {}, but the actual height is {}:\n{}\n",
                n,
                expected_height,
                height,
                test_util::format(&list.tree),
            );
        }
    }

    #[test]
    fn test_fold() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let black_height = rng.gen_range(0..=6);
            let list = random_list(&mut rng, black_height);
            let vec = to_vec(&list);
            for _ in 0..200 {
                let (start, end) = choose2_with_reputation(&mut rng, 0..=list.len());
                let result = list.fold(start..end);
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
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let black_height = rng.gen_range(0..=6);
            let list = random_list(&mut rng, black_height);
            for _ in 0..200 {
                // max_right
                {
                    let start = rng.gen_range(0..=list.len());
                    let acc = rng.gen_range(0..=list.len());
                    let result = list.max_right(start, |s| s.len() <= acc);
                    let expected = (start + acc).min(list.len());
                    assert_eq!(result, expected);
                }
                // min_left
                {
                    let end = rng.gen_range(0..=list.len());
                    let acc = rng.gen_range(0..=list.len());
                    let result = list.min_left(end, |s| s.len() <= acc);
                    let expected = end.saturating_sub(acc);
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
            let mut list = List::<Concat>::new();
            let mut vec = Vec::new();
            for _ in 0..200 {
                match rng.gen_range(0..=max_length) {
                    // Insert
                    x if vec.len() <= x => {
                        let i = rng.gen_range(0..=vec.len());
                        let value = vec![rng.gen_range(0..20)];
                        list.insert(i, value.clone());
                        vec.insert(i, value.clone());
                    }
                    // Remove
                    x if x < vec.len() => {
                        if vec.is_empty() {
                            continue;
                        }
                        let i = rng.gen_range(0..vec.len());
                        let result = list.remove(i);
                        let expected = vec.remove(i);
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
                assert_eq!(&to_vec(&list), &vec);
                test_util::validate(&list.tree);
            }
        }
    }

    #[test]
    fn test_append() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = 8;
            let mut lists = iter::repeat_with(|| {
                let h = rng.gen_range(0..=6);
                random_list(&mut rng, h)
            })
            .take(n)
            .collect::<Vec<_>>();
            let mut vecs = lists.iter().map(to_vec).collect::<Vec<_>>();
            while lists.len() > 1 {
                let i = rng.gen_range(0..=lists.len() - 2);
                let list = {
                    let mut lhs = lists.remove(i);
                    let mut rhs = lists.remove(i);
                    lhs.append(&mut rhs);
                    assert!(rhs.is_empty());
                    validate(&lhs.tree);
                    lhs
                };
                let vec = {
                    let mut lhs = vecs.remove(i);
                    let mut rhs = vecs.remove(i);
                    lhs.append(&mut rhs);
                    assert!(rhs.is_empty());
                    lhs
                };
                assert_eq!(to_vec(&list), vec);
                lists.insert(i, list);
                vecs.insert(i, vec);
            }
        }
    }

    #[test]
    fn test_split_off() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let h = rng.gen_range(0..=6);
            let mut lists = vec![random_list(&mut rng, h)];
            let mut vecs = vec![to_vec(&lists[0])];
            for _ in 0..20 {
                let i = rng.gen_range(0..lists.len());
                let j = rng.gen_range(0..=lists[i].len());
                let list = lists[i].split_off(j);
                let vec = vecs[i].split_off(j);
                validate(&lists[i].tree);
                validate(&list.tree);
                assert_eq!((&to_vec(&lists[i]), &to_vec(&list)), (&vecs[i], &vec));
                lists.insert(i + 1, list);
                vecs.insert(i + 1, vec);
            }
        }
    }
}
