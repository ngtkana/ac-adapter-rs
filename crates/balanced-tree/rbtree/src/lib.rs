mod detail;

use {
    detail::{Nil, Root},
    std::{
        fmt::{self, Debug},
        hash::{Hash, Hasher},
        iter::FromIterator,
        marker::PhantomData,
        mem::take,
        ops::{Bound, Range, RangeBounds},
    },
};

#[derive(Clone)]
pub struct RbTree<T, O: Op<Value = T> = Nop<T>> {
    root: Option<Root<T, O>>,
    __marker: PhantomData<fn(O) -> O>,
}
pub trait Op {
    type Value;
    type Summary: Clone;
    fn summarize(value: &Self::Value) -> Self::Summary;
    fn op(lhs: Self::Summary, rhs: Self::Summary) -> Self::Summary;
}
pub struct Nop<T> {
    __marker: PhantomData<fn(T) -> T>,
}

impl<T: PartialEq, O: Op<Value = T>> PartialEq for RbTree<T, O>
where
    O::Summary: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.root.eq(&other.root)
    }
}
impl<T: Hash, O: Op<Value = T>> Hash for RbTree<T, O>
where
    O::Summary: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.root.hash(state);
    }
}
impl<T: Debug, O: Op<Value = T>> Debug for RbTree<T, O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl<T, O: Op<Value = T>> Default for RbTree<T, O> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T> Op for Nop<T> {
    type Value = T;
    type Summary = ();
    fn summarize(_value: &Self::Value) -> Self::Summary {}
    fn op(_lhs: Self::Summary, _rhs: Self::Summary) -> Self::Summary {}
}

impl<A, O: Op<Value = A>> FromIterator<A> for RbTree<A, O> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut nodes = iter
            .into_iter()
            .map(|x| Self::singleton(x))
            .collect::<Vec<_>>();
        if nodes.is_empty() {
            return Self::default();
        }
        let mut step = 1;
        while step < nodes.len() {
            for i in (0..nodes.len() - step).step_by(2 * step) {
                nodes[i] = Self::merge(take(&mut nodes[i]), take(&mut nodes[i + step]));
            }
            step *= 2;
        }
        take(&mut nodes[0])
    }
}

pub struct Iter<'a, T, O: Op<Value = T>>(Vec<&'a Root<T, O>>);
impl<'a, T, O: Op<Value = T>> Iterator for Iter<'a, T, O> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.pop() {
                None => return None,
                Some(Root::Nil(Nil(x))) => return Some(x),
                Some(Root::Node(node)) => {
                    self.0.push(&node.right);
                    self.0.push(&node.left);
                }
            }
        }
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

impl<T, O: Op<Value = T>> RbTree<T, O> {
    pub fn new() -> Self {
        Self::from_root(None)
    }
    pub fn len(&self) -> usize {
        match &self.root {
            None => 0,
            Some(node) => node.len(),
        }
    }
    pub fn iter(&self) -> Iter<'_, T, O> {
        Iter(match &self.root {
            None => Vec::new(),
            Some(node) => vec![node],
        })
    }
    pub fn fold(&mut self, range: impl RangeBounds<usize>) -> Option<O::Summary> {
        let Range { start, end } = open(range, self.len());
        assert!(start <= end && end <= self.len());
        if start == end {
            return None;
        }
        let root = take(&mut self.root).unwrap();
        let [l, cr] = Self::from_root(Some(root)).split(start);
        let [c, r] = cr.split(end - start);
        let res = c.root.as_ref().unwrap().summary();
        *self = Self::merge(Self::merge(l, c), r);
        Some(res)
    }
    pub fn singleton(x: T) -> Self {
        Self::from_root(Some(Root::singleton(x)))
    }
    pub fn push_front(&mut self, x: T) {
        *self = Self::merge(Self::singleton(x), take(self));
    }
    pub fn push_back(&mut self, x: T) {
        *self = Self::merge(take(self), Self::singleton(x));
    }
    pub fn insert(&mut self, i: usize, x: T) {
        assert!((0..=self.len()).contains(&i));
        let [l, r] = take(self).split(i);
        *self = Self::merge(Self::merge(l, Self::singleton(x)), r);
    }
    pub fn delete(&mut self, i: usize) -> T {
        assert!((0..self.len()).contains(&i));
        let [l, cr] = take(self).split(i);
        let [c, r] = cr.split(1);
        *self = Self::merge(l, r);
        match c.root {
            Some(Root::Node(_)) | None => unreachable!(),
            Some(Root::Nil(Nil(x))) => x,
        }
    }
    pub fn merge(lhs: Self, rhs: Self) -> Self {
        match [lhs.root, rhs.root] {
            [None, None] => Self::from_root(None),
            [Some(l), None] => Self::from_root(Some(l)),
            [None, Some(r)] => Self::from_root(Some(r)),
            [Some(l), Some(r)] => Self::from_root(Some(Root::merge(l, r))),
        }
    }
    pub fn split(self, i: usize) -> [Self; 2] {
        assert!((0..=self.len()).contains(&i));
        if i == 0 {
            [Self::from_root(None), self]
        } else if i == self.len() {
            [self, Self::from_root(None)]
        } else {
            let [l, r] = self.root.unwrap().split(i);
            [Self::from_root(Some(l)), Self::from_root(Some(r))]
        }
    }
    fn from_root(root: Option<Root<T, O>>) -> Self {
        Self {
            root,
            __marker: PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Op, RbTree, Root};
    use itertools::Itertools;
    use rand::{distributions::Alphanumeric, prelude::StdRng, Rng, SeedableRng};
    use randtools::SubRange;
    use std::fmt::Debug;
    use std::iter::repeat_with;

    fn validate<T: Debug, O: Op<Value = T>>(tree: &RbTree<T, O>) {
        match &tree.root {
            None => (),
            Some(root) => validate_dfs(root),
        }
    }
    fn validate_dfs<T: Debug, O: Op<Value = T>>(root: &Root<T, O>) {
        if let Some(node) = root.node() {
            if let Some(left) = node.left.node() {
                assert!(left.height == node.height || left.height == node.height - 1);
                if let Some(ll) = left.left.node() {
                    assert_ne!(ll.height, node.height);
                }
            }
            if let Some(right) = node.right.node() {
                assert_eq!(right.height + 1, node.height);
            }
            validate_dfs(&node.left);
            validate_dfs(&node.right);
        }
    }

    #[test]
    fn test_iter() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..200);
            let a = repeat_with(|| rng.gen_range(0..100)).take(n).collect_vec();
            let tree = a.iter().copied().collect::<RbTree<_>>();
            validate(&tree);
            let b = tree.iter().copied().collect_vec();
            assert_eq!(&a, &b);
        }
    }

    #[test]
    fn test_insert_delete() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(0..80);
            let mut a = repeat_with(|| rng.gen_range(0..100)).take(n).collect_vec();
            let mut tree = a.iter().copied().collect::<RbTree<_>>();
            validate(&tree);
            let b = tree.iter().copied().collect_vec();
            assert_eq!(&a, &b);

            for _ in 0..10 + 2 * n {
                match rng.gen_range(0..2) {
                    // insert
                    0 => {
                        let i = rng.gen_range(0..=a.len());
                        let x = rng.gen_range(0..100);
                        a.insert(i, x);
                        tree.insert(i, x);
                    }
                    // delete
                    1 => {
                        let i = rng.gen_range(0..a.len());
                        a.remove(i);
                        tree.delete(i);
                    }
                    _ => unreachable!(),
                }
                validate(&tree);
                let b = tree.iter().copied().collect_vec();
                assert_eq!(&a, &b);
            }
        }
    }

    struct O {}
    impl Op for O {
        type Summary = String;
        type Value = char;
        fn summarize(value: &Self::Value) -> Self::Summary {
            value.to_string()
        }
        fn op(lhs: Self::Summary, rhs: Self::Summary) -> Self::Summary {
            lhs.chars().chain(rhs.chars()).collect()
        }
    }

    #[test]
    fn test_fold() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(0..20);
            let a = repeat_with(|| rng.sample(Alphanumeric))
                .map(|c| c as char)
                .take(n)
                .collect_vec();
            let mut tree = a.iter().copied().collect::<RbTree<_, O>>();
            validate(&tree);

            for _ in 0..10 + 2 * n {
                let range = rng.sample(SubRange(0..n));
                let result = tree.fold(range.clone()).unwrap_or_default();
                let expected = a[range].iter().collect::<String>();
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_insert_delete_fold() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(0..80);
            let mut a = repeat_with(|| rng.sample(Alphanumeric))
                .map(|c| c as char)
                .take(n)
                .collect_vec();
            let mut tree = a.iter().copied().collect::<RbTree<_, O>>();
            validate(&tree);
            let b = tree.iter().copied().collect_vec();
            assert_eq!(&a, &b);

            for _ in 0..10 + 2 * n {
                match rng.gen_range(0..3) {
                    // insert
                    0 => {
                        let i = rng.gen_range(0..=a.len());
                        let x = rng.sample(Alphanumeric) as char;
                        a.insert(i, x);
                        tree.insert(i, x);
                    }
                    // delete
                    1 => {
                        let i = rng.gen_range(0..a.len());
                        a.remove(i);
                        tree.delete(i);
                    }
                    // fold
                    2 => {
                        let range = rng.sample(SubRange(0..a.len()));
                        let result = tree.fold(range.clone()).unwrap_or_default();
                        let expected = a[range].iter().collect::<String>();
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
                validate(&tree);
                let b = tree.iter().copied().collect_vec();
                assert_eq!(&a, &b);
            }
        }
    }
}
