mod detail;

use {
    detail::{Nil, Root},
    std::{iter::FromIterator, marker::PhantomData, mem::take},
};

#[derive(Clone, Debug, Hash, PartialEq)]
pub struct RbTree<T, O: Op = Nop<T>> {
    root: Option<Root<T, O>>,
    __marker: PhantomData<fn(O) -> O>,
}

pub trait Op {
    type Value;
    type Summary: Copy;
    fn summarize(value: &Self::Value) -> Self::Summary;
    fn op(lhs: Self::Summary, rhs: Self::Summary) -> Self::Summary;
}
pub struct Nop<T> {
    __marker: PhantomData<fn(T) -> T>,
}
impl<T> Op for Nop<T> {
    type Value = T;
    type Summary = ();
    fn summarize(_value: &Self::Value) -> Self::Summary {}
    fn op(_lhs: Self::Summary, _rhs: Self::Summary) -> Self::Summary {}
}

impl<T, O: Op> Default for RbTree<T, O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<A> FromIterator<A> for RbTree<A> {
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

pub struct Iter<'a, T, O>(Vec<&'a Root<T, O>>);
impl<'a, T, O: Op> Iterator for Iter<'a, T, O> {
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

impl<T, O: Op> RbTree<T, O> {
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
    use itertools::Itertools;
    use std::iter::repeat_with;

    use super::{RbTree, Root};
    use rand::{prelude::StdRng, Rng, SeedableRng};
    #[allow(unused_imports)]
    use test_case::test_case;

    fn validate<T>(tree: &RbTree<T>) {
        match &tree.root {
            None => (),
            Some(root) => validate_dfs(root),
        }
    }
    fn validate_dfs<T>(root: &Root<T>) {
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
            println!("a = {:?}", &a);
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
            let n = rng.gen_range(0..200);
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
}
