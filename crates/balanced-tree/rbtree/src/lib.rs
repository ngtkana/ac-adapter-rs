mod detail;

use std::{iter::FromIterator, mem::take};

#[derive(Clone, Debug, Hash, PartialEq)]
pub struct RbTree<T>(Option<Root<T>>);

impl<T> Default for RbTree<T> {
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

pub struct Iter<'a, T> {
    stack: Vec<&'a Root<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.stack.pop() {
                None => return None,
                Some(Root::Nil(Nil(x))) => return Some(x),
                Some(Root::Node(node)) => {
                    self.stack.push(&node.right);
                    self.stack.push(&node.left);
                }
            }
        }
    }
}

impl<T> RbTree<T> {
    pub fn new() -> Self {
        Self(None)
    }
    pub fn len(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(node) => node.len(),
        }
    }
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            stack: match &self.0 {
                None => Vec::new(),
                Some(node) => vec![node],
            },
        }
    }
    pub fn singleton(x: T) -> Self {
        Self(Some(Root::singleton(x)))
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
        match c.0 {
            Some(Root::Node(_)) | None => unreachable!(),
            Some(Root::Nil(Nil(x))) => x,
        }
    }
    pub fn merge(lhs: Self, rhs: Self) -> Self {
        match [lhs.0, rhs.0] {
            [None, None] => Self(None),
            [Some(l), None] => Self(Some(l)),
            [None, Some(r)] => Self(Some(r)),
            [Some(l), Some(r)] => Self(Some(Root::merge(l, r))),
        }
    }
    pub fn split(self, i: usize) -> [Self; 2] {
        assert!((0..=self.len()).contains(&i));
        if i == 0 {
            [Self(None), self]
        } else if i == self.len() {
            [self, Self(None)]
        } else {
            let [l, r] = self.0.unwrap().split(i);
            [Self(Some(l)), Self(Some(r))]
        }
    }
}

#[derive(Clone, Debug, Hash, PartialEq)]
enum Root<T> {
    Nil(Nil<T>),
    Node(Node<T>),
}
#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
struct Nil<T>(T);

#[derive(Clone, Debug, Hash, PartialEq)]
struct Node<T> {
    left: Box<Root<T>>,
    right: Box<Root<T>>,
    height: usize,
    len: usize,
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
        match &tree.0 {
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
        for _ in 0..20 {
            let n = rng.gen_range(0..20);
            let a = repeat_with(|| rng.gen_range(0..100)).take(n).collect_vec();
            println!("a = {:?}", &a);
            let tree = a.iter().copied().collect::<RbTree<_>>();
            validate(&tree);
            let b = tree.iter().copied().collect_vec();
            assert_eq!(&a, &b);
        }
    }
}
