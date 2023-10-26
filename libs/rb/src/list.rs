#![allow(dead_code)]
use crate::tree::BeefPtr;
use crate::tree::BeefSteak;
use crate::tree::Callback;
use crate::tree::LeafPtr;
use crate::tree::Ptr;
use crate::tree::Steak;
use crate::tree::Tree;
use crate::Op;
use std::marker::PhantomData;

/// A list based on a red-black tree.
pub struct List<O: Op> {
    tree: Tree<ListCallback<O>>,
}
impl<O: Op> List<O> {
    /// Create a new empty list.
    pub fn new() -> Self { Self::default() }

    /// Returns the length of the list.
    pub fn len(&self) -> usize {
        match self.tree.root() {
            Some(p) => p.len(),
            None => 0,
        }
    }

    /// Returns `true` if the list is empty.
    pub fn is_empty(&self) -> bool { self.tree.root().is_none() }

    /// Insert a value at the `i`th position.
    ///
    /// # Panics
    ///
    /// Panics if `i > self.len()`.
    pub fn insert(&mut self, mut i: usize, x: O::Value) {
        assert!(i <= self.len(), "index out of bounds");
        let position = self
            .tree
            .binary_search(|b| {
                let left_len = b.left().len();
                if i < left_len {
                    true
                } else {
                    i -= left_len;
                    false
                }
            })
            .map(|l| {
                (l, match i {
                    0 => true,
                    1 => false,
                    _ => unreachable!(),
                })
            });
        let leaf = LeafPtr::new(LeafData {
            acc: O::to_acc(&x),
            value: x,
        });
        self.tree.insert(position, leaf, |left, right| {
            BeefPtr::new(
                BeefData {
                    len: 0,
                    acc: O::mul(&left.data().acc, &right.data().acc),
                    lazy: O::identity(),
                },
                left.upcast(),
                right.upcast(),
            )
        });
    }

    /// Remove the `i`th value and return it.
    ///
    /// # Panics
    ///
    /// Panics if `i >= self.len()`.
    pub fn remove(&mut self, mut i: usize) -> O::Value {
        assert!(i < self.len(), "index out of bounds");
        let p = self
            .tree
            .binary_search(|b| {
                let left_len = b.left().len();
                if i < left_len {
                    true
                } else {
                    i -= left_len;
                    false
                }
            })
            .unwrap();
        self.tree.remove(p, BeefPtr::free);
        p.free().value
    }
}

impl<O: Op> Default for List<O> {
    fn default() -> Self {
        Self {
            tree: Tree::default(),
        }
    }
}

struct LeafData<O: Op> {
    value: O::Value,
    acc: O::Acc,
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct BeefData<O: Op> {
    len: usize,
    acc: O::Acc,
    lazy: O::Lazy,
}

struct ListCallback<O> {
    marker: PhantomData<O>,
}
impl<O: Op> Callback for ListCallback<O> {
    type BeefData = BeefData<O>;
    type LeafData = LeafData<O>;

    fn update(x: &mut BeefSteak<Self>) {
        debug_assert!(O::is_identity(&x.data.lazy));
        x.data.len = x.left.len() + x.right.len();
        x.data.acc = O::mul(x.left.acc(), x.right.acc());
    }

    fn push(x: &mut BeefSteak<Self>) {
        if !O::is_identity(&x.data.lazy) {
            let lazy = O::swap_with_identity(&mut x.data.lazy);
            x.left.apply(&lazy);
            x.right.apply(&lazy);
        }
    }
}

impl<O: Op> Ptr<ListCallback<O>> {
    fn len(self) -> usize {
        match &self.steak {
            Steak::Leaf(_) => 1,
            Steak::Beef(x) => x.data.len,
        }
    }

    fn acc(&self) -> &O::Acc {
        match &self.steak {
            Steak::Leaf(x) => &x.acc,
            Steak::Beef(x) => &x.data.acc,
        }
    }

    fn apply(&mut self, lazy: &O::Lazy) {
        match &mut self.steak {
            Steak::Leaf(x) => {
                O::apply_on_acc(&mut x.acc, lazy);
                O::apply_on_value(&mut x.value, lazy);
            }
            Steak::Beef(x) => O::apply_on_acc(&mut x.data.acc, lazy),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tree::test_util;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;

    const P: u64 = 998244353;

    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
    pub struct HashnBase {
        hash: u64,
        base: u64,
    }
    impl HashnBase {
        pub fn empty() -> Self { Self { hash: 0, base: 1 } }

        pub fn from_value(value: u64) -> Self {
            Self {
                hash: value,
                base: 100,
            }
        }

        pub fn mul(&self, other: &Self) -> Self {
            Self {
                hash: (self.hash * other.base + other.hash) % P,
                base: self.base * other.base % P,
            }
        }
    }

    #[derive(Clone, Copy, Debug, PartialEq)]
    enum RollingHash {}
    impl Op for RollingHash {
        type Acc = HashnBase;
        type Lazy = ();
        type Value = u64;

        fn mul(left: &Self::Acc, right: &Self::Acc) -> Self::Acc { left.mul(right) }

        fn to_acc(value: &Self::Value) -> Self::Acc { HashnBase::from_value(*value) }

        fn compose(_: &mut Self::Lazy, _: &Self::Lazy) {}

        fn identity() -> Self::Lazy {}

        fn apply_on_acc(_: &mut Self::Acc, _: &Self::Lazy) {}

        fn apply_on_value(_: &mut Self::Value, _: &Self::Lazy) {}
    }

    fn to_vec<O: Op>(list: &List<O>) -> Vec<O::Value>
    where
        O::Value: Copy,
    {
        fn to_vec<O: Op>(p: Ptr<ListCallback<O>>, result: &mut Vec<O::Value>)
        where
            O::Value: Copy,
        {
            match &p.steak {
                Steak::Leaf(l) => result.push(l.value),
                Steak::Beef(b) => {
                    to_vec(b.left, result);
                    to_vec(b.right, result);
                }
            }
        }
        let mut result = Vec::new();
        if let Some(root) = list.tree.root() {
            to_vec(root, &mut result);
        }
        result
    }

    #[rstest]
    #[case(3)]
    #[case(40)]
    #[case(200)]
    fn test_insert(#[case] max_length: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut list = List::<RollingHash>::new();
            let mut vec = Vec::new();
            for _ in 0..200 {
                match rng.gen_range(0..=max_length) {
                    // Insert
                    x if vec.len() <= x => {
                        let i = rng.gen_range(0..=vec.len());
                        let value = rng.gen_range(0..20);
                        list.insert(i, value);
                        vec.insert(i, value);
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
}
