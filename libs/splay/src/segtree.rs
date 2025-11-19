use std::{marker::PhantomData, ops::RangeBounds};

use crate::{MarkerTrait, Tree};

pub struct SplaySegtree<O: SegtreeOp> {
    tree: Tree<SegtreeMarker<O>>,
}

struct SegtreeMarker<O> {
    __marker: PhantomData<O>,
}

pub trait SegtreeOp {
    type Value: Clone;

    fn identity() -> Self::Value;

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;
}

impl<O: SegtreeOp> MarkerTrait for SegtreeMarker<O> {
    type Value = O::Value;

    type Prod = O::Value;

    type Op = ();

    fn identity() -> Self::Prod {
        O::identity()
    }

    fn to_prod(value: &Self::Value) -> Self::Prod {
        value.clone()
    }

    fn mul_assign_from_left(lhs: &Self::Prod, rhs: &mut Self::Prod) {
        *rhs = O::mul(lhs, rhs);
    }

    fn mul_assign_from_right(lhs: &mut Self::Prod, rhs: &Self::Prod) {
        *lhs = O::mul(lhs, rhs);
    }

    fn act_on_value(_op: &Self::Op, _value: &mut Self::Value) {}

    fn act_on_prod(_op: &Self::Op, _prod: &mut Self::Prod) {}

    fn act_on_op(_lhs: &Self::Op, _rhs: &mut Self::Op) {}

    fn nop() -> Self::Op {}

    fn is_nop(_op: &Self::Op) -> bool {
        true
    }
}

trait NewTrait<O: SegtreeOp> {
    fn new() -> Self;

    fn is_empty(&self) -> bool;

    fn len(&self) -> usize;

    fn insert(&mut self, index: usize, value: O::Value);

    fn remove(&mut self, index: usize) -> O::Value;

    fn append(&mut self, other: Self);

    fn split_off(&mut self, index: usize) -> Self;

    fn prod(&mut self, range: impl RangeBounds<usize>) -> O::Value;

    fn max_left(&mut self, start: usize, pred: impl FnMut(&O::Value) -> bool) -> usize;

    fn min_right(&mut self, end: usize, pred: impl FnMut(&O::Value) -> bool) -> usize;
}

impl<O: SegtreeOp> NewTrait<O> for SplaySegtree<O> {
    fn new() -> Self {
        Tree::new().into()
    }

    fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    fn len(&self) -> usize {
        self.tree.len()
    }

    fn insert(&mut self, index: usize, value: O::Value) {
        self.tree.insert(index, value);
    }

    fn remove(&mut self, index: usize) -> O::Value {
        self.tree.remove(index)
    }

    fn append(&mut self, other: Self) {
        self.tree.append(other.tree);
    }

    fn split_off(&mut self, index: usize) -> Self {
        self.tree.split_off(index).into()
    }

    fn prod(&mut self, range: impl RangeBounds<usize>) -> O::Value {
        self.tree.prod(range)
    }

    fn max_left(&mut self, start: usize, pred: impl FnMut(&O::Value) -> bool) -> usize {
        self.tree.max_left(start, pred)
    }

    fn min_right(&mut self, end: usize, pred: impl FnMut(&O::Value) -> bool) -> usize {
        self.tree.min_right(end, pred)
    }
}

impl<O: SegtreeOp> SplaySegtree<O> {
    /// Creates a new, empty SplaySegtree.
    pub fn new() -> Self {
        Tree::new().into()
    }

    /// Returns true if the segtree is empty.
    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    /// Returns the number of elements in the segtree.
    pub fn len(&self) -> usize {
        self.tree.len()
    }

    /// Inserts a value at the given index.
    pub fn insert(&mut self, index: usize, value: O::Value) {
        self.tree.insert(index, value);
    }

    /// Removes and returns the value at the given index.
    pub fn remove(&mut self, index: usize) -> O::Value {
        self.tree.remove(index)
    }

    /// Appends another SplaySegtree to this one.
    pub fn append(&mut self, other: Self) {
        self.tree.append(other.tree);
    }

    /// Splits off the segtree at the given index.
    pub fn split_off(&mut self, index: usize) -> Self {
        self.tree.split_off(index).into()
    }

    /// Returns the product of the values in the given range.
    pub fn prod(&mut self, range: impl RangeBounds<usize>) -> O::Value {
        self.tree.prod(range)
    }

    /// Returns the maximum left index for which the predicate holds.
    pub fn max_left(&mut self, start: usize, pred: impl FnMut(&O::Value) -> bool) -> usize {
        self.tree.max_left(start, pred)
    }

    /// Returns the minimum right index for which the predicate holds.
    pub fn min_right(&mut self, end: usize, pred: impl FnMut(&O::Value) -> bool) -> usize {
        self.tree.min_right(end, pred)
    }
}

impl<O: SegtreeOp> Default for SplaySegtree<O> {
    fn default() -> Self {
        Self::new()
    }
}
impl<O: SegtreeOp> From<Tree<SegtreeMarker<O>>> for SplaySegtree<O> {
    fn from(tree: Tree<SegtreeMarker<O>>) -> Self {
        Self { tree }
    }
}

impl<O: SegtreeOp> FromIterator<O::Value> for SplaySegtree<O> {
    fn from_iter<I: IntoIterator<Item = O::Value>>(iter: I) -> Self {
        iter.into_iter().collect::<Tree<_>>().into()
    }
}
