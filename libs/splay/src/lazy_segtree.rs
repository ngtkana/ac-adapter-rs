use std::{marker::PhantomData, ops::RangeBounds};

use crate::{MarkerTrait, Tree};

pub struct SplayLazySegtree<O: LazySegtreeOp> {
    tree: Tree<LazySegtreeMarker<O>>,
}

struct LazySegtreeMarker<O> {
    __marker: PhantomData<O>,
}

pub trait LazySegtreeOp {
    type Value: Clone;

    type Op: PartialEq;

    fn identity() -> Self::Value;

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    fn act(op: &Self::Op, prod: &mut Self::Value);

    fn compose(lhs: &Self::Op, rhs: &mut Self::Op);

    fn nop() -> Self::Op;
}

impl<O: LazySegtreeOp> MarkerTrait for LazySegtreeMarker<O> {
    type Value = O::Value;

    type Prod = O::Value;

    type Op = O::Op;

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

    fn act_on_value(op: &Self::Op, value: &mut Self::Value) {
        O::act(op, value);
    }

    fn act_on_prod(op: &Self::Op, prod: &mut Self::Prod) {
        O::act(op, prod);
    }

    fn act_on_op(lhs: &Self::Op, rhs: &mut Self::Op) {
        O::compose(lhs, rhs);
    }

    fn nop() -> Self::Op {
        O::nop()
    }

    fn is_nop(op: &Self::Op) -> bool {
        *op == O::nop()
    }
}

impl<O: LazySegtreeOp> SplayLazySegtree<O> {
    pub fn new() -> Self {
        Tree::new().into()
    }

    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    pub fn len(&self) -> usize {
        self.tree.len()
    }

    pub fn insert(&mut self, index: usize, value: O::Value) {
        self.tree.insert(index, value);
    }

    pub fn remove(&mut self, index: usize) -> O::Value {
        self.tree.remove(index)
    }

    pub fn append(&mut self, other: Self) {
        self.tree.append(other.tree);
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        self.tree.split_off(index).into()
    }

    pub fn collect_vec(&self) -> Vec<O::Value> {
        self.tree.collect_vec()
    }

    pub fn prod(&mut self, range: impl RangeBounds<usize>) -> O::Value {
        self.tree.prod(range)
    }

    pub fn max_left(&mut self, start: usize, pred: impl FnMut(&O::Value) -> bool) -> usize {
        self.tree.max_left(start, pred)
    }

    pub fn min_right(&mut self, end: usize, pred: impl FnMut(&O::Value) -> bool) -> usize {
        self.tree.min_right(end, pred)
    }

    pub fn apply(&mut self, range: impl RangeBounds<usize>, op: &O::Op) {
        self.tree.apply(range, op);
    }
}

impl<O: LazySegtreeOp> Default for SplayLazySegtree<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: LazySegtreeOp> From<Tree<LazySegtreeMarker<O>>> for SplayLazySegtree<O> {
    fn from(tree: Tree<LazySegtreeMarker<O>>) -> Self {
        Self { tree }
    }
}

impl<O: LazySegtreeOp> FromIterator<O::Value> for SplayLazySegtree<O> {
    fn from_iter<I: IntoIterator<Item = O::Value>>(iter: I) -> Self {
        iter.into_iter().collect::<Tree<_>>().into()
    }
}
