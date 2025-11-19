use std::marker::PhantomData;

use crate::{MarkerTrait, Tree};

pub struct SplayList<T> {
    tree: Tree<ListMarker<T>>,
}

struct ListMarker<T> {
    __marker: PhantomData<T>,
}

impl<T> MarkerTrait for ListMarker<T> {
    type Value = T;

    type Prod = ();

    type Op = ();

    fn identity() -> Self::Prod {}

    fn to_prod(_value: &Self::Value) -> Self::Prod {}

    fn mul_assign_from_left(_lhs: &Self::Prod, _rhs: &mut Self::Prod) {}

    fn mul_assign_from_right(_lhs: &mut Self::Prod, _rhs: &Self::Prod) {}

    fn act_on_value(_op: &Self::Op, _value: &mut Self::Value) {}

    fn act_on_prod(_op: &Self::Op, _prod: &mut Self::Prod) {}

    fn act_on_op(_lhs: &Self::Op, _rhs: &mut Self::Op) {}

    fn nop() -> Self::Op {}

    fn is_nop(_op: &Self::Op) -> bool {
        true
    }
}

// Public inherent methods for SplayList<T>
impl<T> SplayList<T> {
    pub fn new() -> Self {
        Tree::new().into()
    }

    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    pub fn len(&self) -> usize {
        self.tree.len()
    }

    pub fn insert(&mut self, index: usize, value: T) {
        self.tree.insert(index, value);
    }

    pub fn remove(&mut self, index: usize) -> T {
        self.tree.remove(index)
    }

    pub fn append(&mut self, other: Self) {
        self.tree.append(other.tree);
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        self.tree.split_off(index).into()
    }
}

impl<T> From<Tree<ListMarker<T>>> for SplayList<T> {
    fn from(tree: Tree<ListMarker<T>>) -> Self {
        Self { tree }
    }
}

impl<T> FromIterator<T> for SplayList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter().collect::<Tree<_>>().into()
    }
}
