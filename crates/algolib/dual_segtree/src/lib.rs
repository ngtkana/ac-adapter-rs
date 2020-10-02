use std::ops::RangeBounds;
use type_traits::{Action, Identity};

#[derive(Debug, Clone, PartialEq)]
pub struct DualSegtreeWith<T: Action> {
    dual: DualSegtree<T>,
    table: Vec<T::Space>,
}
impl<T: Action> DualSegtreeWith<T> {
    pub fn from_slice(_src: &[T], _table: &[T::Space]) -> Self {
        todo!()
    }
    pub fn apply(&mut self, _range: impl RangeBounds<usize>, _x: T) {
        todo!()
    }
    pub fn get(&mut self, _i: usize) -> &T::Space {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DualSegtree<T> {
    len: usize,
    lg: u32,
    lazy: Vec<T>,
}
impl<T: Identity> DualSegtree<T> {
    pub fn from_slice(_src: &[T]) -> Self {
        todo!()
    }
    pub fn apply(&mut self, _range: impl RangeBounds<usize>, _x: T) {
        todo!()
    }
    pub fn get(&mut self, _i: usize) -> &T {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    mod impl_query;
}
