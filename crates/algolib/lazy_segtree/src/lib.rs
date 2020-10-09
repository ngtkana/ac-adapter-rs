#![allow(dead_code, unused_variables, unused_imports)]
use alg_traits::{Action, Identity};
use std::ops::{Range, RangeBounds};

#[derive(Debug, Clone, PartialEq)]
pub struct LazySegtree<A: Action, T: Identity> {
    len: usize,
    lazy: std::cell::RefCell<Vec<A::Value>>,
    table: std::cell::RefCell<Vec<T::Value>>,
}

impl<A, T> LazySegtree<A, T>
where
    A: Action<Point = T::Value>,
    T: Identity,
{
    fn from_slice(src: &[T::Value]) -> Self {
        todo!()
    }

    fn set(&mut self, i: usize, x: T::Value) {
        todo!()
    }

    fn fold(&self, range: impl RangeBounds<usize>) -> T::Value {
        todo!()
    }

    fn apply(&mut self, range: impl RangeBounds<usize>, a: A::Value) {
        todo!()
    }

    fn search_forward<R, F>(&self, range: R, pred: F) -> usize
    where
        R: RangeBounds<usize>,
        F: FnMut(&T::Value) -> bool,
    {
        todo!()
    }

    fn search_backward<R, F>(&self, range: R, pred: F) -> usize
    where
        R: RangeBounds<usize>,
        F: FnMut(&T::Value) -> bool,
    {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    mod impl_query;
    use super::LazySegtree;
}
