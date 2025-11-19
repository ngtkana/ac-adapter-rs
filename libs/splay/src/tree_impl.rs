#![allow(unused_variables)]
#![allow(clippy::needless_pass_by_value)]
use std::{ops::RangeBounds, ptr::null_mut};

use crate::{MarkerTrait, Tree};

impl<N: MarkerTrait> Tree<N> {
    pub fn new() -> Self {
        Self { root: null_mut() }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_null()
    }

    pub fn len(&self) -> usize {
        unsafe { self.root.as_ref().map_or(0, |x| x.len) }
    }

    pub fn insert(&mut self, index: usize, value: N::Value) {
        todo!()
    }

    pub fn remove(&mut self, index: usize) -> N::Value {
        todo!()
    }

    pub fn append(&mut self, other: Self) {
        todo!()
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        todo!()
    }

    pub fn prod(&mut self, range: impl RangeBounds<usize>) -> N::Prod {
        todo!()
    }

    pub fn max_left(&mut self, start: usize, pred: impl FnMut(&N::Prod) -> bool) -> usize {
        todo!()
    }

    pub fn min_right(&mut self, end: usize, pred: impl FnMut(&N::Prod) -> bool) -> usize {
        todo!()
    }

    pub fn apply(&mut self, range: impl RangeBounds<usize>, op: &N::Op) {
        todo!()
    }
}

impl<N: MarkerTrait> Default for Tree<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: MarkerTrait> FromIterator<N::Value> for Tree<N> {
    fn from_iter<T: IntoIterator<Item = N::Value>>(iter: T) -> Self {
        todo!()
    }
}
