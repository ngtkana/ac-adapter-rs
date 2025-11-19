#![allow(dead_code)]
mod lazy_segtree;
mod list;
mod segtree;
mod tree_impl;

pub use lazy_segtree::{LazySegtreeOp, SplayLazySegtree};
pub use list::SplayList;
pub use segtree::{SegtreeOp, SplaySegtree};

use std::{
    ops::{Deref, DerefMut},
    ptr::null_mut,
};

struct Tree<N: MarkerTrait> {
    root: *mut Node<N>,
}

trait MarkerTrait {
    type Value;
    type Prod;
    type Op;

    fn identity() -> Self::Prod;

    fn to_prod(value: &Self::Value) -> Self::Prod;

    fn mul_assign_from_left(lhs: &Self::Prod, rhs: &mut Self::Prod);

    fn mul_assign_from_right(lhs: &mut Self::Prod, rhs: &Self::Prod);

    fn act_on_value(op: &Self::Op, value: &mut Self::Value);

    fn act_on_prod(op: &Self::Op, prod: &mut Self::Prod);

    fn act_on_op(lhs: &Self::Op, rhs: &mut Self::Op);

    fn nop() -> Self::Op;

    fn is_nop(op: &Self::Op) -> bool;
}

struct Node<N: MarkerTrait> {
    left: *mut Self,
    right: *mut Self,
    len: usize,
    rev: bool,
    value: N::Value,
    prod: N::Prod,
    op: N::Op,
}

impl<N: MarkerTrait> Node<N> {
    pub fn new(value: N::Value) -> Self {
        let prod = N::to_prod(&value);
        Self {
            left: null_mut(),
            right: null_mut(),
            len: 1,
            rev: false,
            value,
            prod,
            op: N::nop(),
        }
    }

    pub fn update(&mut self) {
        unsafe {
            assert!(!self.rev);
            assert!(N::is_nop(&self.op));
            self.len = 1;
            self.prod = N::to_prod(&self.value);
            if let Some(l) = self.left.as_mut() {
                self.len += l.len;
                N::mul_assign_from_left(&l.prod, &mut self.prod);
            }
            if let Some(r) = self.right.as_mut() {
                self.len += r.len;
                N::mul_assign_from_right(&mut self.prod, &r.prod);
            }
        }
    }

    pub fn push(&mut self) {
        unsafe {
            if self.rev {
                self.rev = false;
                std::mem::swap(&mut self.left, &mut self.right);
                if let Some(l) = self.left.as_mut() {
                    l.rev ^= true;
                }
                if let Some(r) = self.right.as_mut() {
                    r.rev ^= true;
                }
            }
            if !N::is_nop(&self.op) {
                if let Some(l) = self.left.as_mut() {
                    N::act_on_value(&self.op, &mut l.value);
                    N::act_on_prod(&self.op, &mut l.prod);
                    N::act_on_op(&self.op, &mut l.op);
                }
                if let Some(r) = self.right.as_mut() {
                    N::act_on_value(&self.op, &mut r.value);
                    N::act_on_prod(&self.op, &mut r.prod);
                    N::act_on_op(&self.op, &mut r.op);
                }
                self.op = N::nop();
            }
        }
    }
}

struct Entry<'a, N: MarkerTrait> {
    node: &'a mut Node<N>,
}

impl<N: MarkerTrait> Deref for Entry<'_, N> {
    type Target = N::Value;

    fn deref(&self) -> &Self::Target {
        &self.node.value
    }
}

impl<N: MarkerTrait> DerefMut for Entry<'_, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.node.value
    }
}

impl<N: MarkerTrait> Drop for Entry<'_, N> {
    fn drop(&mut self) {
        self.node.prod = N::to_prod(&self.node.value);
    }
}

