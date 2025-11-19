#![allow(dead_code)]
mod rev_lazy_segtree;
mod rev_list;
mod rev_segtree;
mod tree_impl;

pub use rev_lazy_segtree::{RevLazySegtree, RevLazySegtreeOp};
pub use rev_list::RevList;
pub use rev_segtree::{RevSegtree, RevSegtreeOp};

use std::{
    ops::{Deref, DerefMut},
    ptr::null_mut,
};

struct Tree<N: Marker> {
    root: *mut Node<N>,
}

trait Marker {
    type Value;
    type Prod;
    type Op;
    type Rev;

    fn identity() -> Self::Prod;

    fn to_prod(value: &Self::Value) -> Self::Prod;

    fn mul_assign_from_left(lhs: &Self::Prod, rhs: &mut Self::Prod);

    fn mul_assign_from_right(lhs: &mut Self::Prod, rhs: &Self::Prod);

    fn act_on_value(op: &Self::Op, value: &mut Self::Value);

    fn act_on_prod(op: &Self::Op, prod: &mut Self::Prod);

    fn act_on_op(lhs: &Self::Op, rhs: &mut Self::Op);

    fn nop() -> Self::Op;

    fn is_nop(op: &Self::Op) -> bool;

    fn rev(rev: &Self::Rev) -> bool;

    fn rev_false() -> Self::Rev;

    fn flip_rev(rev: &mut Self::Rev);
}

struct Node<N: Marker> {
    parent: *mut Self,
    left: *mut Self,
    right: *mut Self,
    len: usize,
    rev: N::Rev,
    value: N::Value,
    prod: N::Prod,
    op: N::Op,
}

impl<N: Marker> Node<N> {
    pub fn new(value: N::Value) -> Self {
        let prod = N::to_prod(&value);
        Self {
            parent: null_mut(),
            left: null_mut(),
            right: null_mut(),
            len: 1,
            rev: N::rev_false(),
            value,
            prod,
            op: N::nop(),
        }
    }

    pub fn update(&mut self) {
        unsafe {
            assert!(!N::rev(&self.rev));
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
            if N::rev(&self.rev) {
                self.rev = N::rev_false();
                std::mem::swap(&mut self.left, &mut self.right);
                if let Some(l) = self.left.as_mut() {
                    N::flip_rev(&mut l.rev);
                }
                if let Some(r) = self.right.as_mut() {
                    N::flip_rev(&mut r.rev);
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

struct Entry<'a, N: Marker> {
    node: &'a mut Node<N>,
}

impl<N: Marker> Deref for Entry<'_, N> {
    type Target = N::Value;

    fn deref(&self) -> &Self::Target {
        &self.node.value
    }
}

impl<N: Marker> DerefMut for Entry<'_, N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.node.value
    }
}

impl<N: Marker> Drop for Entry<'_, N> {
    fn drop(&mut self) {
        self.node.prod = N::to_prod(&self.node.value);
    }
}

#[cfg(test)]
mod test_util {
    use super::*;
    use std::fmt::Write;

    pub fn pretty<N: Marker>(tree: &Tree<N>) -> String
    where
        N::Value: std::fmt::Debug,
    {
        unsafe fn pretty_impl<N: Marker>(x: *mut Node<N>, s: &mut String, header: &mut String)
        where
            N::Value: std::fmt::Debug,
        {
            let Some(x) = x.as_mut() else { return };

            let is_left_child = x.parent.as_ref().is_some_and(|p| std::ptr::eq(p.left, x));
            let is_right_child = x.parent.as_ref().is_some_and(|p| std::ptr::eq(p.right, x));
            let neck = if let Some(p) = x.parent.as_ref() {
                if std::ptr::eq(p.left, x) {
                    '┌'
                } else if std::ptr::eq(p.right, x) {
                    '└'
                } else {
                    unreachable!()
                }
            } else {
                '╶'
            };

            header.push(if is_right_child { '│' } else { ' ' });
            pretty_impl(x.left, s, &mut *header);
            header.pop().unwrap();

            writeln!(s, "{}{neck}○ {:?}", *header, x.value).unwrap();

            header.push(if is_left_child { '│' } else { ' ' });
            pretty_impl(x.right, s, &mut *header);
            header.pop().unwrap();
        }
        unsafe {
            let mut s = String::new();
            pretty_impl(tree.root, &mut s, &mut String::new());
            s
        }
    }
}
