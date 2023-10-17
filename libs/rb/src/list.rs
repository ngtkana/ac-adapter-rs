use crate::tree::Tree;
use crate::Callback;
use crate::Len;
use crate::Op;
use std::marker::PhantomData;

pub(super) struct Irreversible<O: Op> {
    marker: PhantomData<O>,
}

pub(super) struct Reversible<O: Op> {
    marker: PhantomData<O>,
}

#[allow(dead_code)]
pub(super) struct IrreversibleData<O: Op> {
    len: usize,
    value: O::Value,
    acc: O::Acc,
    #[allow(dead_code)]
    lazy: O::Lazy,
}

#[allow(dead_code)]
pub(super) struct ReversibleData<O: Op> {
    len: usize,
    value: O::Value,
    acc: O::Acc,
    #[allow(dead_code)]
    lazy: O::Lazy,
    reverse: bool,
}

#[allow(dead_code)]
impl<O: Op> Callback for Irreversible<O> {
    type Data = IrreversibleData<O>;

    fn push(_node: crate::Ptr<Self>) {}

    fn update(mut node: crate::Ptr<Self>) {
        let mut len = 1;
        let mut acc = O::to_acc(&node.data.value);
        if let Some(left) = node.left {
            acc = O::mul(&left.data.acc, &acc);
            len += left.data.len;
        }
        if let Some(right) = node.right {
            acc = O::mul(&acc, &right.data.acc);
            len += right.data.len;
        }
        node.data.len = len;
        node.data.acc = acc;
    }
}

#[allow(dead_code)]
impl<O: Op> Len for IrreversibleData<O> {
    fn len(&self) -> usize { self.len }
}

#[allow(dead_code)]
impl<O: Op> Callback for Reversible<O> {
    type Data = ReversibleData<O>;

    fn push(_node: crate::Ptr<Self>) {}

    fn update(mut node: crate::Ptr<Self>) {
        let mut len = 1;
        let mut acc = O::to_acc(&node.data.value);
        if let Some(left) = node.left {
            acc = O::mul(&left.data.acc, &acc);
            len += left.data.len;
        }
        if let Some(right) = node.right {
            acc = O::mul(&acc, &right.data.acc);
            len += right.data.len;
        }
        node.data.len = len;
        node.data.acc = acc;
    }
}

/// A list based on a red-black tree.
#[allow(dead_code)]
pub struct RbList<O: Op> {
    root: Tree<Irreversible<O>>,
}

/// A list based on a red-black tree.
#[allow(dead_code)]
pub struct RbReversibleList<O: Op> {
    root: Tree<Reversible<O>>,
}
