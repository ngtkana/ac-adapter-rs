#![allow(clippy::unnecessary_box_returns)]
#![allow(clippy::type_complexity)]

mod debug;
mod internal;

use crate::internal::{merge2, merge3, split2, split3};
use std::cmp::Ordering;

pub use debug::*;

// TODO: make this private
pub struct Node<C: NodeMarker + ?Sized> {
    pub left: Option<Box<Self>>,
    pub right: Option<Box<Self>>,
    pub ht: u8,
    pub len: usize,
    pub rev: bool,
    pub data: C::Data,
}

pub struct CoreTree<C: NodeMarker> {
    root: Option<Box<Node<C>>>,
}

pub trait NodeMarker {
    type Data;

    fn update(node: &mut Node<Self>);

    fn push(node: &mut Node<Self>);
}

impl<C: NodeMarker> Default for CoreTree<C> {
    fn default() -> Self {
        Self { root: None }
    }
}

impl<C: NodeMarker> FromIterator<C::Data> for CoreTree<C> {
    fn from_iter<T: IntoIterator<Item = C::Data>>(iter: T) -> Self {
        let mut result = Self::new();
        for x in iter {
            result.insert(result.len(), x);
        }
        result
    }
}

impl<C: NodeMarker> CoreTree<C> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    pub fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |x| x.len)
    }

    pub fn insert(&mut self, index: usize, data: C::Data) {
        assert!(index <= self.len());
        let node = Box::new(Node::new(data));
        let (l, r) = split2(self.root.take(), index);
        self.root = Some(merge3(l, node, r));
    }

    pub fn remove(&mut self, index: usize) -> C::Data {
        assert!(index < self.len());
        let (l, c, r) = split3(self.root.take().unwrap(), index);
        self.root = merge2(l, r);
        c.data
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        assert!(index <= self.len());
        if index == self.len() {
            return Self::new();
        }
        let (l, c, r) = split3(self.root.take().unwrap(), index);
        self.root = l;
        Self {
            root: merge2(Some(c), r),
        }
    }

    pub fn append(&mut self, other: Self) {
        self.root = merge2(self.root.take(), other.root);
    }

    pub fn reverse(&mut self, start: usize, end: usize) {
        let r = self.split_off(end);
        let mut c = self.split_off(start);
        if let Some(c) = c.root.as_deref_mut() {
            c.rev ^= true;
        }
        self.append(c);
        self.append(r);
    }

    pub fn touch(&mut self) -> Option<&C::Data> {
        self.root.as_deref_mut().map(|node| &node.data)
    }

    pub fn to_vec<T>(&self, f: impl Fn(&C::Data) -> T) -> Vec<T> {
        fn collect_recur<T, C: NodeMarker>(
            x: &Node<C>,
            f: &impl Fn(&C::Data) -> T,
            out: &mut Vec<T>,
            mut rev: bool,
        ) {
            rev ^= x.rev;
            if let Some(y) = if rev { x.right.as_ref() } else { x.left.as_ref() } {
                collect_recur(y, f, out, rev);
            }
            out.push(f(&x.data));
            if let Some(y) = if rev { x.left.as_ref() } else { x.right.as_ref() } {
                collect_recur(y, f, out, rev);
            }
        }
        let Some(x) = self.root.as_deref() else { return vec![] };
        let mut out = Vec::new();
        collect_recur(x, &f, &mut out, false);
        out
    }
}
