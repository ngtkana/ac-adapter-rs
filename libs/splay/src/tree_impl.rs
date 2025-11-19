#![allow(unused_variables)]
#![allow(clippy::needless_pass_by_value)]
use std::{
    cmp::Ordering,
    ops::RangeBounds,
    ptr::{self, null_mut},
};

use crate::{MarkerTrait, Node, Tree};

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
        unsafe {
            let (l, r) = split2(self.root, index);
            let c = Box::leak(Box::new(Node::new(value)));
            self.root = merge3(l, c, r);
        }
    }

    pub fn remove(&mut self, index: usize) -> N::Value {
        unsafe {
            let (l, c, r) = split3(&mut *self.root, index);
            self.root = merge2(l, r);
            Box::from_raw(c).value
        }
    }

    pub fn append(&mut self, other: Self) {
        todo!()
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        todo!()
    }

    pub fn collect_vec(&self) -> Vec<N::Value>
    where
        N::Value: Clone,
    {
        let mut out = vec![];
        visit(self.root, &mut |x| out.push(x.value.clone()));
        out
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

unsafe fn split2<N: MarkerTrait>(
    x: *mut Node<N>,
    mut index: usize,
) -> (*mut Node<N>, *mut Node<N>) {
    let Some(mut x) = x.as_mut() else { return (null_mut(), null_mut()) };
    let is_less = loop {
        let llen = x.left.as_ref().map_or(0, |y| y.len);
        if index <= llen {
            let Some(l) = x.left.as_mut() else { break false };
            x = l;
        } else {
            let Some(r) = x.right.as_mut() else { break true };
            x = r;
            index -= llen + 1;
        }
    };
    splay(x);
    if is_less {
        let r = x.right;
        if let Some(r) = r.as_mut() {
            r.parent = null_mut();
        }
        x.right = null_mut();
        x.update();
        (x, r)
    } else {
        let l = x.left;
        if let Some(l) = l.as_mut() {
            l.parent = null_mut();
        }
        x.left = null_mut();
        x.update();
        (l, x)
    }
}

unsafe fn split3<N: MarkerTrait>(
    mut x: &mut Node<N>,
    mut index: usize,
) -> (*mut Node<N>, &mut Node<N>, *mut Node<N>) {
    loop {
        let llen = x.left.as_ref().map_or(0, |y| y.len);
        match index.cmp(&llen) {
            Ordering::Less => x = &mut *x.left,
            Ordering::Equal => break,
            Ordering::Greater => {
                index -= llen + 1;
                x = &mut *x.right;
            }
        }
    }
    splay(x);
    let l = x.left;
    let r = x.right;
    x.left = null_mut();
    x.right = null_mut();
    if let Some(l) = l.as_mut() {
        l.parent = null_mut();
    }
    if let Some(r) = r.as_mut() {
        r.parent = null_mut();
    }
    x.update();
    (l, x, r)
}

unsafe fn merge2<N: MarkerTrait>(l: *mut Node<N>, r: *mut Node<N>) -> *mut Node<N> {
    let Some(mut r) = r.as_mut() else { return l };
    while let Some(l) = r.left.as_mut() {
        r = l;
    }
    splay(r);
    r.left = l;
    if let Some(l) = l.as_mut() {
        l.parent = r;
    }
    r.update();
    r
}

unsafe fn merge3<N: MarkerTrait>(
    l: *mut Node<N>,
    c: &mut Node<N>,
    r: *mut Node<N>,
) -> &mut Node<N> {
    assert!(c.left.is_null());
    assert!(c.right.is_null());
    assert!(c.parent.is_null());
    if let Some(mut l) = l.as_mut() {
        assert!(l.parent.is_null());
        while let Some(r) = l.right.as_mut() {
            l = r;
        }
        c.left = splay(l);
        l.parent = c;
    }
    if let Some(mut r) = r.as_mut() {
        assert!(r.parent.is_null());
        while let Some(l) = r.left.as_mut() {
            r = l;
        }
        c.right = splay(r);
        r.parent = c;
    }
    c.update();
    c
}

unsafe fn splay<N: MarkerTrait>(x: &mut Node<N>) -> &mut Node<N> {
    while let Some(p) = x.parent.as_mut() {
        let Some(pp) = p.parent.as_mut() else {
            if ptr::eq(p.left, x) {
                rotate_right(p);
            } else {
                rotate_left(p);
            }
            break;
        };
        match (ptr::eq(pp.left, p), ptr::eq(p.left, x)) {
            (true, true) => {
                rotate_right(pp);
                rotate_right(p);
            }
            (true, false) => {
                rotate_left(p);
                rotate_right(pp);
            }
            (false, true) => {
                rotate_right(p);
                rotate_left(pp);
            }
            (false, false) => {
                rotate_left(pp);
                rotate_left(p);
            }
        }
    }
    x
}

unsafe fn rotate_left<N: MarkerTrait>(x: &mut Node<N>) -> &mut Node<N> {
    x.push();
    let y = &mut *x.right;
    y.push();
    x.right = y.left;
    if let Some(c) = x.right.as_mut() {
        c.parent = x;
    }
    y.parent = x.parent;
    y.left = x;
    x.parent = y;
    if let Some(p) = y.parent.as_mut() {
        if ptr::eq(p.left, x) {
            p.left = y;
        } else if ptr::eq(p.right, x) {
            p.right = y;
        } else {
            unreachable!()
        }
    }
    x.update();
    y.update();
    y
}

unsafe fn rotate_right<N: MarkerTrait>(x: &mut Node<N>) -> &mut Node<N> {
    x.push();
    let y = &mut *x.left;
    y.push();
    x.left = y.right;
    if let Some(c) = x.left.as_mut() {
        c.parent = x;
    }
    y.parent = x.parent;
    y.right = x;
    x.parent = y;
    if let Some(p) = y.parent.as_mut() {
        if ptr::eq(p.left, x) {
            p.left = y;
        } else if ptr::eq(p.right, x) {
            p.right = y;
        } else {
            unreachable!()
        }
    }
    x.update();
    y.update();
    y
}

fn visit<N: MarkerTrait>(x: *mut Node<N>, f: &mut impl FnMut(&mut Node<N>)) {
    unsafe {
        let Some(x) = x.as_mut() else { return };
        visit(x.left, f);
        f(x);
        visit(x.right, f);
    }
}
