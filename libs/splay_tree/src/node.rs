use super::LazyOps;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::mem::replace;
use std::mem::swap;
use std::ptr::null_mut;
use std::ptr::{self};

#[allow(unused_must_use)]
pub fn deep_free<O: LazyOps>(root: *mut Node<O>) {
    if !root.is_null() {
        unsafe {
            deep_free((*root).left);
            deep_free((*root).right);
            Box::from_raw(root);
        }
    }
}

pub fn access_index<O: LazyOps>(mut root: &mut Node<O>, mut i: usize) -> &mut Node<O> {
    loop {
        root.push();
        if let Some(left) = unsafe { root.left.as_mut() } {
            left.push();
        }
        if let Some(right) = unsafe { root.right.as_mut() } {
            right.push();
        }
        let lsize = unsafe { root.left.as_ref() }.map_or(0, |left| left.len);
        root = match i.cmp(&lsize) {
            Ordering::Less => unsafe { root.left.as_mut() }.unwrap(),
            Ordering::Equal => {
                root.splay();
                return root;
            }
            Ordering::Greater => {
                i -= lsize + 1;
                unsafe { root.right.as_mut() }.unwrap()
            }
        };
    }
}

pub fn merge<O: LazyOps>(left: *mut Node<O>, right: *mut Node<O>) -> *mut Node<O> {
    let ans = if let Some(mut left) = unsafe { left.as_mut() } {
        if let Some(right) = unsafe { right.as_mut() } {
            left = access_index(left, left.len - 1);
            left.push();
            left.right = right;
            right.parent = left;
            left.update();
        }
        left
    } else {
        right
    };
    ans
}

pub fn split_at<O: LazyOps>(root: *mut Node<O>, at: usize) -> [*mut Node<O>; 2] {
    if let Some(mut root) = unsafe { root.as_mut() } {
        if at == root.len {
            [root, null_mut()]
        } else if at == 0 {
            [null_mut(), root]
        } else {
            root = access_index(root, at);
            root.push();
            let left = replace(&mut root.left, null_mut());
            if let Some(left) = unsafe { left.as_mut() } {
                left.parent = null_mut();
                root.update();
            }
            [left, root]
        }
    } else {
        [null_mut(), null_mut()]
    }
}

pub struct Node<O: LazyOps> {
    pub left: *mut Self,
    pub right: *mut Self,
    pub parent: *mut Self,
    pub len: usize,
    pub rev: bool,
    pub value: O::Value,
    pub acc: O::Acc,
    pub lazy: Option<O::Lazy>,
}
impl<O: LazyOps> Node<O> {
    pub fn new(value: O::Value) -> Self {
        Node {
            left: null_mut(),
            right: null_mut(),
            parent: null_mut(),
            len: 1,
            rev: false,
            acc: O::proj(&value),
            value,
            lazy: None,
        }
    }

    pub fn dump(&self)
    where
        O::Value: Debug,
        O::Acc: Debug,
        O::Lazy: Debug,
    {
        if let Some(left) = unsafe { self.left.as_ref() } {
            left.dump();
        }
        println!(
            "{:?}: parent = {:?},  left = {:?}, right = {:?}, len = {}, rev = {}, value = {:?}, \
             acc = {:?}, lazy = {:?}",
            std::ptr::from_ref(self),
            self.parent,
            self.left,
            self.right,
            self.len,
            self.rev,
            self.value,
            self.acc,
            self.lazy
        );
        if let Some(right) = unsafe { self.right.as_ref() } {
            right.dump();
        }
    }

    pub fn update(&mut self) {
        self.len = 1;
        self.acc = O::proj(&self.value);
        if let Some(left) = unsafe { self.left.as_mut() } {
            left.push();
            self.len += left.len;
            self.acc = O::op(&left.acc, &self.acc);
        }
        if let Some(right) = unsafe { self.right.as_mut() } {
            right.push();
            self.len += right.len;
            self.acc = O::op(&self.acc, &right.acc);
        }
    }

    pub fn push(&mut self) {
        if let Some(lazy) = self.lazy.take() {
            O::act_value(&lazy, &mut self.value);
            O::act_acc(&lazy, &mut self.acc);
            if let Some(left) = unsafe { self.left.as_mut() } {
                O::compose_to_option(&lazy, &mut left.lazy);
            }
            if let Some(right) = unsafe { self.right.as_mut() } {
                O::compose_to_option(&lazy, &mut right.lazy);
            }
        }
        if replace(&mut self.rev, false) {
            swap(&mut self.left, &mut self.right);
            if let Some(left) = unsafe { self.left.as_mut() } {
                left.rev ^= true;
            }
            if let Some(right) = unsafe { self.right.as_mut() } {
                right.rev ^= true;
            }
        }
    }

    pub fn rotate(&mut self) {
        let p = unsafe { &mut *self.parent };
        let g = p.parent;
        self.push();
        if ptr::eq(self, p.left) {
            p.left = self.right;
            if let Some(c) = unsafe { p.left.as_mut() } {
                c.parent = p;
            }
            self.right = p;
        } else {
            p.right = self.left;
            if let Some(c) = unsafe { p.right.as_mut() } {
                c.parent = p;
            }
            self.left = p;
        }
        p.parent = self;
        self.parent = g;
        if let Some(g) = unsafe { g.as_mut() } {
            if ptr::eq(p, g.left) {
                g.left = self;
            } else {
                g.right = self;
            }
        }
        p.update();
        self.update();
    }

    pub fn splay(&mut self) {
        while let Some(p) = unsafe { self.parent.as_mut() } {
            if let Some(g) = unsafe { p.parent.as_mut() } {
                if ptr::eq(self, p.left) == ptr::eq(p, g.left) {
                    p.rotate();
                } else {
                    self.rotate();
                }
            }
            self.rotate();
        }
    }
}
