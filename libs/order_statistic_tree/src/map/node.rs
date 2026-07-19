use std::borrow::Borrow;
use std::ptr::NonNull;

use super::{Op, OrderStatisticMap};

pub struct Node<K, V, O: Op<Key = K, Value = V>> {
    pub key: K,
    pub value: V,
    pub parent: Option<NonNull<Self>>,
    pub left: Option<NonNull<Self>>,
    pub right: Option<NonNull<Self>>,
    pub len: usize,
    pub prod: O::SegValue,
}

impl<K, V, O: Op<Key = K, Value = V>> Node<K, V, O> {
    pub fn update(&mut self) {
        unsafe {
            self.len = self.left.map_or(0, |left| (*left.as_ptr()).len)
                + 1
                + self.right.map_or(0, |rigth| (*rigth.as_ptr()).len);

            let left_prod =
                self.left.map_or_else(O::identity, |l| (*l.as_ptr()).prod.clone());
            let right_prod =
                self.right.map_or_else(O::identity, |r| (*r.as_ptr()).prod.clone());
            self.prod = O::mul(
                &O::mul(&left_prod, &O::to_seg_value(&self.key, &self.value)),
                &right_prod,
            );
        }
    }
}

pub fn splay<K, V, O: Op<Key = K, Value = V>>(x: NonNull<Node<K, V, O>>) -> NonNull<Node<K, V, O>> {
    unsafe {
        while let Some(p) = (*x.as_ptr()).parent {
            if let Some(q) = (*p.as_ptr()).parent {
                if (*q.as_ptr()).left == Some(p) && (*p.as_ptr()).left == Some(x) {
                    // zig-zig: left-left
                    rotate_right(q);
                    rotate_right(p);
                } else if (*q.as_ptr()).right == Some(p) && (*p.as_ptr()).right == Some(x) {
                    // zig-zig: right-right
                    rotate_left(q);
                    rotate_left(p);
                } else {
                    // zig-zag
                    if (*p.as_ptr()).left == Some(x) {
                        rotate_right(p);
                    } else {
                        rotate_left(p);
                    }
                    if (*q.as_ptr()).left == Some(x) {
                        rotate_right(q);
                    } else {
                        rotate_left(q);
                    }
                }
            } else {
                // zig: parent is root
                if (*p.as_ptr()).left == Some(x) {
                    rotate_right(p);
                } else if (*p.as_ptr()).right == Some(x) {
                    rotate_left(p);
                } else {
                    unreachable!()
                }
            }
        }
        x
    }
}

pub fn rotate_left<K, V, O: Op<Key = K, Value = V>>(x: NonNull<Node<K, V, O>>) -> NonNull<Node<K, V, O>> {
    unsafe {
        let y = (*x.as_ptr()).right.unwrap();
        let c = (*y.as_ptr()).left;

        (*x.as_ptr()).right = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).left = Some(x);

        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);

        (*x.as_ptr()).update();
        (*y.as_ptr()).update();

        y
    }
}

pub fn rotate_right<K, V, O: Op<Key = K, Value = V>>(x: NonNull<Node<K, V, O>>) -> NonNull<Node<K, V, O>> {
    unsafe {
        let y = (*x.as_ptr()).left.unwrap();
        let c = (*y.as_ptr()).right;

        (*x.as_ptr()).left = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).right = Some(x);

        if let Some(q) = (*x.as_ptr()).parent {
            if (*q.as_ptr()).left == Some(x) {
                (*q.as_ptr()).left = Some(y);
            } else {
                (*q.as_ptr()).right = Some(y);
            }
            (*y.as_ptr()).parent = Some(q);
        } else {
            (*y.as_ptr()).parent = None;
        }
        (*x.as_ptr()).parent = Some(y);

        (*x.as_ptr()).update();
        (*y.as_ptr()).update();

        y
    }
}

pub fn free_subtree<K, V, O: Op<Key = K, Value = V>>(root: Option<NonNull<Node<K, V, O>>>) {
    let mut stack = Vec::new();
    if let Some(r) = root {
        stack.push(r);
    }
    while let Some(node) = stack.pop() {
        unsafe {
            if let Some(left) = (*node.as_ptr()).left {
                stack.push(left);
            }
            if let Some(right) = (*node.as_ptr()).right {
                stack.push(right);
            }
            drop(Box::from_raw(node.as_ptr()));
        }
    }
}

pub fn find_and_splay<K, Q: Ord + ?Sized, V, O: Op<Key = K, Value = V>>(
    map: &OrderStatisticMap<K, V, O>,
    key: &Q,
) -> Option<NonNull<Node<K, V, O>>>
where
    K: Ord + Borrow<Q>,
{
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            let mut found = false;
            loop {
                let key_cmp = key.cmp((*current.as_ptr()).key.borrow());
                match key_cmp {
                    std::cmp::Ordering::Less => {
                        if let Some(left) = (*current.as_ptr()).left {
                            current = left;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        if let Some(right) = (*current.as_ptr()).right {
                            current = right;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        found = true;
                        break;
                    }
                }
            }
            current = splay(current);
            map.root.set(Some(current));
            if found { Some(current) } else { None }
        },
    }
}

pub fn nth_and_splay<K, V, O: Op<Key = K, Value = V>>(map: &OrderStatisticMap<K, V, O>, mut n: usize) -> NonNull<Node<K, V, O>> {
    let root = map.root.get().unwrap();
    unsafe {
        let mut current = root;
        loop {
            let left_len = (*current.as_ptr()).left.map_or(0, |l| (*l.as_ptr()).len);
            match n.cmp(&left_len) {
                std::cmp::Ordering::Less => {
                    current = (*current.as_ptr()).left.unwrap();
                }
                std::cmp::Ordering::Greater => {
                    n -= left_len + 1;
                    current = (*current.as_ptr()).right.unwrap();
                }
                std::cmp::Ordering::Equal => {
                    break;
                }
            }
        }
        current = splay(current);
        map.root.set(Some(current));
        current
    }
}

#[allow(clippy::type_complexity)]
pub fn locate_and_splay<K, Q: Ord + ?Sized, V, O: Op<Key = K, Value = V>>(
    map: &OrderStatisticMap<K, V, O>,
    key: &Q,
    include_equal: bool,
) -> (usize, Option<NonNull<Node<K, V, O>>>)
where
    K: Ord + Borrow<Q>,
{
    match map.root.get() {
        None => (0, None),
        Some(root) => unsafe {
            let mut current = root;
            let mut pos = 0;
            let mut found_node = None;

            loop {
                let left_len = (*current.as_ptr()).left.map_or(0, |l| (*l.as_ptr()).len);
                let key_cmp = key.cmp((*current.as_ptr()).key.borrow());
                match key_cmp {
                    std::cmp::Ordering::Less => {
                        if let Some(left) = (*current.as_ptr()).left {
                            current = left;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Greater => {
                        pos += left_len + 1;
                        if let Some(right) = (*current.as_ptr()).right {
                            current = right;
                        } else {
                            break;
                        }
                    }
                    std::cmp::Ordering::Equal => {
                        pos += left_len;
                        found_node = Some(current);
                        if include_equal {
                            pos += 1;
                            if let Some(right) = (*current.as_ptr()).right {
                                current = right;
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                }
            }
            current = splay(current);
            map.root.set(Some(current));
            (pos, found_node)
        },
    }
}

pub fn leftmost_and_splay<K, V, O: Op<Key = K, Value = V>>(map: &OrderStatisticMap<K, V, O>) -> Option<NonNull<Node<K, V, O>>> {
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            while let Some(left) = (*current.as_ptr()).left {
                current = left;
            }
            current = splay(current);
            map.root.set(Some(current));
            Some(current)
        },
    }
}

pub fn rightmost_and_splay<K, V, O: Op<Key = K, Value = V>>(map: &OrderStatisticMap<K, V, O>) -> Option<NonNull<Node<K, V, O>>> {
    match map.root.get() {
        None => None,
        Some(root) => unsafe {
            let mut current = root;
            while let Some(right) = (*current.as_ptr()).right {
                current = right;
            }
            current = splay(current);
            map.root.set(Some(current));
            Some(current)
        },
    }
}

type SplitResult<K, V, O> = (Option<NonNull<Node<K, V, O>>>, Option<NonNull<Node<K, V, O>>>);

pub fn split_at_index<K, V, O: Op<Key = K, Value = V>>(
    root: Option<NonNull<Node<K, V, O>>>,
    idx: usize,
) -> SplitResult<K, V, O> {
    match root {
        None => (None, None),
        Some(r) => {
            let len = unsafe { (*r.as_ptr()).len };
            if idx == 0 {
                return (None, Some(r));
            }
            if idx >= len {
                return (Some(r), None);
            }
            unsafe {
                let pivot = nth_from_node(r, idx);
                let pivot_splayed = splay(pivot);

                let left = (*pivot_splayed.as_ptr()).left.take();
                if let Some(l) = left {
                    (*l.as_ptr()).parent = None;
                }

                (*pivot_splayed.as_ptr()).update();

                (left, Some(pivot_splayed))
            }
        }
    }
}

fn nth_from_node<K, V, O: Op<Key = K, Value = V>>(
    node: NonNull<Node<K, V, O>>,
    mut n: usize,
) -> NonNull<Node<K, V, O>> {
    let mut current = node;
    loop {
        let left_len = unsafe { (*current.as_ptr()).left.map_or(0, |l| (*l.as_ptr()).len) };
        match n.cmp(&left_len) {
            std::cmp::Ordering::Less => {
                current = unsafe { (*current.as_ptr()).left.unwrap() };
            }
            std::cmp::Ordering::Greater => {
                n -= left_len + 1;
                current = unsafe { (*current.as_ptr()).right.unwrap() };
            }
            std::cmp::Ordering::Equal => {
                break;
            }
        }
    }
    current
}

pub fn merge_trees<K, V, O: Op<Key = K, Value = V>>(
    left: Option<NonNull<Node<K, V, O>>>,
    right: Option<NonNull<Node<K, V, O>>>,
) -> Option<NonNull<Node<K, V, O>>> {
    match (left, right) {
        (None, None) => None,
        (Some(l), None) => {
            unsafe { (*l.as_ptr()).parent = None; }
            Some(l)
        }
        (None, Some(r)) => {
            unsafe { (*r.as_ptr()).parent = None; }
            Some(r)
        }
        (Some(l), Some(r)) => {
            unsafe {
                (*l.as_ptr()).parent = None;

                let mut curr = l;
                while let Some(next) = (*curr.as_ptr()).right {
                    curr = next;
                }
                let new_left_root = splay(curr);

                (*new_left_root.as_ptr()).right = Some(r);
                (*r.as_ptr()).parent = Some(new_left_root);
                (*new_left_root.as_ptr()).update();

                Some(new_left_root)
            }
        }
    }
}

pub fn detach_root<K, V, O: Op<Key = K, Value = V>>(map: &mut OrderStatisticMap<K, V, O>) -> (K, V) {
    let root = map.root.get().unwrap();
    unsafe {
        let (key, value) = (
            std::ptr::read(&raw const (*root.as_ptr()).key),
            std::ptr::read(&raw const (*root.as_ptr()).value),
        );

        let left = (*root.as_ptr()).left;
        let right = (*root.as_ptr()).right;

        let new_root = merge_trees(left, right);

        drop(Box::from_raw(root.as_ptr()));
        map.root.set(new_root);
        (key, value)
    }
}

