use super::{Navi2, Navi3, Op};
use std::ptr::NonNull;

type Nn<O> = NonNull<Node<O>>;
pub(super) type Onn<O> = Option<NonNull<Node<O>>>;

pub(super) struct Node<O: Op> {
    pub(super) store: O::Store,
    left: Onn<O>,
    right: Onn<O>,
    parent: Onn<O>,
}
impl<O: Op> Node<O> {
    pub(super) fn new(store: O::Store) -> Self {
        Self {
            store,
            left: None,
            right: None,
            parent: None,
        }
    }
    fn update(&mut self) {
        unsafe {
            O::update(
                &mut self.store,
                self.left.map(|left| &(*left.as_ptr()).store),
                self.right.map(|right| &(*right.as_ptr()).store),
            );
        }
    }
}

pub(super) fn visit<T, O: Op<Store = T>>(root: Onn<O>, f: &mut impl FnMut(&T)) {
    let Some(root) = root else { return };
    unsafe {
        visit((*root.as_ptr()).left, f);
        f(&(*root.as_ptr()).store);
        visit((*root.as_ptr()).right, f);
    }
}

pub(super) fn merge2<O: Op>(left: Onn<O>, right: Onn<O>) -> Onn<O> {
    match (left, right) {
        (left, None) => left,
        (None, right) => right,
        (Some(mut left), Some(right)) => unsafe {
            (left, _) = find_and_splay(left, |_root, _left, _right| Navi3::GoDownRight);
            (*left.as_ptr()).right = Some(right);
            (*right.as_ptr()).parent = Some(left);
            (*left.as_ptr()).update();
            Some(left)
        },
    }
}

pub(super) fn merge3<O: Op>(left: Onn<O>, center: Nn<O>, right: Onn<O>) -> Nn<O> {
    unsafe {
        if let Some(left) = left {
            (*left.as_ptr()).parent = Some(center);
        }
        if let Some(right) = right {
            (*right.as_ptr()).parent = Some(center);
        }
        (*center.as_ptr()).left = left;
        (*center.as_ptr()).right = right;
        (*center.as_ptr()).update();
        center
    }
}

pub(super) fn split2<T, O: Op<Store = T>>(
    root: Onn<O>,
    mut f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2,
) -> (Onn<O>, Onn<O>) {
    let Some(root) = root else { return (None, None) };
    let (root, navi) = find_and_splay(root, |node, left, right| match f(node, left, right) {
        Navi2::GoDownRight => Navi3::GoDownRight,
        Navi2::GoDownLeft => Navi3::GoDownLeft,
    });
    unsafe {
        match navi {
            Navi3::GoDownRight => {
                let right = (*root.as_ptr()).right.take();
                if let Some(right) = right {
                    (*right.as_ptr()).parent = None;
                }
                (*root.as_ptr()).update();
                (Some(root), right)
            }
            Navi3::GoDownLeft => {
                let left = (*root.as_ptr()).left.take();
                if let Some(left) = left {
                    (*left.as_ptr()).parent = None;
                }
                (*root.as_ptr()).update();
                (left, Some(root))
            }
            Navi3::Found => unreachable!(),
        }
    }
}

pub(super) enum Split3Result<O: Op> {
    Success(Onn<O>, Nn<O>, Onn<O>),
    Failure(Onn<O>),
}

pub(super) fn split3<T, O: Op<Store = T>>(
    root: Onn<O>,
    f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3,
) -> Split3Result<O> {
    let Some(root) = root else { return Split3Result::Failure(None) };
    let (root, navi3) = find_and_splay(root, f);
    if navi3 != Navi3::Found {
        return Split3Result::Failure(Some(root));
    }
    unsafe {
        let left = (*root.as_ptr()).left.take();
        if let Some(left) = left {
            (*left.as_ptr()).parent = None;
        }
        let right = (*root.as_ptr()).right.take();
        if let Some(right) = right {
            (*right.as_ptr()).parent = None;
        }
        (*root.as_ptr()).update();
        Split3Result::Success(left, root, right)
    }
}

fn splay<O: Op>(x: Nn<O>) -> Nn<O> {
    unsafe {
        while let Some(p) = (*x.as_ptr()).parent {
            if let Some(q) = (*p.as_ptr()).parent {
                match ((*q.as_ptr()).left == Some(p), (*p.as_ptr()).left == Some(x)) {
                    (true, true) => {
                        rotate_right(q);
                        rotate_right(p);
                    }
                    (false, false) => {
                        rotate_left(q);
                        rotate_left(p);
                    }
                    (true, false) => {
                        rotate_left(p);
                        rotate_right(q);
                    }
                    (false, true) => {
                        rotate_right(p);
                        rotate_left(q);
                    }
                }
            } else if (*p.as_ptr()).left == Some(x) {
                rotate_right(p);
            } else {
                rotate_left(p);
            }
        }
        x
    }
}

fn rotate_left<O: Op>(x: Nn<O>) -> Nn<O> {
    unsafe {
        let p = (*x.as_ptr()).parent;
        let y = (*x.as_ptr()).right.unwrap();
        let c = (*y.as_ptr()).left;
        (*x.as_ptr()).right = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).left = Some(x);
        (*x.as_ptr()).parent = Some(y);
        if let Some(p) = p {
            if (*p.as_ptr()).left == Some(x) {
                (*p.as_ptr()).left = Some(y);
            } else {
                (*p.as_ptr()).right = Some(y);
            }
        }
        (*y.as_ptr()).parent = p;
        (*x.as_ptr()).update();
        (*y.as_ptr()).update();
        y
    }
}

fn rotate_right<O: Op>(x: Nn<O>) -> Nn<O> {
    unsafe {
        let p = (*x.as_ptr()).parent;
        let y = (*x.as_ptr()).left.unwrap();
        let c = (*y.as_ptr()).right;
        (*x.as_ptr()).left = c;
        if let Some(c) = c {
            (*c.as_ptr()).parent = Some(x);
        }
        (*y.as_ptr()).right = Some(x);
        (*x.as_ptr()).parent = Some(y);
        if let Some(p) = p {
            if (*p.as_ptr()).left == Some(x) {
                (*p.as_ptr()).left = Some(y);
            } else {
                (*p.as_ptr()).right = Some(y);
            }
        }
        (*y.as_ptr()).parent = p;
        (*x.as_ptr()).update();
        (*y.as_ptr()).update();
        y
    }
}

pub(super) fn free_subtree<O: Op>(root: Onn<O>) {
    let Some(root) = root else { return };
    let mut stack = vec![root];
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

fn find_and_splay<T, O: Op<Store = T>>(
    root: Nn<O>,
    mut f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3,
) -> (Nn<O>, Navi3) {
    unsafe {
        let mut node = root;
        loop {
            let navi = f(
                &(*node.as_ptr()).store,
                (*node.as_ptr()).left.map(|left| &(*left.as_ptr()).store),
                (*node.as_ptr()).right.map(|right| &(*right.as_ptr()).store),
            );
            match navi {
                Navi3::GoDownLeft => {
                    if let Some(left) = (*node.as_ptr()).left {
                        node = left;
                        continue;
                    }
                }
                Navi3::GoDownRight => {
                    if let Some(right) = (*node.as_ptr()).right {
                        node = right;
                        continue;
                    }
                }
                Navi3::Found => {}
            }
            return (splay(node), navi);
        }
    }
}
