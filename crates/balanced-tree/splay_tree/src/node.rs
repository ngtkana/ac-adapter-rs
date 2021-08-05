use {
    super::LazyOps,
    std::{cmp::Ordering, ptr, ptr::null_mut},
};

pub struct Node<O: LazyOps> {
    pub left: *mut Self,
    pub right: *mut Self,
    pub parent: *mut Self,
    pub value: O::Value,
    pub acc: O::Acc,
    pub len: usize,
    pub lazy: Option<O::Lazy>,
}
impl<O: LazyOps> Node<O> {
    pub fn new(value: O::Value) -> Self {
        Self {
            left: null_mut(),
            right: null_mut(),
            parent: null_mut(),
            acc: O::proj(&value),
            value,
            len: 1,
            lazy: None,
        }
    }
    pub unsafe fn splay(&mut self) {
        while let Some(p) = self.parent.as_mut() {
            if let Some(g) = p.parent.as_mut() {
                g.push();
                p.push();
                self.push();
                if ptr::eq(p.left, self) == ptr::eq(g.left, p) {
                    p.rotate();
                    self.rotate();
                } else {
                    self.rotate();
                    self.rotate();
                }
            } else {
                p.push();
                self.push();
                self.rotate();
            }
        }
    }
    pub unsafe fn rotate(&mut self) {
        let p = self.parent.as_mut().unwrap();
        self.parent = p.parent;
        if ptr::eq(p.left, self) {
            p.left = self.right;
            if let Some(c) = p.left.as_mut() {
                c.parent = p;
            }
            self.right = p;
        } else {
            p.right = self.left;
            if let Some(c) = p.right.as_mut() {
                c.parent = p;
            }
            self.left = p;
        }
        p.parent = self;
        p.update();
        self.update();
        if let Some(g) = self.parent.as_mut() {
            if ptr::eq(g.left, p) {
                g.left = self;
            } else {
                g.right = self;
            }
            g.update();
        }
    }
    pub unsafe fn update(&mut self) {
        self.len = 1;
        self.acc = O::proj(&self.value);
        if let Some(left) = self.left.as_mut() {
            left.push();
            self.len += left.len;
            self.acc = O::op(&left.acc, &self.acc);
        }
        if let Some(right) = self.right.as_mut() {
            right.push();
            self.len += right.len;
            self.acc = O::op(&self.acc, &right.acc);
        }
    }
    pub unsafe fn push(&mut self) {
        if let Some(lazy) = self.lazy.take() {
            O::act_value(&lazy, &mut self.value);
            O::act_acc(&lazy, &mut self.acc);
            if let Some(left) = self.left.as_mut() {
                match left.lazy.as_mut() {
                    None => left.lazy = Some(lazy.clone()),
                    Some(left_lazy) => O::lazy_propagate(&lazy, left_lazy),
                }
            }
            if let Some(right) = self.right.as_mut() {
                match right.lazy.as_mut() {
                    None => right.lazy = Some(lazy.clone()),
                    Some(right_lazy) => O::lazy_propagate(&lazy, right_lazy),
                }
            }
        }
    }
}

pub unsafe fn deep_free<O: LazyOps>(root: *mut Node<O>) {
    if !root.is_null() {
        deep_free((*root).left);
        deep_free((*root).right);
        Box::from_raw(root);
    }
}

pub unsafe fn get<O: LazyOps>(root: *mut Node<O>, mut index: usize) -> *mut Node<O> {
    let mut root = root.as_mut().unwrap();
    loop {
        let lsize = root.left.as_ref().map_or(0, |left| left.len);
        root = match index.cmp(&lsize) {
            Ordering::Less => root.left.as_mut().unwrap(),
            Ordering::Equal => {
                root.splay();
                return root;
            }
            Ordering::Greater => {
                index -= lsize + 1;
                root.right.as_mut().unwrap()
            }
        };
    }
}

pub unsafe fn merge<O: LazyOps>(lhs: *mut Node<O>, rhs: *mut Node<O>) -> *mut Node<O> {
    if let Some(mut lhs) = lhs.as_mut() {
        if let Some(rhs) = rhs.as_mut() {
            lhs = get(lhs, lhs.len - 1).as_mut().unwrap();
            lhs.right = rhs;
            rhs.parent = lhs;
            lhs.update();
        }
        lhs
    } else {
        rhs
    }
}

pub unsafe fn split<O: LazyOps>(root: *mut Node<O>, index: usize) -> [*mut Node<O>; 2] {
    if let Some(root) = root.as_mut() {
        if index == root.len {
            [root, null_mut()]
        } else {
            let rhs = get(root, index).as_mut().unwrap();
            let lhs = rhs.left;
            if let Some(lhs) = lhs.as_mut() {
                lhs.parent = null_mut();
                rhs.left = null_mut();
                rhs.update();
            }
            [lhs, rhs]
        }
    } else {
        [null_mut(); 2]
    }
}
