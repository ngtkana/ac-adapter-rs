//! おいでよ unsafe の森

use std::cmp::Ordering;
use {
    super::Ops,
    std::{
        marker::PhantomData,
        ptr::{self, null_mut},
    },
};

pub unsafe fn deep_free<O: Ops>(root: *mut Node<O>) {
    if !root.is_null() {
        deep_free((*root).left);
        deep_free((*root).right);
        Box::from_raw(root);
    }
}

pub unsafe fn get<O: Ops>(root: *mut Node<O>, mut index: usize) -> *mut Node<O> {
    debug_assert!(index < (*root).len);
    let mut now = root;
    loop {
        let lsize = if (*now).left.is_null() {
            0
        } else {
            (*(*now).left).len
        };
        now = match index.cmp(&lsize) {
            Ordering::Less => (*now).left,
            Ordering::Equal => {
                (*now).splay();
                return now;
            }
            Ordering::Greater => {
                index -= lsize + 1;
                (*now).right
            }
        };
    }
}

pub unsafe fn merge<O: Ops>(mut lhs: *mut Node<O>, rhs: *mut Node<O>) -> *mut Node<O> {
    if lhs.is_null() {
        return rhs;
    }
    if rhs.is_null() {
        return lhs;
    }
    lhs = get(lhs, (*lhs).len - 1);
    (*lhs).right = rhs;
    (*rhs).parent = lhs;
    (*lhs).update();
    lhs
}

pub unsafe fn split<O: Ops>(mut root: *mut Node<O>, index: usize) -> [*mut Node<O>; 2] {
    if root.is_null() {
        debug_assert_eq!(index, 0);
        return [null_mut(), null_mut()];
    }
    debug_assert!(index <= (*root).len);
    if (*root).len == index {
        return [root, null_mut()];
    }
    if index == 0 {
        return [null_mut(), root];
    }
    root = get(root, index);
    let lhs = (*root).left;
    let rhs = root;
    (*rhs).left = null_mut();
    (*lhs).parent = null_mut();
    (*rhs).update();
    [lhs, rhs]
}

pub unsafe fn insert<O: Ops>(root: *mut Node<O>, index: usize, node: *mut Node<O>) -> *mut Node<O> {
    let [left, right] = split(root, index);
    merge(merge(left, node), right)
}

pub unsafe fn delete<O: Ops>(mut root: *mut Node<O>, index: usize) -> [*mut Node<O>; 2] {
    root = get(root, index);
    let lhs = (*root).left;
    let rhs = (*root).right;
    if !lhs.is_null() {
        (*lhs).parent = null_mut();
    }
    if !rhs.is_null() {
        (*rhs).parent = null_mut();
    }
    (*root).left = null_mut();
    (*root).right = null_mut();
    (*root).update();
    [merge(lhs, rhs), root]
}

pub struct Node<O: Ops> {
    pub left: *mut Self,
    pub right: *mut Self,
    pub parent: *mut Self,
    pub len: usize,
    pub value: O::Value,
    pub fold: O::Acc,
    pub __marker: PhantomData<fn(O) -> O>,
}
impl<O: Ops> Node<O> {
    pub fn new(value: O::Value) -> Self {
        Self {
            left: null_mut(),
            right: null_mut(),
            parent: null_mut(),
            len: 1,
            fold: O::proj(&value),
            value,
            __marker: PhantomData,
        }
    }
    pub unsafe fn rotate(&mut self) {
        debug_assert!(!self.parent.is_null());
        let mut p = self.parent;
        let mut pp = (*p).parent;
        let mut c;
        if (*p).left == self as *mut _ {
            c = self.right;
            self.right = p;
            (*p).left = c;
        } else {
            c = self.left;
            self.left = p;
            (*p).right = c;
        }
        if !pp.is_null() && (*pp).left == p {
            (*pp).left = self;
        }
        if !pp.is_null() && (*pp).right == p {
            (*pp).right = self;
        }
        self.parent = pp;
        (*p).parent = self;
        if !c.is_null() {
            (*c).parent = p;
        }
        (*p).update();
        self.update();
    }
    pub unsafe fn splay(&mut self) {
        while self.state() != 0 {
            let p = self.parent;
            if (*p).state() == 0 {
                self.rotate()
            } else if self.state() == (*p).state() {
                (*p).rotate();
                self.rotate();
            } else {
                self.rotate();
                self.rotate();
            }
        }
    }
    pub unsafe fn state(&self) -> i32 {
        let p = self.parent;
        if p.is_null() {
            0
        } else if ptr::eq((*p).left as *const _, self as *const _) {
            1
        } else if ptr::eq((*p).right as *const _, self as *const _) {
            -1
        } else {
            unreachable!()
        }
    }
    pub unsafe fn update(&mut self) {
        self.len = 1;
        let mut fold = O::proj(&self.value);
        if !self.left.is_null() {
            self.len += (*self.left).len;
            fold = O::op(&(*self.left).fold, &fold);
        }
        if !self.right.is_null() {
            self.len += (*self.right).len;
            fold = O::op(&fold, &(*self.right).fold);
        }
        self.fold = fold;
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{super::Ops, get, merge, Node},
        std::ptr::null_mut,
    };

    enum O {}
    impl Ops for O {
        type Value = char;
        type Acc = String;
        fn proj(c: &char) -> String {
            c.to_string()
        }
        fn op(lhs: &String, rhs: &String) -> String {
            lhs.chars().chain(rhs.chars()).collect()
        }
    }
    type NodeCat = Node<O>;

    #[test]
    fn test_unit() {
        let unit = Box::into_raw(Box::new(NodeCat::new('c')));
        assert_eq!(unsafe { &*unit }.value, 'c');
        assert_eq!(unsafe { &*unit }.fold, "c");
        assert_eq!(unsafe { get(unit, 0) }, unit);
        unsafe { Box::from_raw(unit) };
    }

    #[test]
    fn test_three() {
        let a = Box::into_raw(Box::new(NodeCat::new('a')));
        let b = Box::into_raw(Box::new(NodeCat::new('b')));
        let c = Box::into_raw(Box::new(NodeCat::new('c')));
        dbg!(a, b, c);

        // a
        //  \
        //   b   型であることを assert
        //    \
        //     c
        let preorder_abc = |root: &*mut NodeCat| {
            assert_eq!(*root, a);

            assert_eq!(unsafe { &*a }.left, null_mut());
            assert_eq!(unsafe { &*a }.right, b);
            assert_eq!(unsafe { &*a }.parent, null_mut());
            assert_eq!(unsafe { &*a }.len, 3);
            assert_eq!(unsafe { &*a }.value, 'a');
            assert_eq!(unsafe { &*a }.fold, "abc");

            assert_eq!(unsafe { &*b }.left, null_mut());
            assert_eq!(unsafe { &*b }.right, c);
            assert_eq!(unsafe { &*b }.parent, a);
            assert_eq!(unsafe { &*b }.len, 2);
            assert_eq!(unsafe { &*b }.value, 'b');
            assert_eq!(unsafe { &*b }.fold, "bc");

            assert_eq!(unsafe { &*c }.left, null_mut());
            assert_eq!(unsafe { &*c }.right, null_mut());
            assert_eq!(unsafe { &*c }.parent, b);
            assert_eq!(unsafe { &*c }.len, 1);
            assert_eq!(unsafe { &*c }.value, 'c');
            assert_eq!(unsafe { &*c }.fold, "c");
        };

        //   b
        //  / \  型であることを assert
        // a   c
        let preorder_bac = |root: &*mut NodeCat| {
            assert_eq!(*root, b);

            assert_eq!(unsafe { &*a }.left, null_mut());
            assert_eq!(unsafe { &*a }.right, null_mut());
            assert_eq!(unsafe { &*a }.parent, b);
            assert_eq!(unsafe { &*a }.len, 1);
            assert_eq!(unsafe { &*a }.value, 'a');
            assert_eq!(unsafe { &*a }.fold, "a");

            assert_eq!(unsafe { &*b }.left, a);
            assert_eq!(unsafe { &*b }.right, c);
            assert_eq!(unsafe { &*b }.parent, null_mut());
            assert_eq!(unsafe { &*b }.len, 3);
            assert_eq!(unsafe { &*b }.value, 'b');
            assert_eq!(unsafe { &*b }.fold, "abc");

            assert_eq!(unsafe { &*c }.left, null_mut());
            assert_eq!(unsafe { &*c }.right, null_mut());
            assert_eq!(unsafe { &*c }.parent, b);
            assert_eq!(unsafe { &*c }.len, 1);
            assert_eq!(unsafe { &*c }.value, 'c');
            assert_eq!(unsafe { &*c }.fold, "c");
        };

        //     c
        //    /
        //   b   型であることを assert
        //  /
        // a
        let preorder_cba = |root: &*mut NodeCat| {
            assert_eq!(*root, c);

            assert_eq!(unsafe { &*a }.left, null_mut());
            assert_eq!(unsafe { &*a }.right, null_mut());
            assert_eq!(unsafe { &*a }.parent, b);
            assert_eq!(unsafe { &*a }.len, 1);
            assert_eq!(unsafe { &*a }.value, 'a');
            assert_eq!(unsafe { &*a }.fold, "a");

            assert_eq!(unsafe { &*b }.left, a);
            assert_eq!(unsafe { &*b }.right, null_mut());
            assert_eq!(unsafe { &*b }.parent, c);
            assert_eq!(unsafe { &*b }.len, 2);
            assert_eq!(unsafe { &*b }.value, 'b');
            assert_eq!(unsafe { &*b }.fold, "ab");

            assert_eq!(unsafe { &*c }.left, b);
            assert_eq!(unsafe { &*c }.right, null_mut());
            assert_eq!(unsafe { &*c }.parent, null_mut());
            assert_eq!(unsafe { &*c }.len, 3);
            assert_eq!(unsafe { &*c }.value, 'c');
            assert_eq!(unsafe { &*c }.fold, "abc");
        };

        // merge は音を返します。
        let mut root = unsafe { merge(a, merge(b, c)) };
        preorder_abc(&root);

        // get(1) で根を b にします。
        root = unsafe { get(root, 1) };
        preorder_bac(&root);

        // get(0) で根を a にします。
        root = unsafe { get(root, 0) };
        preorder_abc(&root);

        // get(2) で根を a にします。
        root = unsafe { get(root, 2) };
        preorder_cba(&root);

        unsafe { Box::from_raw(a) };
        unsafe { Box::from_raw(b) };
        unsafe { Box::from_raw(c) };
    }
}
