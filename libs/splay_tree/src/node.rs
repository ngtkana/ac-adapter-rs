use super::LazyOps;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::mem::replace;
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

/// # Safety notes
///
/// `root` は生ポインタで受け渡しします。スプレー操作は祖先へ辿ってから元のノードへ戻って
/// 書き換えることがあるため、`&mut Node<O>` を引数に取ると（呼び出し期間中ずっと有効な排他参照
/// という強い保証のもとで）別名経由の書き込みと衝突し、未定義動作になります（Stacked/Tree
/// Borrows で検証済み）。そのため、この関数とその内部で呼ぶ `splay`/`rotate` は生ポインタのみを
/// 扱い、フィールドアクセスの瞬間だけ一時的に参照を作ります。
pub fn access_index<O: LazyOps>(root: *mut Node<O>, mut i: usize) -> *mut Node<O> {
    let mut root = root;
    loop {
        unsafe { (*root).push() };
        let left = unsafe { (*root).left };
        if let Some(left) = unsafe { left.as_mut() } {
            left.push();
        }
        let right = unsafe { (*root).right };
        if let Some(right) = unsafe { right.as_mut() } {
            right.push();
        }
        let lsize = unsafe { left.as_ref() }.map_or(0, |left| left.len);
        root = match i.cmp(&lsize) {
            Ordering::Less => left,
            Ordering::Equal => {
                splay(root);
                return root;
            }
            Ordering::Greater => {
                i -= lsize + 1;
                right
            }
        };
    }
}

pub fn merge<O: LazyOps>(left: *mut Node<O>, right: *mut Node<O>) -> *mut Node<O> {
    if left.is_null() {
        return right;
    }
    if right.is_null() {
        return left;
    }
    let left = access_index(left, unsafe { (*left).len } - 1);
    unsafe {
        (*left).push();
        (*left).right = right;
        (*right).parent = left;
        (*left).update();
    }
    left
}

pub fn split_at<O: LazyOps>(root: *mut Node<O>, at: usize) -> [*mut Node<O>; 2] {
    if root.is_null() {
        return [null_mut(), null_mut()];
    }
    let len = unsafe { (*root).len };
    if at == len {
        [root, null_mut()]
    } else if at == 0 {
        [null_mut(), root]
    } else {
        let root = access_index(root, at);
        unsafe { (*root).push() };
        let left = replace(unsafe { &mut (*root).left }, null_mut());
        if let Some(left) = unsafe { left.as_mut() } {
            left.parent = null_mut();
            unsafe { (*root).update() };
        }
        [left, root]
    }
}

/// ノード `x` を根まで splay します。生ポインタで実装している理由は [`access_index`] を参照してください。
fn splay<O: LazyOps>(x: *mut Node<O>) {
    loop {
        let p = unsafe { (*x).parent };
        if p.is_null() {
            return;
        }
        let g = unsafe { (*p).parent };
        if !g.is_null() {
            let x_is_p_left = ptr::eq(x, unsafe { (*p).left });
            let p_is_g_left = ptr::eq(p, unsafe { (*g).left });
            if x_is_p_left == p_is_g_left {
                rotate(p);
            } else {
                rotate(x);
            }
        }
        rotate(x);
    }
}

/// `x` をその親 `p` の位置まで回転させます。生ポインタで実装している理由は [`access_index`] を参照してください。
fn rotate<O: LazyOps>(x: *mut Node<O>) {
    let p = unsafe { (*x).parent };
    let g = unsafe { (*p).parent };
    unsafe { (*x).push() };
    if ptr::eq(x, unsafe { (*p).left }) {
        let xr = unsafe { (*x).right };
        unsafe { (*p).left = xr };
        if let Some(c) = unsafe { xr.as_mut() } {
            c.parent = p;
        }
        unsafe { (*x).right = p };
    } else {
        let xl = unsafe { (*x).left };
        unsafe { (*p).right = xl };
        if let Some(c) = unsafe { xl.as_mut() } {
            c.parent = p;
        }
        unsafe { (*x).left = p };
    }
    unsafe {
        (*p).parent = x;
        (*x).parent = g;
    }
    if let Some(g) = unsafe { g.as_mut() } {
        if ptr::eq(p, g.left) {
            g.left = x;
        } else {
            g.right = x;
        }
    }
    unsafe {
        (*p).update();
        (*x).update();
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
            std::mem::swap(&mut self.left, &mut self.right);
            if let Some(left) = unsafe { self.left.as_mut() } {
                left.rev ^= true;
            }
            if let Some(right) = unsafe { self.right.as_mut() } {
                right.rev ^= true;
            }
        }
    }
}
