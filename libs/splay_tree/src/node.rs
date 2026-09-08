use super::LazyOps;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::mem::replace;
use std::ptr::null_mut;
use std::ptr::{self};

/// 部分木 `root` を根から葉へたどり、すべてのノードを解放する。
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

/// 添字 `i` にあたるノードを根から辿って探し、[`splay`] で根まで回転させて返す。
///
/// 各ノードで `push` して遅延作用・反転フラグを確定させたうえで左部分木の `len` を見て、
/// `i` が左部分木に入るか・自分自身か・右部分木かを判定しながら降りていく。
///
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

/// `left` の全要素の後ろに `right` の全要素を連結した木の根を返す。
///
/// `left` の最右ノードを [`access_index`] で根まで splay し、その右の子として `right` を繋ぐ。
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

/// 木 `root` を添字 `at` の直前で `[前半, 後半]`（前半は `[0, at)`、後半は `[at, len)`）に分割する。
///
/// `at` 番目のノードを [`access_index`] で根まで splay し、その左部分木を切り離すことで実現する。
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

/// ノード `x` を回転で根まで持ち上げる（splay 操作）。生ポインタで実装している理由は [`access_index`] を参照。
///
/// `x`・親・祖父の位置関係（一直線か、く の字か）に応じて zig-zig / zig-zag の2段回転を
/// まとめて行うことで、ならし計算量を $O(\log n)$ に抑える。
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

/// `x` をその親 `p` の位置まで1段回転させる。生ポインタで実装している理由は [`access_index`] を参照。
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

/// スプレー木のノード。`left`/`right`/`parent` は生ポインタで管理する（[`access_index`] の Safety notes を参照）。
pub struct Node<O: LazyOps> {
    /// 左の子。無ければ `null_mut()`。
    pub left: *mut Self,
    /// 右の子。無ければ `null_mut()`。
    pub right: *mut Self,
    /// 親。根なら `null_mut()`。
    pub parent: *mut Self,
    /// この部分木の要素数。
    pub len: usize,
    /// この部分木が左右反転待ちなら `true`（[`push`](Self::push) で子へ伝播する遅延フラグ）。
    pub rev: bool,
    /// このノード自身の値。
    pub value: O::Value,
    /// この部分木の集約値。
    pub acc: O::Acc,
    /// 未伝播の作用。[`push`](Self::push) で自分に適用し、子へ伝播する。
    pub lazy: Option<O::Lazy>,
}
impl<O: LazyOps> Node<O> {
    /// 値 `value` 単独からなる葉ノード（`len = 1`）を作る。
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

    /// 部分木を中間順（左・自分・右）で標準出力にダンプする（デバッグ用）。
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

    /// 左右の子を `push` してから、その `len`・`acc` を使って自分の `len`・`acc` を再計算する。
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

    /// 保留中の作用・反転フラグを自分自身に確定させ、子へ伝播する。
    ///
    /// `lazy` があれば `value`/`acc` に適用してから子の `lazy` へ合成し、`rev` が立っていれば
    /// 左右の子を入れ替えて子の `rev` を反転する。ノードの実データを読む前には必ず呼ぶこと。
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
