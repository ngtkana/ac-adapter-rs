use super::Navi2;
use super::Navi3;
use super::Op;
use std::ptr::NonNull;

type Nn<O> = NonNull<Node<O>>;
pub(super) type Onn<O> = Option<NonNull<Node<O>>>;

/// スプレイ木の1ノード。
///
/// `left` / `right` / `parent` は生ポインタ（[`NonNull`]）で子・親を指す侵入型のリンクで、
/// ノード自体は常にヒープ上の `Box` として確保される（対応する解放は [`free_subtree`] が行う）。
pub(super) struct Node<O: Op> {
    /// ノードが持つ値。集約成分は `update` が呼ばれるたびに最新化される。
    pub(super) store: O::Store,
    left: Onn<O>,
    right: Onn<O>,
    parent: Onn<O>,
}
impl<O: Op> Node<O> {
    /// 左右の子・親を持たない単独ノードを作る。
    pub(super) fn new(store: O::Store) -> Self {
        Self {
            store,
            left: None,
            right: None,
            parent: None,
        }
    }

    /// 左右の子の集約値から `store` の集約値を再計算する（[`Op::update`] を呼び出す）。
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

/// 中順（in-order）走査で `f` を各ノードの値に適用する。
pub(super) fn visit<T, O: Op<Store = T>>(root: Onn<O>, f: &mut impl FnMut(&T)) {
    let Some(root) = root else { return };
    unsafe {
        visit((*root.as_ptr()).left, f);
        f(&(*root.as_ptr()).store);
        visit((*root.as_ptr()).right, f);
    }
}

/// 2つの部分木 `left`, `right`（`left` の全要素が `right` の全要素より小さい）を1つに併合する。
///
/// `left` の最大要素（最も右のノード）をスプレイでルートに浮かせ、その右の子として `right` を繋ぐ。
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

/// `left`, `center`, `right`（この順に全要素が単調に増加）を `center` を根として結合する。
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

/// クロージャ `f` が指す位置で `root` を2つの部分木に分割する。
///
/// `f` が返す方向にたどり着いたノードを境目としてスプレイでルートに浮かせたのち、
/// その方向の子を切り離す。
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

/// [`split3`] の結果。目的のノードが見つかれば `Success`、見つからなければ元の木を `Failure` で返す。
pub(super) enum Split3Result<O: Op> {
    Success(Onn<O>, Nn<O>, Onn<O>),
    Failure(Onn<O>),
}

/// クロージャ `f` で指定したノードを木から切り出し、左右の部分木と共に返す。
///
/// `f` が [`Navi3::Found`] を返すノードをスプレイでルートに浮かせ、その左右の子を切り離して返す。
/// 見つからなければスプレイ済みの木を [`Split3Result::Failure`] に包んで返す。
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

/// `x` を回転によりルートまで浮上させる（スプレイ操作）。
///
/// 親と祖父母の位置関係に応じて zig-zig / zig-zag の2段回転を行い、根の直下では単純な1段回転を行う。
/// zig-zig を優先することでならし $O(\log n)$ が保証される。
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

/// `x` を左回転し、`x` の右の子を新しい根として返す。
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

/// `x` を右回転し、`x` の左の子を新しい根として返す。
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

/// 部分木の全ノードを（スタックを使い非再帰で）解放する。
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

/// `root` からクロージャ `f` に従って探索し、たどり着いたノードをスプレイしてルートにする。
///
/// 戻り値は新しい根と、そのノードで `f` が返した [`Navi3`]（`GoDownLeft` / `GoDownRight` は
/// 子が無く探索が止まった場合、`Found` は探索対象が見つかった場合）。
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
