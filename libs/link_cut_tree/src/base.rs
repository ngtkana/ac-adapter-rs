/// [`Op`](crate::Op) を splay 木の内部表現へアダプトするための内部トレイト（非公開）
#[doc(hidden)]
pub trait OpBase {
    type Value: Clone;
    type InternalValue: Clone;

    fn identity() -> Self::InternalValue;

    fn mul(lhs: &Self::InternalValue, rhs: &Self::InternalValue) -> Self::InternalValue;

    fn into_front(value: Self::InternalValue) -> Self::Value;

    fn from_front(value: Self::Value) -> Self::InternalValue;

    fn rev(value: &mut Self::InternalValue);
}

/// Link-Cut Tree の実体
///
/// `crate` 直下に再エクスポートされている [`LinkCutTree`](crate::LinkCutTree),
/// [`CommutLinkCutTree`](crate::CommutLinkCutTree), [`NonCommutLinkCutTree`](crate::NonCommutLinkCutTree)
/// を通して使う。直接構築するには `O: OpBase` を満たす型が必要になるため、通常は使わない。
///
/// # 解説
///
/// 各節点は自分の親へのポインタ `parent` と、splay 木上の左右の子 `left`, `right` を持つ。
/// 森を構成する各根付き木は「優先パス」（根から葉方向へ続く 1 本道）に分解され、優先パス 1 本が
/// splay 木 1 本に対応する。splay 木内では節点は深さ順（根に近いほど左）に並ぶ。優先パス同士は、
/// パス下端の節点の `parent` が「パスの繋ぎ目の親（path-parent）」を指すことでつながる
/// （このときその親から見て自分は splay 木上の子ではないため、`is_splay_root` が真になる）。
///
/// `expose(x)` は根から `x` までを 1 本の優先パスに再編する中心操作で、`x` から `parent` を辿って
/// 根に向かいながら経路上の各 splay 木を `splay` して連結していく。他の操作（`link`, `cut`,
/// `evert`, `parent`, `fold` など）はすべて `expose` を軸に実装され、splay 木の償却解析により
/// 1 回あたり償却 $O(\log n)$ で動作する。
pub struct LinkCutTreeBase<O: OpBase> {
    nodes: Vec<Node<O>>,
}
impl<O: OpBase> LinkCutTreeBase<O> {
    /// 節点数 $n$ の互いに素な森を構築する
    ///
    /// 節点は $0, \dots, n-1$ の ID を持ち、初期状態では辺を持たない（各節点が孤立した根）。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let lct = LinkCutTree::new(3);
    /// ```
    pub fn new(n: usize) -> Self {
        Self {
            nodes: (0..n)
                .map(|id| Node {
                    id,
                    parent: std::ptr::null_mut(),
                    left: std::ptr::null_mut(),
                    right: std::ptr::null_mut(),
                    rev: false,
                    value: O::identity(),
                    acc: O::identity(),
                })
                .collect(),
        }
    }

    /// 各節点に初期値 `values` を割り当てた森を構築する
    ///
    /// 節点数はイテレータの長さに等しい。各節点は孤立した根として初期化される。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::CommutLinkCutTree;
    /// use link_cut_tree::Op;
    ///
    /// enum Add {}
    /// impl Op for Add {
    ///     type Value = i64;
    ///     fn identity() -> i64 {
    ///         0
    ///     }
    ///     fn op(lhs: &i64, rhs: &i64) -> i64 {
    ///         lhs + rhs
    ///     }
    /// }
    ///
    /// let lct = CommutLinkCutTree::<Add>::from_values([1, 2, 3]);
    /// ```
    pub fn from_values(values: impl IntoIterator<Item = O::Value>) -> Self {
        Self {
            nodes: values
                .into_iter()
                .map(O::from_front)
                .enumerate()
                .map(|(id, value)| Node {
                    id,
                    parent: std::ptr::null_mut(),
                    left: std::ptr::null_mut(),
                    right: std::ptr::null_mut(),
                    rev: false,
                    value: value.clone(),
                    acc: value,
                })
                .collect(),
        }
    }

    /// `p` を `c` の親とする有向辺を張る
    ///
    /// # 仕様
    ///
    /// `c` が属する木の根であること、かつ `p` と `c` が非連結であることを要求する。
    ///
    /// # Panics
    ///
    /// - `c` が根でないとき
    /// - `p` と `c` がすでに連結なとき
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(2);
    /// lct.link(0, 1);
    /// assert_eq!(lct.parent(1), Some(0));
    /// ```
    pub fn link(&mut self, p: usize, c: usize) {
        unsafe {
            let base = self.nodes.as_mut_ptr();
            let c = base.add(c);
            let p = base.add(p);
            expose(c);
            assert!((*c).left.is_null(), "c = {} is not a root", (*c).id);
            expose(p);
            assert!(
                (*c).parent.is_null(),
                "c = {} and p = {} are already connected",
                (*c).id,
                (*p).id
            );
            (*c).parent = p;
            (*p).right = c;
            update(p);
        }
    }

    /// `i` と `j` を無向辺で結ぶ
    ///
    /// すでに連結なら何もせず `false` を返す。そうでなければ `j` を根に付け替えてから `link(i, j)` する。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(2);
    /// assert!(lct.undirected_link(0, 1));
    /// assert!(!lct.undirected_link(0, 1)); // すでに連結
    /// ```
    pub fn undirected_link(&mut self, i: usize, j: usize) -> bool {
        if self.undirected_is_connected(i, j) {
            return false;
        }
        self.evert(j);
        self.link(i, j);
        true
    }

    /// `x` とその親を結ぶ辺を切断する
    ///
    /// `x` が根なら何もせず `None` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(2);
    /// lct.link(0, 1);
    /// assert_eq!(lct.cut(1), Some(0));
    /// assert_eq!(lct.cut(1), None); // すでに根
    /// ```
    pub fn cut(&mut self, x: usize) -> Option<usize> {
        unsafe {
            let x = self.nodes.as_mut_ptr().add(x);
            expose(x);
            let p = (*x).left;
            (*x).left = std::ptr::null_mut();
            let ans = if p.is_null() { None } else { Some((*p).id) };
            if !p.is_null() {
                (*p).parent = std::ptr::null_mut();
            }
            update(x);
            ans
        }
    }

    /// `i` と `j` の間の無向辺を切断する
    ///
    /// `i`, `j` 間に辺がなければ何もせず `false` を返す。あれば `i` を根に付け替えてから `cut(j)` する。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(2);
    /// lct.undirected_link(0, 1);
    /// assert!(lct.undirected_cut(0, 1));
    /// assert!(!lct.undirected_cut(0, 1)); // すでに非連結
    /// ```
    pub fn undirected_cut(&mut self, i: usize, j: usize) -> bool {
        if !self.undirected_has_edge(i, j) {
            return false;
        }
        self.evert(i);
        self.cut(j);
        true
    }

    /// `x` を根に付け替える
    ///
    /// `x` の属する木全体で、根から各節点への辺の向きを反転する。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(2);
    /// lct.link(0, 1);
    /// lct.evert(1);
    /// assert_eq!(lct.parent(0), Some(1));
    /// ```
    pub fn evert(&mut self, x: usize) {
        unsafe {
            let x = self.nodes.as_mut_ptr().add(x);
            expose(x);
            rev(x);
            push(x);
        }
    }

    /// `x` と `y` の間に辺があるかを判定する
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(2);
    /// lct.link(0, 1);
    /// assert!(lct.undirected_has_edge(0, 1));
    /// assert!(lct.undirected_has_edge(1, 0));
    /// ```
    pub fn undirected_has_edge(&mut self, x: usize, y: usize) -> bool {
        self.parent(x) == Some(y) || self.parent(y) == Some(x)
    }

    /// `x` と `y` が同じ木に属するかを判定する
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(3);
    /// lct.link(0, 1);
    /// assert!(lct.undirected_is_connected(0, 1));
    /// assert!(!lct.undirected_is_connected(0, 2));
    /// ```
    pub fn undirected_is_connected(&mut self, x: usize, y: usize) -> bool {
        if x == y {
            return true;
        }
        unsafe {
            let base = self.nodes.as_mut_ptr();
            let x = base.add(x);
            let y = base.add(y);
            expose(x);
            expose(y);
            !(*x).parent.is_null()
        }
    }

    /// `x` と `y` の最小共通祖先を返す
    ///
    /// `x` と `y` が非連結なら `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(3);
    /// lct.link(0, 1);
    /// lct.link(1, 2);
    /// assert_eq!(lct.lca(0, 2), Some(0));
    /// ```
    pub fn lca(&mut self, x: usize, y: usize) -> Option<usize> {
        if x == y {
            return Some(x);
        }
        unsafe {
            let base = self.nodes.as_mut_ptr();
            let x = base.add(x);
            let y = base.add(y);
            expose(x);
            let lca = expose(y);
            if (*x).parent.is_null() {
                None
            } else {
                Some((*lca).id)
            }
        }
    }

    /// `x` の値を `f` で更新する
    ///
    /// 更新後の値は `f(現在の値)`。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::CommutLinkCutTree;
    /// use link_cut_tree::Op;
    ///
    /// enum Add {}
    /// impl Op for Add {
    ///     type Value = i64;
    ///     fn identity() -> i64 {
    ///         0
    ///     }
    ///     fn op(lhs: &i64, rhs: &i64) -> i64 {
    ///         lhs + rhs
    ///     }
    /// }
    ///
    /// let mut lct = CommutLinkCutTree::<Add>::from_values([1, 2, 3]);
    /// lct.set(0, |v| v + 10);
    /// assert_eq!(lct.fold(0), 11);
    /// ```
    pub fn set(&mut self, x: usize, mut f: impl FnMut(O::Value) -> O::Value) {
        unsafe {
            let x = self.nodes.as_mut_ptr().add(x);
            expose(x);
            (*x).value = O::from_front(f(O::into_front((*x).value.clone())));
            update(x);
        }
    }

    /// `x` の属する木の根から `x` までのパスの集約値を返す
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::CommutLinkCutTree;
    /// use link_cut_tree::Op;
    ///
    /// enum Add {}
    /// impl Op for Add {
    ///     type Value = i64;
    ///     fn identity() -> i64 {
    ///         0
    ///     }
    ///     fn op(lhs: &i64, rhs: &i64) -> i64 {
    ///         lhs + rhs
    ///     }
    /// }
    ///
    /// let mut lct = CommutLinkCutTree::<Add>::from_values([1, 2, 3]);
    /// lct.link(0, 1);
    /// lct.link(1, 2);
    /// assert_eq!(lct.fold(2), 1 + 2 + 3);
    /// ```
    pub fn fold(&mut self, x: usize) -> O::Value {
        unsafe {
            let x = self.nodes.as_mut_ptr().add(x);
            expose(x);
            O::into_front((*x).acc.clone())
        }
    }

    /// `i` から `j` までのパスの集約値を返す
    ///
    /// `i` と `j` が非連結なら `None`。`i` を根に付け替えてから `j` への `fold` を行う。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::CommutLinkCutTree;
    /// use link_cut_tree::Op;
    ///
    /// enum Add {}
    /// impl Op for Add {
    ///     type Value = i64;
    ///     fn identity() -> i64 {
    ///         0
    ///     }
    ///     fn op(lhs: &i64, rhs: &i64) -> i64 {
    ///         lhs + rhs
    ///     }
    /// }
    ///
    /// let mut lct = CommutLinkCutTree::<Add>::from_values([1, 2, 3]);
    /// lct.undirected_link(0, 1);
    /// lct.undirected_link(1, 2);
    /// assert_eq!(lct.undirected_fold(0, 2), Some(1 + 2 + 3));
    /// ```
    pub fn undirected_fold(&mut self, i: usize, j: usize) -> Option<O::Value> {
        if !self.undirected_is_connected(i, j) {
            return None;
        }
        self.evert(i);
        Some(self.fold(j))
    }

    /// `x` の親の ID を返す
    ///
    /// `x` が根なら `None`。
    ///
    /// # 例
    ///
    /// ```
    /// use link_cut_tree::LinkCutTree;
    /// let mut lct = LinkCutTree::new(2);
    /// lct.link(0, 1);
    /// assert_eq!(lct.parent(1), Some(0));
    /// assert_eq!(lct.parent(0), None);
    /// ```
    pub fn parent(&mut self, x: usize) -> Option<usize> {
        unsafe {
            let x = self.nodes.as_mut_ptr().add(x);
            expose(x);
            let mut p = (*x).left;
            if p.is_null() {
                return None;
            }
            while !(*p).right.is_null() {
                p = (*p).right;
            }
            splay(p);
            Some((*p).id)
        }
    }
}

#[derive(Clone, Copy)]
struct Node<O: OpBase> {
    id: usize,
    parent: *mut Self,
    left: *mut Self,
    right: *mut Self,
    rev: bool,
    value: O::InternalValue,
    acc: O::InternalValue,
}

unsafe fn is_splay_root<O: OpBase>(x: *mut Node<O>) -> bool {
    unsafe {
        let p = (*x).parent;
        p.is_null() || (!std::ptr::eq((*p).left, x) && !std::ptr::eq((*p).right, x))
    }
}

unsafe fn push<O: OpBase>(x: *mut Node<O>) {
    unsafe {
        if (*x).rev {
            let l = (*x).left;
            let r = (*x).right;
            if !l.is_null() {
                rev(l);
            }
            if !r.is_null() {
                rev(r);
            }
            (*x).rev = false;
        }
    }
}

unsafe fn update<O: OpBase>(x: *mut Node<O>) {
    unsafe {
        (*x).acc = (*x).value.clone();
        let l = (*x).left;
        let r = (*x).right;
        if !l.is_null() {
            (*x).acc = O::mul(&(*l).acc, &(*x).acc);
        }
        if !r.is_null() {
            (*x).acc = O::mul(&(*x).acc, &(*r).acc);
        }
    }
}

unsafe fn rev<O: OpBase>(x: *mut Node<O>) {
    unsafe {
        std::mem::swap(&mut (*x).left, &mut (*x).right);
        O::rev(&mut (*x).acc);
        (*x).rev ^= true;
    }
}

unsafe fn expose<O: OpBase>(x: *mut Node<O>) -> *mut Node<O> {
    unsafe {
        let mut last = std::ptr::null_mut();
        let mut current = x;
        while !current.is_null() {
            splay(current);
            (*current).right = last;
            update(current);
            last = current;
            current = (*current).parent;
        }
        splay(x);
        last
    }
}

unsafe fn splay<O: OpBase>(x: *mut Node<O>) {
    unsafe {
        push(x);
        while !is_splay_root(x) {
            let p = (*x).parent;
            if is_splay_root(p) {
                push(p);
                push(x);
                if std::ptr::eq((*p).left, x) {
                    rotate_right(p);
                } else {
                    rotate_left(p);
                }
            } else {
                let g = (*p).parent;
                push(g);
                push(p);
                push(x);
                #[allow(clippy::collapsible_else_if)]
                if std::ptr::eq((*p).left, x) {
                    if std::ptr::eq((*g).left, p) {
                        rotate_right(g);
                        rotate_right(p);
                    } else {
                        rotate_right(p);
                        rotate_left(g);
                    }
                } else {
                    if std::ptr::eq((*g).left, p) {
                        rotate_left(p);
                        rotate_right(g);
                    } else {
                        rotate_left(g);
                        rotate_left(p);
                    }
                }
            }
        }
    }
}

unsafe fn rotate_left<O: OpBase>(l: *mut Node<O>) {
    unsafe {
        let r = (*l).right;
        let p = (*l).parent;
        let c = (*r).left;
        (*l).right = c;
        if !c.is_null() {
            (*c).parent = l;
        }
        (*r).left = l;
        (*l).parent = r;
        (*r).parent = p;
        update(l);
        update(r);
        if !p.is_null() {
            if std::ptr::eq((*p).left, l) {
                (*p).left = r;
            } else if std::ptr::eq((*p).right, l) {
                (*p).right = r;
            }
            update(p);
        }
    }
}

unsafe fn rotate_right<O: OpBase>(r: *mut Node<O>) {
    unsafe {
        let l = (*r).left;
        let p = (*r).parent;
        let c = (*l).right;
        (*r).left = c;
        if !c.is_null() {
            (*c).parent = r;
        }
        (*l).right = r;
        (*r).parent = l;
        (*l).parent = p;
        update(r);
        update(l);
        if !p.is_null() {
            if std::ptr::eq((*p).left, r) {
                (*p).left = l;
            } else if std::ptr::eq((*p).right, r) {
                (*p).right = l;
            }
            update(p);
        }
    }
}
