//! Splay 木で、列を管理するデータ構造です。
//!
//! [詳しいインターフェースは `SplayTree`](SplayTree) のドキュメントをご覧ください。
//!
//! # 概要
//!
//! [`SplayTree`] は、列 `a = [ a[0], a[1], ..., a[n-1] ]`
//! を管理します。要素の間には（可換とは限らない）積が定義されているとします。
//! また、列の結合を和で表記します。このとき、主に次のことを実現するデータ構造です。
//!
//! | おなまえ                                  | 計算量        | やること                          |
//! | -                                         | -             | -                                 |
//! | [`new`](SplayTree::new)                   | O(1)          | `a = []`                          |
//! | [`entry(i)`](SplayTree::entry)            | O(lg n) am.   | `a[i]` のハンドラ                 |
//! | [`fold(l..r)`](SplayTree::fold)           | O(lg n) am.   | `a[l] * a[l+1] * ... * a[r-1]`    |
//! | [`insert(i, x)`](SplayTree::insert)       | O(lg n) am.   | `a = a[..i] + [x] + a[i+1..]`     |
//! | [`delete(i)`](SplayTree::delete)          | O(lg n) am.   | `a = a[..i-1] + a[i+1..]`         |
//! | [`append(b)`](SplayTree::append)          | O(lg n) am.   | `a = a + b`                       |
//! | [`split_off(i)`](SplayTree::split_off)    | O(lg n) am.   | `a = a[..i], return a[i..]`       |
//!

mod node;

#[cfg(test)]
pub mod brute;
#[cfg(test)]
mod test_cat;
#[cfg(test)]
mod tests;

use {
    node::{deep_free, get, merge, split, Node},
    std::{
        cell::Cell,
        cmp::Ordering,
        fmt::Debug,
        hash::Hash,
        iter::FromIterator,
        marker::PhantomData,
        mem::replace,
        ops::{Bound, Deref, DerefMut, Drop, Index, Range, RangeBounds},
        ptr::null_mut,
    },
};

/// [`Acc`](LazyOps::Acc), [`Lazy`](LazyOps::Lazy) をユニット型にして、演算を回避する型です。
pub struct Nop<T>(PhantomData<fn(T) -> T>);
impl<T: Value> LazyOps for Nop<T> {
    type Value = T;
    type Acc = ();
    type Lazy = ();
    fn proj(_: &Self::Value) -> Self::Acc {}
    fn op(&(): &Self::Acc, &(): &Self::Acc) -> Self::Acc {}
    fn act_value(&(): &Self::Lazy, _value: &mut Self::Value) {}
    fn act_acc(&(): &Self::Lazy, &mut (): &mut Self::Acc) {}
    fn lazy_propagate(&(): &Self::Lazy, &mut (): &mut Self::Lazy) {}
}
/// [`Lazy`](LazyOps::Lazy) をユニット型にして、演算を回避する型です。
pub struct NoLazy<T>(PhantomData<fn(T) -> T>);
impl<O: Ops> LazyOps for NoLazy<O> {
    type Value = O::Value;
    type Acc = O::Acc;
    type Lazy = ();
    fn proj(value: &Self::Value) -> Self::Acc {
        O::proj(value)
    }
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc {
        O::op(lhs, rhs)
    }
    fn act_value(&(): &Self::Lazy, _value: &mut Self::Value) {}
    fn act_acc(&(): &Self::Lazy, _acc: &mut Self::Acc) {}
    fn lazy_propagate(&(): &Self::Lazy, &mut (): &mut Self::Lazy) {}
}

/// [`Sized`], [`Debug`], [`Clone`] 取りまとめ役です。
pub trait Value: Sized + Debug + Clone {}
impl<T: Sized + Debug + Clone> Value for T {}

/// 演算
pub trait Ops {
    /// 値型
    type Value: Value;
    /// 集約値型
    type Acc: Value;
    /// 集約化
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 演算
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
}

/// 遅延作用つき演算
pub trait LazyOps {
    /// 値型
    type Value: Value;
    /// 集約値型
    type Acc: Value;
    /// 遅延値型
    type Lazy: Value;
    /// 集約化
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 演算
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
    /// 値への作用
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value);
    /// 集約値への作用
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc);
    /// 遅延値の伝播
    fn lazy_propagate(upper: &Self::Lazy, lower: &mut Self::Lazy);
}

/// スプレー木
///
/// # Examples
///
/// ## 演算の必要がない場合
///
/// [`Nop`] を使いましょう。
///
/// ```
/// # use splay_tree::{SplayTree, Nop};
/// // FromIterator
/// let mut splay = (0..4).collect::<SplayTree<Nop<i32>>>();
///
/// // get
/// assert_eq!(splay.get(2), Some(&2));
///
/// // insert （push_{front,back} もよろしくです。）
/// splay.insert(3, -1);
///
/// // delete（pop_{front,back} もよろしくです。）
/// assert_eq!(splay.delete(0), 0);
///
/// // iter
/// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![1, 2, -1, 3]);
/// assert_eq!(splay.iter().rev().copied().collect::<Vec<_>>(), vec![3, -1, 2, 1]);
/// assert_eq!(splay.iter().step_by(2).copied().collect::<Vec<_>>(), vec![1, -1]);
/// assert_eq!(splay.iter().rev().step_by(2).copied().collect::<Vec<_>>(), vec![3, 2]);
///
/// // append（prepend もよろしくです。）
/// splay.append(&mut (4..8).collect::<SplayTree<_>>());
///
/// // split_off（split_on もよろしくです。）
/// let split_off = splay.split_off(6);
/// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![1, 2, -1, 3, 4, 5]);
/// assert_eq!(split_off.iter().copied().collect::<Vec<_>>(), vec![6, 7]);
/// ```
///
/// ## 遅延作用の必要ない場合： 演算 `+` の例
///
/// [`NoLazy`] を使いましょう。
///
/// ```
/// # use splay_tree::{SplayTree, Ops, NoLazy};
/// enum O {}
/// impl Ops for O {
///     type Value = i32;
///     type Acc = i32;
///     fn proj(&value: &Self::Value) -> Self::Acc {
///         value
///     }
///     fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc {
///         lhs + rhs
///     }
/// }
///
/// // FromIterator
/// let mut splay = vec![1, 2, 4, 8].into_iter().collect::<SplayTree<NoLazy<O>>>();
///
/// // fold, fold_all
/// assert_eq!(splay.fold(1..3), Some(2 + 4));
///
/// // push_front, pop_back
/// splay.push_front(-10);
/// assert_eq!(splay.pop_back(), Some(8));
/// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![-10, 1, 2, 4]);
///
/// // fold
/// assert_eq!(splay.fold(..3), Some(-10 + 1 + 2));
/// ```
pub struct SplayTree<O: LazyOps> {
    root: Cell<*mut Node<O>>,
}
impl<O: LazyOps> Debug for SplayTree<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl<O: LazyOps> Clone for SplayTree<O> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}
impl<O: LazyOps> Default for SplayTree<O> {
    fn default() -> Self {
        Self {
            root: Cell::new(null_mut()),
        }
    }
}
impl<O: LazyOps> PartialEq for SplayTree<O>
where
    O::Value: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(x, y)| x == y)
    }
}
impl<O: LazyOps> Eq for SplayTree<O> where O::Value: Eq {}
impl<O: LazyOps> PartialOrd for SplayTree<O>
where
    O::Value: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        for (x, y) in self.iter().zip(other.iter()) {
            match x.partial_cmp(y) {
                Some(Ordering::Equal) => (),
                non_eq => return non_eq,
            }
        }
        self.len().partial_cmp(&other.len())
    }
}
impl<O: LazyOps> Ord for SplayTree<O>
where
    O::Value: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        for (x, y) in self.iter().zip(other.iter()) {
            match x.cmp(y) {
                Ordering::Equal => (),
                non_eq => return non_eq,
            }
        }
        self.len().cmp(&other.len())
    }
}
impl<O: LazyOps> Hash for SplayTree<O>
where
    O::Value: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.iter().for_each(|x| x.hash(state))
    }
}
impl<O: LazyOps> SplayTree<O> {
    /// 空の [`SplayTree`] を作ります。
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    pub fn new() -> Self {
        None.into_iter().collect()
    }
    /// 管理している配列が空であるときに `true` を返します。
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.get().is_null()
    }
    /// 管理している配列の長さを返します。
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = (0..10).collect::<SplayTree<Nop<_>>>();
    /// assert_eq!(splay.len(), 10);
    /// ```
    pub fn len(&self) -> usize {
        let root = self.root.get();
        unsafe { root.as_ref() }.map_or(0, |root| root.len)
    }
    /// `index` 番目の要素への参照を返します。範囲外のときには `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = (0..10).collect::<SplayTree<Nop<_>>>();
    /// assert_eq!(splay.get(2), Some(&2));
    /// ```
    ///
    ///
    /// # 参照を返して大丈夫な理由
    ///
    /// 畳み込みの値と違って、木の形が変わっても参照先の値が書き換わらないためです。
    ///
    ///
    /// # お友達のご紹介
    ///
    /// [`Index`] トレイトは、スライス型などと同じく範囲外でパニックします。
    ///
    pub fn get(&self, index: usize) -> Option<&O::Value> {
        if self.len() <= index {
            return None;
        }
        let root = self.root.get();
        let root = unsafe { get(root, index).as_mut() }.unwrap();
        self.root.set(root);
        Some(&root.value)
    }
    /// `index` 番目を編集できるエントリーを返します。範囲外のときには `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// *splay.entry(1).unwrap() += 10;
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 11, 2]);
    /// ```
    pub fn entry(&mut self, index: usize) -> Option<Entry<'_, O>> {
        if self.len() <= index {
            None
        } else {
            self.root.set(unsafe { get(self.root.get(), index) });
            Some(Entry { splay: self })
        }
    }
    /// 添え字範囲 `range` の指す要素全てに `lazy` を作用します。
    ///
    /// # Panics
    ///
    /// 変な区間
    ///
    ///
    /// # Examples
    ///
    /// - 畳み込み: min
    /// - 作用: add
    ///
    /// の例です。
    ///
    /// ```
    /// # use splay_tree::{SplayTree, LazyOps};
    /// enum O {}
    /// impl LazyOps for O {
    ///     type Value = i32;
    ///     type Acc = i32;
    ///     type Lazy = i32;
    ///     fn proj(&value: &Self::Value) -> Self::Acc {
    ///         value
    ///     }
    ///     fn op(&lhs: &Self::Acc, &rhs: &Self::Acc) -> Self::Acc {
    ///         lhs.min(rhs)
    ///     }
    ///     fn act_value(&lazy: &Self::Lazy, value: &mut Self::Value) {
    ///         *value += lazy;
    ///     }
    ///     fn act_acc(&lazy: &Self::Lazy, acc: &mut Self::Acc) {
    ///         *acc += lazy;
    ///     }
    ///     fn lazy_propagate(upper: &Self::Lazy, lower: &mut Self::Lazy) {
    ///         *lower += upper;
    ///     }
    /// }
    ///
    /// // 初期化
    /// let mut splay = vec![17, 28, 6, 11].into_iter().collect::<SplayTree<O>>();
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![17, 28, 6, 11]);
    /// assert_eq!(splay.fold(..), Some(6));
    ///
    /// // 真ん中 2 つに 10 を加算
    /// splay.act(1..3, 10);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![17, 38, 16, 11]);
    /// assert_eq!(splay.fold(..), Some(11));
    /// ```
    pub fn act(&mut self, range: impl RangeBounds<usize>, lazy: O::Lazy) {
        let Range { start, end } = into_range(self.len(), range);
        let root = self.root.get();
        let [lc, r] = unsafe { split(root, end) };
        let [l, c] = unsafe { split(lc, start) };
        unsafe {
            if let Some(c) = c.as_mut() {
                c.lazy = Some(lazy);
                c.push();
            }
        }
        self.root.set(unsafe { merge(merge(l, c), r) });
    }
    /// `range` を添え字範囲として畳み込みます。空区間のときには `None` を返します。
    ///
    /// # Panics
    ///
    /// 変な区間
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Ops, NoLazy};
    /// enum O {}
    /// impl Ops for O {
    ///     type Value = i32;
    ///     type Acc = i32;
    ///     fn proj(&value: &Self::Value) -> Self::Acc {
    ///         value
    ///     }
    ///     fn op(&lhs: &Self::Acc, &rhs: &Self::Acc) -> Self::Acc {
    ///         lhs + rhs
    ///     }
    /// }
    /// let splay = (0..10).map(|x| 1 << x).collect::<SplayTree<NoLazy<O>>>();
    /// assert_eq!(splay.fold(..), Some(1023));
    /// assert_eq!(splay.fold(8..), Some(768));
    /// assert_eq!(splay.fold(..4), Some(15));
    /// assert_eq!(splay.fold(2..5), Some(28));
    /// ```
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Acc> {
        let Range { start, end } = into_range(self.len(), range);
        let root = self.root.get();
        let [lc, r] = unsafe { split(root, end) };
        let [l, c] = unsafe { split(lc, start) };
        let ans = unsafe { c.as_ref() }.map(|c| c.acc.clone());
        self.root.set(unsafe { merge(merge(l, c), r) });
        ans
    }
    /// `index` 番目に要素 `x` を挿入します。範囲外の場合はパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// splay.insert(1, 10);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 10, 1, 2]);
    /// ```
    pub fn insert(&mut self, index: usize, value: O::Value) {
        assert!(index <= self.len());
        let root = self.root.get();
        let node = Box::into_raw(Box::new(Node::new(value)));
        let node = unsafe { node.as_mut() }.unwrap();
        let root = if self.len() == index {
            node.left = root;
            if let Some(root) = unsafe { root.as_mut() } {
                root.parent = node;
            }
            unsafe { node.update() };
            node
        } else {
            let right = unsafe { get(root, index).as_mut() }.unwrap();
            let left = replace(&mut right.left, null_mut());
            unsafe { right.update() };
            if let Some(left) = unsafe { left.as_mut() } {
                left.parent = null_mut();
            }
            unsafe { merge(merge(left, node), right) }
        };
        self.root.set(root);
    }
    /// `index` 番目の要素を削除します。範囲外の場合はパニックします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// splay.delete(1);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 2]);
    /// ```
    pub fn delete(&mut self, index: usize) -> O::Value {
        assert!(index < self.len());
        let deleting = unsafe { get(self.root.get(), index).as_mut() }.unwrap();
        let left = replace(&mut deleting.left, null_mut());
        let right = replace(&mut deleting.right, null_mut());
        unsafe { deleting.update() };
        if let Some(left) = unsafe { left.as_mut() } {
            left.parent = null_mut();
        }
        if let Some(right) = unsafe { right.as_mut() } {
            right.parent = null_mut();
        }
        self.root.set(unsafe { merge(left, right) });
        unsafe { Box::from_raw(deleting) }.value
    }
    /// 受け取ったスプレー木を空にしつつ、それがもともと持っていた要素をすべて前側に挿入します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// splay.prepend(&mut (10..13).collect::<SplayTree<Nop<_>>>());
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 11, 12, 0, 1, 2]);
    /// ```
    pub fn prepend(&mut self, head: &mut Self) {
        let root = self.root.get();
        self.root.set(unsafe { merge(head.root.get(), root) });
        head.root.set(null_mut());
    }
    /// 受け取ったスプレー木を空にしつつ、それがもともと持っていた要素をすべて後側に挿入します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// splay.append(&mut (10..13).collect::<SplayTree<Nop<_>>>());
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2, 10, 11, 12]);
    /// ```
    pub fn append(&mut self, tail: &mut Self) {
        let root = self.root.get();
        self.root.set(unsafe { merge(root, tail.root.get()) });
        tail.root.set(null_mut());
    }
    /// 管理している配列を `at` で分けて、前側を自分用、後側を戻り値用にします。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..6).collect::<SplayTree<Nop<_>>>();
    /// let rhs = splay.split_off(3);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2]);
    /// assert_eq!(rhs.iter().copied().collect::<Vec<_>>(), vec![3, 4, 5]);
    /// ```
    pub fn split_off(&mut self, at: usize) -> Self {
        let root = self.root.get();
        let [root, right] = unsafe { split(root, at) };
        self.root.set(root);
        Self {
            root: Cell::new(right),
        }
    }
    /// 管理している配列を `at` で分けて、前側を戻り値、後側を自分用にします。
    ///
    /// お名前はふざけました。（小声）（だって
    /// [`LinkedList`](std::collections::LinkedList) にないんだもん）
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..6).collect::<SplayTree<Nop<_>>>();
    /// let rhs = splay.split_on(3);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![3, 4, 5]);
    /// assert_eq!(rhs.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2]);
    /// ```
    pub fn split_on(&mut self, at: usize) -> Self {
        let root = self.root.get();
        let [left, root] = unsafe { split(root, at) };
        self.root.set(root);
        Self {
            root: Cell::new(left),
        }
    }
    /// 管理している配列の後ろに `x` を追加します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// splay.push_back(10);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2, 10]);
    /// ```
    pub fn push_back(&mut self, value: O::Value) {
        let node = Box::into_raw(Box::new(Node::new(value)));
        let root = self.root.get();
        self.root.set(unsafe { merge(root, node) });
    }
    /// 管理している配列の前に `x` を追加します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// splay.push_front(10);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 0, 1, 2]);
    /// ```
    pub fn push_front(&mut self, value: O::Value) {
        let node = Box::into_raw(Box::new(Node::new(value)));
        let root = self.root.get();
        self.root.set(unsafe { merge(node, root) });
    }
    /// 管理している配列の最後の要素を削除して返します。なければ `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// assert_eq!(splay.pop_back(), Some(2));
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 1]);
    /// ```
    pub fn pop_back(&mut self) -> Option<O::Value> {
        let root = self.root.get();
        let root = unsafe { root.as_mut() }?;
        let [root, single] = unsafe { split(root, root.len - 1) };
        self.root.set(root);
        Some(unsafe { Box::from_raw(single).value })
    }
    /// 管理している配列の最初の要素を削除して返します。なければ `None` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let mut splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// assert_eq!(splay.pop_front(), Some(0));
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![1, 2]);
    /// ```
    pub fn pop_front(&mut self) -> Option<O::Value> {
        let root = self.root.get();
        let root = unsafe { root.as_mut() }?;
        let [single, root] = unsafe { split(root, 1) };
        self.root.set(root);
        Some(unsafe { Box::from_raw(single).value })
    }
    /// 管理している要素を左から順番に捜査するイテレータを返します。
    ///
    /// # できること
    ///
    /// [`DoubleEndedIterator`], [`ExactSizeIterator`] を実装しています。
    /// 実装は [`Index::index`] を呼びまくっているだけなのでいろいろできるのですが、
    /// とりあえず [`Iterator::nth`], [`DoubleEndedIterator::nth_back`] だけ高速化してあります。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = (0..3).collect::<SplayTree<Nop<_>>>();
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2]);
    /// assert_eq!(splay.iter().copied().rev().collect::<Vec<_>>(), vec![2, 1, 0]);
    /// assert_eq!(splay.iter().copied().len(), 3);
    /// assert_eq!(splay.iter().copied().rev().len(), 3);
    /// ```
    pub fn iter(&self) -> Iter<'_, O> {
        Iter {
            splay: self,
            start: 0,
            end: self.len(),
        }
    }
    /// [`iter`](Self::iter) の部分を返すバージョンです。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = (0..5).collect::<SplayTree<Nop<_>>>();
    /// assert_eq!(splay.range(1..=3).copied().collect::<Vec<_>>(), vec![1, 2, 3]);
    /// assert_eq!(splay.range(1..=3).copied().rev().collect::<Vec<_>>(), vec![3, 2, 1]);
    /// assert_eq!(splay.range(1..=3).copied().len(), 3);
    /// assert_eq!(splay.range(1..=3).copied().rev().len(), 3);
    /// ```
    pub fn range(&self, range: impl RangeBounds<usize>) -> Iter<'_, O> {
        let Range { start, end } = into_range(self.len(), range);
        Iter {
            splay: self,
            start,
            end,
        }
    }
}

impl<O: LazyOps> Index<usize> for SplayTree<O> {
    type Output = O::Value;
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<O: LazyOps> FromIterator<O::Value> for SplayTree<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut root = null_mut();
        for value in iter {
            let node = Box::into_raw(Box::new(Node::new(value)));
            root = unsafe { merge(root, node) };
        }
        let root = Cell::new(root);
        Self { root }
    }
}

/// [`SplayTree::entry`] の戻り値型
pub struct Entry<'a, O: LazyOps> {
    splay: &'a mut SplayTree<O>,
}
impl<'a, O: LazyOps> Deref for Entry<'a, O> {
    type Target = O::Value;
    fn deref(&self) -> &Self::Target {
        let root = self.splay.root.get();
        let root = unsafe { root.as_ref() }.unwrap();
        &root.value
    }
}
impl<'a, O: LazyOps> DerefMut for Entry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        let root = self.splay.root.get();
        let root = unsafe { root.as_mut() }.unwrap();
        &mut root.value
    }
}
impl<'a, O: LazyOps> Drop for Entry<'a, O> {
    fn drop(&mut self) {
        let root = self.splay.root.get();
        let root = unsafe { root.as_mut() }.unwrap();
        unsafe { root.update() }
    }
}

impl<O: LazyOps> Drop for SplayTree<O> {
    fn drop(&mut self) {
        let root = self.root.get();
        unsafe { deep_free(root) }
    }
}

/// イテレータ型です。[`ExactSizeIterator`], [`DoubleEndedIterator`] を実装しており、
/// [`Iterator::nth`], [`DoubleEndedIterator::nth_back`] をオーバーライドしています。
pub struct Iter<'a, O: LazyOps> {
    splay: &'a SplayTree<O>,
    start: usize,
    end: usize,
}
impl<'a, O: LazyOps> Iterator for Iter<'a, O> {
    type Item = &'a O::Value;
    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            let res = &self.splay[self.start];
            self.start += 1;
            Some(res)
        }
    }
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if self.len() <= n {
            self.start = self.end;
            None
        } else {
            self.start += n;
            let res = &self.splay[self.start];
            self.start += 1;
            Some(res)
        }
    }
}
impl<'a, O: LazyOps> ExactSizeIterator for Iter<'a, O> {
    fn len(&self) -> usize {
        self.end - self.start
    }
}

impl<'a, O: LazyOps> DoubleEndedIterator for Iter<'a, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            self.end -= 1;
            Some(&self.splay[self.end])
        }
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.len() <= n {
            self.end = self.start;
            None
        } else {
            self.end -= n + 1;
            Some(&self.splay[self.end])
        }
    }
}

fn into_range(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start - 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end + 1,
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };
    if len < start {
        splay_tree_start_index_len_fail(start, len);
    }
    if len < end {
        splay_tree_end_index_len_fail(end, len);
    }
    if start > end {
        splay_tree_index_order_fail(start, end)
    }
    start..end
}
fn splay_tree_start_index_len_fail(index: usize, len: usize) -> ! {
    panic!(
        "range start index {} out of range for splay tree of length {}",
        index, len
    );
}
fn splay_tree_end_index_len_fail(index: usize, len: usize) -> ! {
    panic!(
        "range end index {} out of range for splay tree of length {}",
        index, len
    );
}
fn splay_tree_index_order_fail(index: usize, end: usize) -> ! {
    panic!("splay tree index starts at {} but ends at {}", index, end);
}
