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

use std::hash::Hash;

mod node;

use {
    self::node::{deep_free, delete, get, insert, merge, split, Node},
    std::{
        cell::Cell,
        cmp::Ordering,
        fmt::Debug,
        iter::FromIterator,
        marker::PhantomData,
        ops::{Bound, Deref, DerefMut, Index, Range, RangeBounds},
        ptr::null_mut,
    },
};

/// [`Acc`](Ops::Acc) をユニット型にして、演算を回避する型です。
pub struct Nop<T>(PhantomData<fn(T) -> T>);
impl<T: Sized + Debug + Clone> Ops for Nop<T> {
    type Value = T;
    type Acc = ();
    fn proj(_: &Self::Value) -> Self::Acc {}
    fn op(&(): &Self::Acc, &(): &Self::Acc) -> Self::Acc {}
}

/// 演算
pub trait Ops {
    /// 値型
    type Value: Sized + Debug + Clone;
    /// サマリー型
    type Acc: Sized + Debug + Clone;
    /// サマリー化
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 演算
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
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
/// ## 演算 `+` の例
///
/// 戻り値が `Option<O::Value>` です。
///
/// ```
/// # use splay_tree::{SplayTree, Ops};
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
/// let mut splay = vec![1, 2, 4, 8].into_iter().collect::<SplayTree<O>>();
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
pub struct SplayTree<O: Ops>(Cell<*mut Node<O>>);
impl<O: Ops> Debug for SplayTree<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl<O: Ops> Clone for SplayTree<O> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}
impl<O: Ops> Default for SplayTree<O> {
    fn default() -> Self {
        Self(Cell::new(null_mut()))
    }
}
impl<O: Ops> PartialEq for SplayTree<O>
where
    O::Value: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(x, y)| x == y)
    }
}
impl<O: Ops> Eq for SplayTree<O> where O::Value: Eq {}
impl<O: Ops> PartialOrd for SplayTree<O>
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
impl<O: Ops> Ord for SplayTree<O>
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
impl<O: Ops> Hash for SplayTree<O>
where
    O::Value: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.iter().for_each(|x| x.hash(state))
    }
}
impl<O: Ops> SplayTree<O> {
    /// 新しい [`SplayTree`] を作ります。
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }
    /// 管理している配列が空であるときに `true` を返します。
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.get().is_null()
    }
    /// 管理している配列の長さを返します。
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = (0..10).collect::<SplayTree<Nop<_>>>();
    /// assert_eq!(splay.len(), 10);
    /// ```
    pub fn len(&self) -> usize {
        unsafe { self.0.get().as_ref().map_or(0, |r| r.len) }
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
            None
        } else {
            assert!(index < self.len());
            self.0.set(unsafe { get(self.0.get(), index) });
            Some(unsafe { &(*self.0.get()).value })
        }
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
            *self.0.get_mut() = unsafe { get(self.0.get(), index) };
            Some(Entry(self))
        }
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
    /// # use splay_tree::{SplayTree, Ops};
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
    /// let splay = (0..10).map(|x| 1 << x).collect::<SplayTree<O>>();
    /// assert_eq!(splay.fold(..), Some(1023));
    /// assert_eq!(splay.fold(8..), Some(768));
    /// assert_eq!(splay.fold(..4), Some(15));
    /// assert_eq!(splay.fold(2..5), Some(28));
    /// ```
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Acc> {
        let Range { start, end } = into_range(self.len(), range);
        let [lc, r] = unsafe { split(self.0.get(), end) };
        let [l, c] = unsafe { split(lc, start) };
        let ans = unsafe { c.as_ref().map(|c| &c.fold) }.cloned();
        self.0.set(unsafe { merge(merge(l, c), r) });
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
    pub fn insert(&mut self, index: usize, x: O::Value) {
        assert!(index <= self.len());
        let node = Box::into_raw(Box::new(Node::new(x)));
        self.0.set(if self.0.get().is_null() {
            node
        } else {
            unsafe { insert(self.0.get(), index, node) }
        });
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
        let [root, node] = unsafe { delete(self.0.get(), index) };
        self.0.set(root);
        unsafe { Box::from_raw(node).value }
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
        self.0.set(unsafe { merge(head.0.get(), self.0.get()) });
        head.0.set(null_mut());
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
        self.0.set(unsafe { merge(self.0.get(), tail.0.get()) });
        tail.0.set(null_mut());
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
        let [l, r] = unsafe { split(self.0.get(), at) };
        self.0.set(l);
        Self(Cell::new(r))
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
        let [l, r] = unsafe { split(self.0.get(), at) };
        self.0.set(r);
        Self(Cell::new(l))
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
    pub fn push_back(&mut self, x: O::Value) {
        let node = Box::into_raw(Box::new(Node::new(x)));
        self.0.set(unsafe { merge(self.0.get(), node) });
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
    pub fn push_front(&mut self, x: O::Value) {
        let node = Box::into_raw(Box::new(Node::new(x)));
        self.0.set(unsafe { merge(node, self.0.get()) });
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
        if self.is_empty() {
            None
        } else {
            let [l, r] = unsafe { split(self.0.get(), self.len() - 1) };
            self.0.set(l);
            Some(unsafe { Box::from_raw(r).value })
        }
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
        if self.is_empty() {
            None
        } else {
            let [l, r] = unsafe { split(self.0.get(), 1) };
            self.0.set(r);
            Some(unsafe { Box::from_raw(l).value })
        }
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

impl<O: Ops> Index<usize> for SplayTree<O> {
    type Output = O::Value;
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap()
    }
}

/// [`SplayTree::entry`] の戻り値型
pub struct Entry<'a, O: Ops>(&'a mut SplayTree<O>);
impl<'a, O: Ops> Deref for Entry<'a, O> {
    type Target = O::Value;
    fn deref(&self) -> &Self::Target {
        unsafe { &(*(self.0).0.get()).value }
    }
}
impl<'a, O: Ops> DerefMut for Entry<'a, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut (*(self.0).0.get()).value }
    }
}
impl<'a, O: Ops> Drop for Entry<'a, O> {
    fn drop(&mut self) {
        unsafe { (*(self.0).0.get()).update() }
    }
}

impl<O: Ops> FromIterator<O::Value> for SplayTree<O> {
    fn from_iter<I: IntoIterator<Item = O::Value>>(iter: I) -> Self {
        let mut res = Self::new();
        iter.into_iter().for_each(|x| res.push_back(x));
        res
    }
}

impl<O: Ops> Drop for SplayTree<O> {
    fn drop(&mut self) {
        unsafe { deep_free(self.0.get()) }
    }
}

/// イテレータ型です。[`ExactSizeIterator`], [`DoubleEndedIterator`] を実装しており、
/// [`Iterator::nth`], [`DoubleEndedIterator::nth_back`] をオーバーライドしています。
pub struct Iter<'a, O: Ops> {
    splay: &'a SplayTree<O>,
    start: usize,
    end: usize,
}
impl<'a, O: Ops> Iterator for Iter<'a, O> {
    type Item = &'a O::Value;
    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            let res = self.splay.get(self.start).unwrap();
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
            let res = self.splay.get(self.start).unwrap();
            self.start += 1;
            Some(res)
        }
    }
}
impl<'a, O: Ops> ExactSizeIterator for Iter<'a, O> {
    fn len(&self) -> usize {
        self.end - self.start
    }
}

impl<'a, O: Ops> DoubleEndedIterator for Iter<'a, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            self.end -= 1;
            Some(self.splay.get(self.end).unwrap())
        }
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.len() <= n {
            self.end = self.start;
            None
        } else {
            self.end -= n + 1;
            Some(self.splay.get(self.end).unwrap())
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

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use {
        super::{Nop, Ops, SplayTree},
        itertools::assert_equal,
        rand::{distributions::Alphanumeric, prelude::StdRng, Rng, SeedableRng},
        std::{cmp::Ordering, fmt::Debug, mem::swap, ops::Range},
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

    const ABCDEFG: &str = "ABCDEFG";

    #[test]
    fn test_clone() {
        let splay = ABCDEFG.chars().collect::<SplayTree<O>>();
        let new = splay.clone();
        assert_eq!(splay, new);
        for i in 0..ABCDEFG.len() {
            splay.get(i);
            new.get(i);
            assert_ne!(splay.0.get(), new.0.get());
        }
    }

    #[test]
    fn test_default() {
        let splay = SplayTree::<O>::new();
        assert!(splay.is_empty());
    }

    fn from_slice<T: Copy + Sized + Debug>(a: &[T]) -> SplayTree<Nop<T>> {
        a.iter().copied().collect()
    }

    #[test]
    fn test_eq() {
        assert_eq!(from_slice(&[0, 1]), from_slice(&[0, 1]),);
        assert_ne!(from_slice(&[0, 1]), from_slice(&[0, 1, 2]),);
        assert_ne!(from_slice(&[0, 1, 2]), from_slice(&[0, 1]),);
        assert_ne!(from_slice(&[0, 1]), from_slice(&[0, 2]),);
        assert_ne!(from_slice(&[0, 1]), from_slice(&[2, 1]),);
    }

    #[test]
    fn test_partial_cmp() {
        assert_eq!(
            from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[0.0, 1.0])),
            Some(Ordering::Equal)
        );
        assert_eq!(
            from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[0.0, 1.0, 2.0])),
            Some(Ordering::Less)
        );
        assert_eq!(
            from_slice(&[0.0, 1.0, 2.0]).partial_cmp(&from_slice(&[0.0, 1.0])),
            Some(Ordering::Greater)
        );
        assert_eq!(
            from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[0.0, 2.0])),
            Some(Ordering::Less)
        );
        assert_eq!(
            from_slice(&[0.0, 2.0]).partial_cmp(&from_slice(&[0.0, 1.0])),
            Some(Ordering::Greater)
        );
        assert_eq!(
            from_slice(&[0.0, 2.0]).partial_cmp(&from_slice(&[0.0, std::f64::NAN])),
            None,
        );
        assert_eq!(
            from_slice(&[0.0, 1.0]).partial_cmp(&from_slice(&[2.0, std::f64::NAN])),
            Some(Ordering::Less)
        );
    }

    #[test]
    fn test_hash() {
        #![allow(clippy::bool_assert_comparison)]
        #[allow(clippy::mutable_key_type)]
        let mut set = HashSet::new();
        set.insert(from_slice(&[0, 1]));
        assert_eq!(set.len(), 1);
        set.insert(from_slice(&[0, 1]));
        assert_eq!(set.len(), 1);
        set.insert(from_slice(&[0, 2]));
        assert_eq!(set.len(), 2);
        assert_eq!(set.remove(&from_slice(&[0, 3])), false);
        assert_eq!(set.remove(&from_slice(&[0, 2])), true);
        assert_eq!(set.len(), 1);
    }

    #[test]
    fn test_len() {
        let mut splay = ABCDEFG.chars().collect::<SplayTree<O>>();
        assert_eq!(splay.len(), ABCDEFG.len());
        splay.delete(3);
        assert_eq!(splay.len(), ABCDEFG.len() - 1);
        splay.insert(4, 'Z');
        assert_eq!(splay.len(), ABCDEFG.len());
    }

    #[test]
    fn test_entry() {
        fn to_ascii_lowercase(c: &mut char) {
            *c = (*c).to_ascii_lowercase();
        }
        let mut splay = ABCDEFG.chars().collect::<SplayTree<O>>();
        *splay.entry(2).unwrap() = '2';
        to_ascii_lowercase(&mut *splay.entry(4).unwrap());
        assert!(splay.entry(1000).is_none());
        assert_eq!(splay.fold(..).unwrap(), "AB2DeFG");
    }

    #[test]
    fn test_fold_all() {
        let mut splay = ABCDEFG.chars().collect::<SplayTree<O>>();
        assert_eq!(splay.fold(..).unwrap().as_str(), "ABCDEFG");
        splay.delete(3);
        assert_eq!(splay.fold(..).unwrap().as_str(), "ABCEFG");
        splay.insert(4, 'Z');
        assert_eq!(splay.fold(..).unwrap().as_str(), "ABCEZFG");
    }

    #[test]
    fn test_iter() {
        let splay = ABCDEFG.chars().collect::<SplayTree<O>>();
        assert_equal(splay.iter().copied(), ABCDEFG.chars());
        assert_equal(splay.iter().rev().copied(), ABCDEFG.chars().rev());
    }

    #[test]
    fn test_cat_typical_queries() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            test_case(
                &mut rng,
                &Spec {
                    get: 4,
                    fold: 2,
                    push_back: 1,
                    push_front: 1,
                    insert: 1,
                    pop_back: 1,
                    pop_front: 1,
                    delete: 1,
                },
            );
        }
    }

    #[test]
    fn test_cat_typical_queries_many_delete() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            test_case(
                &mut rng,
                &Spec {
                    get: 4,
                    fold: 2,
                    push_back: 1,
                    push_front: 1,
                    insert: 1,
                    pop_back: 2,
                    pop_front: 2,
                    delete: 2,
                },
            );
        }
    }

    #[test]
    fn test_cat_typical_queries_many_push() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            test_case(
                &mut rng,
                &Spec {
                    get: 4,
                    fold: 2,
                    push_back: 2,
                    push_front: 2,
                    insert: 2,
                    pop_back: 1,
                    pop_front: 1,
                    delete: 1,
                },
            );
        }
    }

    struct Spec {
        get: usize,
        fold: usize,
        push_back: usize,
        push_front: usize,
        insert: usize,
        pop_back: usize,
        pop_front: usize,
        delete: usize,
    }

    fn test_case(rng: &mut StdRng, spec: &Spec) {
        let mut splay = SplayTree::<O>::new();
        let mut brute = Brute::new();
        let dice_max = spec.get
            + spec.fold
            + spec.push_back
            + spec.push_front
            + spec.insert
            + spec.pop_back
            + spec.pop_front;
        for _ in 0..200 {
            let mut dice = rng.gen_range(0..dice_max);

            // get
            if dice < spec.get {
                let i = rng.gen_range(0..=brute.len());
                let expected = brute.get(i);
                println!("get({}) = {:?}", i, &expected);
                let result = splay.get(i);
                assert_eq!(result, expected);
                continue;
            }
            dice -= spec.get;

            // fold
            if dice < spec.fold {
                let mut l = rng.gen_range(0..=brute.len() + 1);
                let mut r = rng.gen_range(0..=brute.len());
                if l > r {
                    swap(&mut l, &mut r);
                    r -= 1;
                }
                let expected = brute.fold(l..r);
                println!("fold({}..{}) = {:?}", l, r, &expected);
                let result = splay.fold(l..r);
                assert_eq!(expected, result);
                continue;
            }
            dice -= spec.fold;

            // push_back
            if dice < spec.push_back {
                let c = rng.sample(Alphanumeric) as char;
                brute.push_back(c);
                println!("push_back({}) -> {:?}", c, brute.fold_all_unwrap());
                splay.push_back(c);
                continue;
            }
            dice -= spec.push_back;

            // push_front
            if dice < spec.push_front {
                let c = rng.sample(Alphanumeric) as char;
                brute.push_front(c);
                splay.push_front(c);
                continue;
            }
            dice -= spec.push_front;

            // insert
            if dice < spec.insert {
                let i = rng.gen_range(0..=brute.len());
                let c = rng.sample(Alphanumeric) as char;
                brute.insert(i, c);
                splay.insert(i, c);
                continue;
            }
            dice -= spec.insert;

            // pop_back
            if dice < spec.pop_back {
                let expected = brute.pop_back();
                println!(
                    "pop_back() = {:?} -> {:?}",
                    expected,
                    brute.fold_all_unwrap()
                );
                let result = splay.pop_back();
                assert_eq!(expected, result);
                continue;
            }
            dice -= spec.pop_back;

            // pop_front
            if dice < spec.pop_front {
                let expected = brute.pop_front();
                println!(
                    "pop_front() = {:?} -> {:?}",
                    expected,
                    brute.fold_all_unwrap()
                );
                let result = splay.pop_front();
                assert_eq!(expected, result);
                continue;
            }
            dice -= spec.pop_front;

            // delete
            if dice < spec.delete {
                let i = rng.gen_range(0..brute.len());
                if i < brute.len() {
                    let expected = brute.delete(i);
                    println!(
                        "delete({}) = {:?} -> {:?}",
                        i,
                        expected,
                        brute.fold_all_unwrap()
                    );
                    let result = splay.delete(i);
                    assert_eq!(expected, result);
                }
                continue;
            }
            unreachable!();
        }
    }

    #[derive(Clone, Debug, Default, Hash, PartialEq)]
    struct Brute {
        vec: Vec<char>,
    }
    impl Brute {
        fn new() -> Self {
            Self::default()
        }
        fn len(&self) -> usize {
            self.vec.len()
        }
        fn get(&self, index: usize) -> Option<&char> {
            self.vec.get(index)
        }
        fn fold_all_unwrap(&self) -> String {
            self.vec.iter().collect::<String>()
        }
        fn fold(&self, range: Range<usize>) -> Option<String> {
            let s = self.vec[range].iter().collect::<String>();
            if s.is_empty() {
                None
            } else {
                Some(s)
            }
        }
        fn push_back(&mut self, c: char) {
            self.vec.push(c);
        }
        fn push_front(&mut self, c: char) {
            self.vec.insert(0, c);
        }
        fn insert(&mut self, i: usize, c: char) {
            self.vec.insert(i, c);
        }
        fn pop_back(&mut self) -> Option<char> {
            self.vec.pop()
        }
        fn pop_front(&mut self) -> Option<char> {
            if self.vec.is_empty() {
                None
            } else {
                Some(self.vec.remove(0))
            }
        }
        fn delete(&mut self, i: usize) -> char {
            self.vec.remove(i)
        }
    }
}
