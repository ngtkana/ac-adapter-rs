//! Splay 木で、列を管理するデータ構造です。
//!
//! # できること
//!
//! [`SplayTree`] は、列 `a = [ a[0], a[1], ..., a[n-1] ]`
//! を管理します。要素の間には（可換とは限らない）積が定義されているとします。
//! また、列の結合を和で表記します。このとき、次のことを実現するデータ構造です。
//!
//! | おなまえ                                  | 計算量        | やること                          |
//! | -                                         | -             | -                                 |
//! | [`new`](SplayTree::new)                   | O(1)          | `a = []`                          |
//! | [`is_empty`](SplayTree::is_empty)         | O(1)          | `a = []?`                         |
//! | [`get(i)`](SplayTree::get)                | O(lg n) am.   | `a[i]?`                           |
//! | [`entry(i)`](SplayTree::entry)            | O(lg n) am.   | `a[i]` のハンドラ                 |
//! | [`fold(l..r)`](SplayTree::fold)           | O(lg n) am.   | `a[l] * a[l+1] * ... * a[r-1]`    |
//! | [`fold_all()`](SplayTree::fold_all)       | O(1)          | `a[0] * a[1] * ... * a[n-1]`      |
//! | [`insert(i, x)`](SplayTree::insert)       | O(lg n) am.   | `a = a[..i] + [x] + a[i+1..]`     |
//! | [`delete(i)`](SplayTree::delete)          | O(lg n) am.   | `a = a[..i-1] + a[i+1..]`         |
//! | [`append(b)`](SplayTree::append)          | O(lg n) am.   | `a = a + b`                       |
//! | [`prepend(b)`](SplayTree::prepend)        | O(lg n) am.   | `a = b + a`                       |
//! | [`split_off(i)`](SplayTree::split_off)    | O(lg n) am.   | `a = a[..i], return a[i..]`       |
//! | [`split_on(i)`](SplayTree::split_on)      | O(lg n) am.   | `a = a[i..], return a[..i]`       |
//!
//! あと [`push_back`](SplayTree::push_back) とかもあります。
//!
//!
//! # Examples
//!
//! ## 演算の必要がない場合
//!
//! [`Nop`] を使いましょう。
//!
//! ```
//! # use splay_tree::{SplayTree, Nop};
//! // FromIterator
//! let mut splay = (0..4).collect::<SplayTree<Nop<i32>>>();
//!
//! // get
//! assert_eq!(splay.get(2), &2);
//!
//! // insert （push_{front,back} もよろしくです。）
//! splay.insert(3, -1);
//!
//! // delete（pop_{front,back} もよろしくです。）
//! assert_eq!(splay.delete(0), 0);
//!
//! // iter
//! assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![1, 2, -1, 3]);
//! assert_eq!(splay.iter().rev().copied().collect::<Vec<_>>(), vec![3, -1, 2, 1]);
//! assert_eq!(splay.iter().step_by(2).copied().collect::<Vec<_>>(), vec![1, -1]);
//! assert_eq!(splay.iter().rev().step_by(2).copied().collect::<Vec<_>>(), vec![3, 2]);
//!
//! // append（prepend もよろしくです。）
//! splay.append(&mut (4..8).collect::<SplayTree<_>>());
//!
//! // split_off（split_on もよろしくです。）
//! let split_off = splay.split_off(6);
//! assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![1, 2, -1, 3, 4, 5]);
//! assert_eq!(split_off.iter().copied().collect::<Vec<_>>(), vec![6, 7]);
//! ```
//!
//! ## 演算 `+` の例
//!
//! 戻り値が `Option<O::Value>` です。
//!
//! ```
//! # use splay_tree::{SplayTree, Ops};
//! enum O {}
//! impl Ops for O {
//!     type Value = i32;
//!     type Acc = i32;
//!     fn proj(&value: &Self::Value) -> Self::Acc {
//!         value
//!     }
//!     fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc {
//!         lhs + rhs
//!     }
//! }
//!
//! // FromIterator
//! let mut splay = vec![1, 2, 4, 8].into_iter().collect::<SplayTree<O>>();
//!
//! // fold, fold_all
//! assert_eq!(splay.fold(1..3), Some(2 + 4));
//! assert_eq!(splay.fold_all(), Some(15));
//!
//! // push_front, pop_back
//! splay.push_front(-10);
//! assert_eq!(splay.pop_back(), Some(8));
//! assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![-10, 1, 2, 4]);
//!
//! // fold
//! assert_eq!(splay.fold(..3), Some(-10 + 1 + 2));
//! ```

mod node;

use {
    node::{deep_free, delete, get, insert, merge, split, Node},
    std::{
        cell::Cell,
        fmt::Debug,
        iter::FromIterator,
        marker::PhantomData,
        ops::{Bound, Deref, DerefMut, Range, RangeBounds},
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
pub struct SplayTree<O: Ops>(Cell<*mut Node<O>>);
impl<O: Ops> SplayTree<O> {
    pub fn new() -> Self {
        Self(Cell::new(null_mut()))
    }
    pub fn is_empty(&self) -> bool {
        self.0.get().is_null()
    }
    pub fn len(&self) -> usize {
        unsafe { self.0.get().as_ref().map_or(0, |r| r.len) }
    }
    pub fn get(&self, index: usize) -> &O::Value {
        assert!(index < self.len());
        self.0.set(unsafe { get(self.0.get(), index) });
        unsafe { &(*self.0.get()).value }
    }
    pub fn entry(&mut self, index: usize) -> Entry<'_, O> {
        assert!(index < self.len());
        *self.0.get_mut() = unsafe { get(self.0.get(), index) };
        Entry(self)
    }
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Acc> {
        let Range { start, end } = into_range(self.len(), range);
        if self.len() < start {
            splay_tree_start_index_len_fail(start, self.len());
        }
        if self.len() < end {
            splay_tree_end_index_len_fail(end, self.len());
        }
        if start > end {
            splay_tree_index_order_fail(start, end)
        }
        let [lc, r] = unsafe { split(self.0.get(), end) };
        let [l, c] = unsafe { split(lc, start) };
        let ans = unsafe { c.as_ref().map(|c| &c.fold) }.cloned();
        self.0.set(unsafe { merge(merge(l, c), r) });
        ans
    }
    pub fn fold_all(&self) -> Option<O::Acc> {
        unsafe { self.0.get().as_ref().map(|c| &c.fold) }.cloned()
    }
    pub fn insert(&mut self, index: usize, x: O::Value) {
        assert!(index <= self.len());
        let node = Box::into_raw(Box::new(Node::new(x)));
        self.0.set(if self.0.get().is_null() {
            node
        } else {
            unsafe { insert(self.0.get(), index, node) }
        });
    }
    pub fn delete(&mut self, index: usize) -> O::Value {
        assert!(index < self.len());
        let [root, node] = unsafe { delete(self.0.get(), index) };
        self.0.set(root);
        unsafe { Box::from_raw(node).value }
    }
    pub fn prepend(&mut self, head: &mut Self) {
        self.0.set(unsafe { merge(head.0.get(), self.0.get()) });
        head.0.set(null_mut());
    }
    pub fn append(&mut self, tail: &mut Self) {
        self.0.set(unsafe { merge(self.0.get(), tail.0.get()) });
        tail.0.set(null_mut());
    }
    pub fn split_off(&mut self, at: usize) -> Self {
        let [l, r] = unsafe { split(self.0.get(), at) };
        self.0.set(l);
        Self(Cell::new(r))
    }
    pub fn split_on(&mut self, at: usize) -> Self {
        let [l, r] = unsafe { split(self.0.get(), at) };
        self.0.set(r);
        Self(Cell::new(l))
    }
    pub fn push_back(&mut self, x: O::Value) {
        self.append(&mut Self::__singleton(x))
    }
    pub fn push_front(&mut self, x: O::Value) {
        self.prepend(&mut Self::__singleton(x))
    }
    pub fn pop_back(&mut self) -> Option<O::Value> {
        if self.is_empty() {
            None
        } else {
            let [l, r] = unsafe { split(self.0.get(), self.len() - 1) };
            self.0.set(l);
            Some(unsafe { Box::from_raw(r).value })
        }
    }
    pub fn pop_front(&mut self) -> Option<O::Value> {
        if self.is_empty() {
            None
        } else {
            let [l, r] = unsafe { split(self.0.get(), 1) };
            self.0.set(r);
            Some(unsafe { Box::from_raw(l).value })
        }
    }
    pub fn iter(&self) -> Iter<'_, O> {
        Iter {
            splay: self,
            start: 0,
            end: self.len(),
        }
    }
    fn __singleton(value: O::Value) -> Self {
        Self(Cell::new(Box::into_raw(Box::new(Node::new(value)))))
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
/// `nth`, `nth_back` をオーバーライドしています。
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
            let res = self.splay.get(self.start);
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
            let res = self.splay.get(self.start);
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
            Some(self.splay.get(self.end))
        }
    }
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if self.len() <= n {
            self.end = self.start;
            None
        } else {
            self.end -= n + 1;
            Some(self.splay.get(self.end))
        }
    }
}

fn into_range(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    (match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start + 1,
        Bound::Unbounded => 0,
    })..(match range.end_bound() {
        Bound::Included(&end) => end + 1,
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    })
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
