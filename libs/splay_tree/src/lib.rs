//! スプレー木です。

mod node;

/// # Citation
///
/// [Library-Checer Dynamic Sequence Range Affine Range Sum]
/// (https://judge.yosupo.jp/problem/dynamic_sequence_range_affine_range_sum)
///
/// # 制約
///
/// N, Q ≤ 500,000
///
///
/// # APIs
///
/// insert, delete, reverse, act, fold
///
/// # 提出 (3051 ms)
///
/// https://judge.yosupo.jp/submission/55691
#[cfg(test)]
mod test_dynamic_sequence_range_affine_range;

/// # Citation
///
/// [SoundHound Programming Contest 2018 Masters Tournament 本戦 (Open)]
/// (https://atcoder.jp/contests/soundhound2018-summer-final-open/tasks/soundhound2018_summer_final_e)
///
/// # 制約
///
/// N, Q ≤ 200,000
///
///
/// # APIs
///
/// merge, split_off, fold
///
/// # 提出 (3157 ms)
///
/// https://atcoder.jp/contests/soundhound2018-summer-final-open/submissions/24922921
#[cfg(test)]
mod test_hash_swapping;

#[cfg(test)]
mod test_trivial;

use self::node::access_index;
use self::node::deep_free;
use self::node::merge;
use self::node::split_at;
use self::node::Node;
use std::cell::Cell;
use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::Bound;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Index;
use std::ops::Range;
use std::ops::RangeBounds;
use std::ptr::null_mut;

/// [`Sized`], [`Debug`], [`Clone`] をまとめたトレイト
pub trait Value: Sized + Debug + Clone {}
impl<T: Sized + Debug + Clone> Value for T {}

/// 集約も作用もなしの場合に使うトレイト
pub struct Nop<T: Value>(PhantomData<fn(T) -> T>);
impl<T: Value> LazyOps for Nop<T> {
    type Acc = ();
    type Lazy = ();
    type Value = T;

    fn proj(_value: &Self::Value) -> Self::Acc {}

    fn op(&(): &Self::Acc, &(): &Self::Acc) -> Self::Acc {}

    fn act_value(&(): &Self::Lazy, _value: &mut Self::Value) {}

    fn act_acc(&(): &Self::Lazy, &mut (): &mut Self::Acc) {}

    fn compose(&(): &Self::Lazy, &mut (): &mut Self::Lazy) {}
}
/// 作用なしの場合に使うトレイト
pub trait Ops {
    /// 頂点重み型
    type Value: Value;
    /// 集約値型
    type Acc: Value;
    /// 集約化
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 集約演算
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
}
/// [`Ops`] を実装する型をラップして [`LazyOps`] を実装する型
pub struct NoLazy<O>(PhantomData<fn(O) -> O>);
impl<O: Ops> LazyOps for NoLazy<O> {
    type Acc = O::Acc;
    type Lazy = ();
    type Value = O::Value;

    fn proj(value: &Self::Value) -> Self::Acc {
        O::proj(value)
    }

    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc {
        O::op(lhs, rhs)
    }

    fn act_value(&(): &Self::Lazy, _value: &mut Self::Value) {}

    fn act_acc(&(): &Self::Lazy, _acc: &mut Self::Acc) {}

    fn compose(&(): &Self::Lazy, &mut (): &mut Self::Lazy) {}
}

/// 集約と作用のトレイト
pub trait LazyOps {
    /// 頂点重み型
    type Value: Value;
    /// 集約値型
    type Acc: Value;
    /// 作用値型
    type Lazy: Value;
    /// 集約化
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 集約演算
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
    /// 頂点重みへの作用
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value);
    /// 集約値への作用
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc);
    /// 作用の合成
    fn compose(upper: &Self::Lazy, lower: &mut Self::Lazy);
    /// Option へ作用の合成
    fn compose_to_option(upper: &Self::Lazy, lower: &mut Option<Self::Lazy>) {
        match lower {
            None => *lower = Some(upper.clone()),
            Some(lower) => Self::compose(upper, lower),
        }
    }
}

/// スプレー木
pub struct SplayTree<O: LazyOps>(Cell<*mut Node<O>>);
impl<O: LazyOps> SplayTree<O> {
    /// 空のスプレー木を構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    pub fn new() -> Self {
        Self(Cell::new(null_mut()))
    }

    /// 空ならば `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.get().is_null()
    }

    /// 要素数を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    ///
    /// // 0 要素
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert_eq!(splay.len(), 0);
    ///
    /// // 3 要素
    /// let splay = repeat(()).take(3).collect::<SplayTree<Nop<()>>>();
    /// assert_eq!(splay.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        unsafe { self.0.get().as_ref() }.map_or(0, |root| root.len)
    }

    /// 指定した場所に挿入します。
    ///
    /// # Panics
    ///
    /// - 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let mut splay = vec![10, 11, 12]
    ///     .into_iter()
    ///     .collect::<SplayTree<Nop<i32>>>();
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 11, 12]);
    ///
    /// splay.insert(1, 20);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![
    ///     10, 20, 11, 12
    /// ]);
    /// ```
    pub fn insert(&mut self, at: usize, value: O::Value) {
        if self.len() < at {
            splay_tree_index_out_of_range_fail(at, self.len());
        }
        let [left, right] = split_at(self.0.get(), at);
        let node = Box::leak(Box::new(Node::new(value)));
        self.0.set(merge(merge(left, node), right));
    }

    /// 指定した場所の要素を削除します。
    ///
    /// # Panics
    ///
    /// - 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let mut splay = vec![10, 11, 12]
    ///     .into_iter()
    ///     .collect::<SplayTree<Nop<i32>>>();
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 11, 12]);
    ///
    /// splay.delete(1);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 12]);
    /// ```
    pub fn delete(&mut self, at: usize) -> O::Value {
        if self.len() <= at {
            splay_tree_index_out_of_range_fail(at, self.len());
        }
        let [lc, r] = split_at(self.0.get(), at + 1);
        let [l, c] = split_at(lc, at);
        let ans = unsafe { Box::from_raw(c) }.value;
        self.0.set(merge(l, r));
        ans
    }

    /// 指定した範囲の要素を逆順にします。
    ///
    /// # Panics
    ///
    /// - 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let mut splay = (10..15).collect::<SplayTree<Nop<i32>>>();
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![
    ///     10, 11, 12, 13, 14
    /// ]);
    ///
    /// splay.reverse(1..4);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![
    ///     10, 13, 12, 11, 14
    /// ]);
    /// ```
    pub fn reverse(&mut self, range: impl RangeBounds<usize>) {
        let Range { start, end } = into_range(self.len(), range);
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        if let Some(c) = unsafe { c.as_mut() } {
            c.rev ^= true;
            c.push();
        }
        self.0.set(merge(merge(l, c), r));
    }

    /// 指定した範囲の要素を畳み込みます。
    ///
    /// # Panics
    ///
    /// - 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, NoLazy, Ops};
    /// # use std::iter::repeat;
    /// enum Sum {}
    /// impl Ops for Sum {
    ///     type Acc = i32;
    ///     type Value = i32;
    ///
    ///     fn proj(&x: &i32) -> i32 {
    ///         x
    ///     }
    ///
    ///     fn op(&x: &i32, &y: &i32) -> i32 {
    ///         x + y
    ///     }
    /// }
    /// let splay = (10..15).collect::<SplayTree<NoLazy<Sum>>>();
    /// assert_eq!(splay.fold(2..), Some(12 + 13 + 14));
    /// assert_eq!(splay.fold(2..2), None);
    /// ```
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Acc> {
        let Range { start, end } = into_range(self.len(), range);
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        let ans = unsafe { c.as_mut() }.map(|c| {
            c.update();
            c.acc.clone()
        });
        self.0.set(merge(merge(l, c), r));
        ans
    }

    /// 指定した範囲の要素すべてに作用します。
    ///
    /// # Panics
    ///
    /// - 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, LazyOps};
    /// # use std::iter::repeat;
    /// enum Update {}
    /// impl LazyOps for Update {
    ///     type Acc = ();
    ///     type Lazy = i32;
    ///     type Value = i32;
    ///
    ///     fn proj(&x: &i32) {}
    ///
    ///     fn op(&(): &(), &(): &()) {}
    ///
    ///     fn act_value(&lazy: &Self::Lazy, value: &mut Self::Value) {
    ///         *value = lazy;
    ///     }
    ///
    ///     fn act_acc(&_lazy: &Self::Lazy, &mut (): &mut Self::Acc) {}
    ///
    ///     fn compose(&x: &Self::Lazy, y: &mut Self::Lazy) {
    ///         *y = x;
    ///     }
    /// }
    ///
    /// let mut splay = (10..15).collect::<SplayTree<Update>>();
    /// splay.act(2..4, 20);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![
    ///     10, 11, 20, 20, 14
    /// ]);
    /// ```
    pub fn act(&mut self, range: impl RangeBounds<usize>, lazy: O::Lazy) {
        let Range { start, end } = into_range(self.len(), range);
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        if let Some(c) = unsafe { c.as_mut() } {
            c.lazy = Some(lazy);
            c.push();
        }
        self.0.set(merge(merge(l, c), r));
    }

    /// 指定した場所の要素への参照を返します。範囲外のときには `None` を返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let splay = vec![10, 11, 12]
    ///     .into_iter()
    ///     .collect::<SplayTree<Nop<i32>>>();
    /// assert_eq!(splay.get(0), Some(&10));
    /// assert_eq!(splay.get(5), None);
    /// ```
    pub fn get(&self, i: usize) -> Option<&O::Value> {
        if self.len() <= i {
            return None;
        }
        let mut root = unsafe { self.0.get().as_mut() }.unwrap();
        root = access_index(root, i);
        self.0.set(root);
        let ans = &root.value;
        Some(ans)
    }

    /// 指定した場所の要素への可変ハンドラを返します。範囲外のときには `None` を返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let mut splay = vec![10, 11, 12]
    ///     .into_iter()
    ///     .collect::<SplayTree<Nop<i32>>>();
    /// *splay.entry(0).unwrap() += 10;
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![20, 11, 12]);
    /// ```
    pub fn entry(&mut self, i: usize) -> Option<Entry<'_, O>> {
        if self.len() <= i {
            return None;
        }
        let mut root = unsafe { self.0.get().as_mut() }.unwrap();
        root = access_index(root, i);
        self.0.set(root);
        Some(Entry(self))
    }

    /// 指定した場所以降を切り離して返します。
    ///
    ///
    /// # Panics
    ///
    /// - 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let mut splay = (10..15).into_iter().collect::<SplayTree<Nop<i32>>>();
    /// let other = splay.split_off(3);
    ///
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 11, 12]);
    /// assert_eq!(other.iter().copied().collect::<Vec<_>>(), vec![13, 14]);
    /// ```
    pub fn split_off(&mut self, at: usize) -> Self {
        if self.len() < at {
            splay_tree_index_out_of_range_fail(at, self.len());
        }
        let [left, right] = split_at(self.0.get(), at);
        self.0.set(left);
        Self(Cell::new(right))
    }

    /// 受け取ったスプレー木の値をすべて後ろにつなげます。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let mut splay = (10..13).into_iter().collect::<SplayTree<Nop<i32>>>();
    /// let mut other = (20..23).into_iter().collect::<SplayTree<Nop<i32>>>();
    /// splay.append(&mut other);
    ///
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![
    ///     10, 11, 12, 20, 21, 22
    /// ]);
    /// ```
    pub fn append(&mut self, right: &Self) {
        let root = merge(self.0.get(), right.0.get());
        self.0.set(root);
        right.0.set(null_mut());
    }

    /// 要素を順番に返すイテレータを返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let splay = (10..13).into_iter().collect::<SplayTree<Nop<i32>>>();
    /// let mut iter = splay.iter();
    ///
    /// assert_eq!(iter.next(), Some(&10));
    /// assert_eq!(iter.next_back(), Some(&12));
    /// assert_eq!(iter.next(), Some(&11));
    /// assert_eq!(iter.next_back(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, O> {
        Iter {
            splay: self,
            start: 0,
            end: self.len(),
        }
    }

    /// 指定した範囲の要素を順番に返すイテレータを返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let splay = (0..20).into_iter().collect::<SplayTree<Nop<i32>>>();
    /// let mut iter = splay.range(10..13);
    ///
    /// assert_eq!(iter.next(), Some(&10));
    /// assert_eq!(iter.next_back(), Some(&12));
    /// assert_eq!(iter.next(), Some(&11));
    /// assert_eq!(iter.next_back(), None);
    /// ```
    pub fn range(&self, range: impl RangeBounds<usize>) -> Iter<'_, O> {
        let Range { start, end } = into_range(self.len(), range);
        Iter {
            splay: self,
            start,
            end,
        }
    }

    /// 内部情報をダンプします。
    pub fn dump(&self) {
        println!("    === start dump ===    ");
        match unsafe { self.0.get().as_ref() } {
            None => println!("empty"),
            Some(root) => root.dump(),
        }
        println!("    ===  end  dump ===    ");
    }
}

impl<O: LazyOps> FromIterator<O::Value> for SplayTree<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        let mut root = match iter.next() {
            None => return Self::new(),
            Some(value) => Box::leak(Box::new(Node::new(value))),
        };
        for value in iter {
            let node = Box::leak(Box::new(Node::new(value)));
            root.parent = node;
            node.left = root;
            node.update();
            root = node;
        }
        Self(Cell::new(root))
    }
}

impl<'a, O: LazyOps> IntoIterator for &'a SplayTree<O> {
    type IntoIter = Iter<'a, O>;
    type Item = &'a O::Value;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
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
        Self(Cell::new(null_mut()))
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
        self.iter().for_each(|x| x.hash(state));
    }
}

impl<O: LazyOps> Index<usize> for SplayTree<O> {
    type Output = O::Value;

    fn index(&self, index: usize) -> &Self::Output {
        if self.len() <= index {
            splay_tree_index_out_of_range_fail(index, self.len());
        }
        self.get(index).unwrap()
    }
}

/// [`SplayTree::iter`], [`SplayTree::range`] の戻り値型です。
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
            let ans = self.splay.get(self.start).unwrap();
            self.start += 1;
            Some(ans)
        }
    }
}
impl<'a, O: LazyOps> DoubleEndedIterator for Iter<'a, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            self.end -= 1;
            let ans = self.splay.get(self.end).unwrap();
            Some(ans)
        }
    }
}

/// [`SplayTree::entry`] の戻り値型です。
pub struct Entry<'a, O: LazyOps>(&'a mut SplayTree<O>);
impl<O: LazyOps> Deref for Entry<'_, O> {
    type Target = O::Value;

    fn deref(&self) -> &Self::Target {
        &unsafe { &*self.0 .0.get() }.value
    }
}
impl<O: LazyOps> DerefMut for Entry<'_, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut unsafe { &mut *self.0 .0.get() }.value
    }
}

impl<O: LazyOps> Drop for SplayTree<O> {
    fn drop(&mut self) {
        deep_free(self.0.get());
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
fn splay_tree_index_out_of_range_fail(index: usize, len: usize) -> ! {
    panic!("range index {index} out of range for splay tree of length {len}");
}
fn splay_tree_start_index_len_fail(index: usize, len: usize) -> ! {
    panic!("range start index {index} out of range for splay tree of length {len}");
}
fn splay_tree_end_index_len_fail(index: usize, len: usize) -> ! {
    panic!("range end index {index} out of range for splay tree of length {len}");
}
fn splay_tree_index_order_fail(index: usize, end: usize) -> ! {
    panic!("splay tree index starts at {index} but ends at {end}");
}
