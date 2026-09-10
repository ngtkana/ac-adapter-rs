//! 挿入・削除・区間反転・区間作用・区間畳み込みに対応した平衡二分探索木（スプレー木）。
//!
//! 要素を現在の並び順の添字（0-indexed）でアクセスする、配列を模した木構造。ノードに
//! モノイド $(Acc, \cdot)$ の集約値と、値・集約値へ作用する $Lazy$ を持たせ、遅延伝播で
//! 管理する。任意位置へアクセスするたびに対象ノードを回転で根まで引き上げる「スプレー」
//! 操作を行うことで、平衡条件を明示的に保たなくてもならし $O(\log n)$ でアクセス・分割・
//! 併合ができる。
//!
//! # 仕様
//!
//! [`LazyOps`] トレイトで集約 $Acc$ と作用 $Lazy$ を定義し、[`SplayTree<O>`](SplayTree) を使う。
//!
//! - [`proj`](LazyOps::proj), [`op`](LazyOps::op): 値 $\to$ 集約値の変換と、集約どうしの積（結合律が必要）
//! - [`act_value`](LazyOps::act_value), [`act_acc`](LazyOps::act_acc), [`compose`](LazyOps::compose): 値・集約値への作用と作用の合成
//! - 作用が不要なら [`Ops`] を実装して [`NoLazy`] でラップする
//! - 集約も作用も不要なら [`Nop`] をそのまま使う
//!
//! 主な操作：
//!
//! - [`insert`](SplayTree::insert), [`remove`](SplayTree::remove): 添字を指定した挿入・削除
//! - [`reverse`](SplayTree::reverse): 区間 $[l, r)$ の反転
//! - [`act`](SplayTree::act): 区間 $[l, r)$ への作用の適用
//! - [`fold`](SplayTree::fold): 区間 $[l, r)$ の集約値の取得
//! - [`get`](SplayTree::get), [`entry`](SplayTree::entry): 1点の参照・書き換え
//! - [`split_off`](SplayTree::split_off), [`append`](SplayTree::append): 木の分割・併合
//!
//! # 例
//!
//! ```
//! use splay_tree::NoLazy;
//! use splay_tree::Ops;
//! use splay_tree::SplayTree;
//!
//! enum Sum {}
//! impl Ops for Sum {
//!     type Value = i32;
//!     type Acc = i32;
//!     fn proj(&x: &i32) -> i32 {
//!         x
//!     }
//!     fn op(&x: &i32, &y: &i32) -> i32 {
//!         x + y
//!     }
//! }
//!
//! let mut splay = (0..5).collect::<SplayTree<NoLazy<Sum>>>();
//! splay.insert(2, 100);
//! assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![
//!     0, 1, 100, 2, 3, 4
//! ]);
//! assert_eq!(splay.fold(..), Some(0 + 1 + 100 + 2 + 3 + 4));
//! ```
//!
//! # 計算量
//!
//! - [`insert`](SplayTree::insert), [`remove`](SplayTree::remove), [`get`](SplayTree::get), [`entry`](SplayTree::entry): ならし $O(\log n)$
//! - [`reverse`](SplayTree::reverse), [`act`](SplayTree::act), [`fold`](SplayTree::fold): ならし $O(\log n)$
//! - [`split_off`](SplayTree::split_off), [`append`](SplayTree::append): ならし $O(\log n)$

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
/// insert, remove, reverse, act, fold
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

/// `Sized + Debug + Clone` をまとめたトレイト境界。[`LazyOps`] の関連型はすべてこれを要求する。
pub trait Value: Sized + Debug + Clone {}
impl<T: Sized + Debug + Clone> Value for T {}

/// 集約も作用も行わない場合に使う [`LazyOps`] 実装。要素の並びを管理するだけでよいときに使う。
///
/// # 例
///
/// ```
/// # use splay_tree::{Nop, SplayTree};
/// let splay = (0..3).collect::<SplayTree<Nop<i32>>>();
/// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![0, 1, 2]);
/// ```
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
/// 作用（更新）を持たない、集約だけを定義するトレイト。[`NoLazy`] でラップすると [`LazyOps`] になる。
pub trait Ops {
    /// 頂点重みの型。
    type Value: Value;
    /// 集約値の型。
    type Acc: Value;
    /// 値 $x$ の集約値 $\mathrm{proj}(x)$ を返す。
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 集約値どうしの積 $x \cdot y$ を返す。結合律を満たすこと。
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
}
/// [`Ops`] を実装する型を、作用なしの [`LazyOps`] に変換するラッパー型。
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

/// 集約と、集約・値への作用を定義するトレイト。[`SplayTree`] の要素型・集約型・作用型を決める。
///
/// 集約値の型を $Acc$、作用の型を $Lazy$ とする。$Lazy$ は可換とは限らないため、
/// [`compose`](Self::compose) は「先に既存の作用、後から新しい作用」の順で合成する。
pub trait LazyOps {
    /// 頂点重みの型。
    type Value: Value;
    /// 集約値の型 $Acc$。
    type Acc: Value;
    /// 作用の型 $Lazy$。
    type Lazy: Value;
    /// 値 $x$ の集約値 $\mathrm{proj}(x)$ を返す。
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 集約値どうしの積 $x \cdot y$ を返す。結合律を満たすこと。
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
    /// 値 `value` に作用 `lazy` を適用する。
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value);
    /// 集約値 `acc` に作用 `lazy` を適用する。
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc);
    /// `lower` を、先に `lower`、後から `upper` を適用したのと同じ効果になるよう更新する。
    fn compose(upper: &Self::Lazy, lower: &mut Self::Lazy);
    /// `lower` が `None` なら `upper` で埋め、`Some` なら [`compose`](Self::compose) で合成する。
    fn compose_to_option(upper: &Self::Lazy, lower: &mut Option<Self::Lazy>) {
        match lower {
            None => *lower = Some(upper.clone()),
            Some(lower) => Self::compose(upper, lower),
        }
    }
}

/// 挿入・削除・区間操作に対応したスプレー木本体。[モジュールレベルの説明を参照](self)。
pub struct SplayTree<O: LazyOps>(Cell<*mut Node<O>>);
impl<O: LazyOps> SplayTree<O> {
    /// 空のスプレー木を構築する。
    ///
    /// # 例
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    pub fn new() -> Self {
        Self(Cell::new(null_mut()))
    }

    /// 要素数が 0 なら `true` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// let splay = SplayTree::<Nop<()>>::new();
    /// assert!(splay.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.get().is_null()
    }

    /// 要素数を返す。
    ///
    /// # 計算量
    ///
    /// $O(1)$。
    ///
    /// # 例
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

    /// 添字 `at` の位置に `value` を挿入し、以降の要素を後ろへずらす。
    ///
    /// # Panics
    ///
    /// `at > self.len()` のときパニックする。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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
        let node = Box::into_raw(Box::new(Node::new(value)));
        self.0.set(merge(merge(left, node), right));
    }

    /// 添字 `at` の要素を削除して返し、以降の要素を前へずらす。
    ///
    /// # Panics
    ///
    /// `at >= self.len()` のときパニックする。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// # use splay_tree::{SplayTree, Nop};
    /// # use std::iter::repeat;
    /// let mut splay = vec![10, 11, 12]
    ///     .into_iter()
    ///     .collect::<SplayTree<Nop<i32>>>();
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 11, 12]);
    ///
    /// splay.remove(1);
    /// assert_eq!(splay.iter().copied().collect::<Vec<_>>(), vec![10, 12]);
    /// ```
    pub fn remove(&mut self, at: usize) -> O::Value {
        if self.len() <= at {
            splay_tree_index_out_of_range_fail(at, self.len());
        }
        let [lc, r] = split_at(self.0.get(), at + 1);
        let [l, c] = split_at(lc, at);
        let ans = unsafe { Box::from_raw(c) }.value;
        self.0.set(merge(l, r));
        ans
    }

    /// 区間 `range`（添字）の要素を反転する。遅延伝播で行うため、木全体を書き換えない。
    ///
    /// # Panics
    ///
    /// `range` が範囲外のときパニックする。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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

    /// 区間 `range` の要素を [`LazyOps::op`] で畳み込んだ集約値を返す。区間が空なら `None`。
    ///
    /// # Panics
    ///
    /// `range` が範囲外のときパニックする。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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

    /// 区間 `range` の要素すべてに作用 `lazy` を [`LazyOps::act_value`] で適用する。
    ///
    /// # Panics
    ///
    /// `range` が範囲外のときパニックする。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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

    /// 添字 `i` の要素への参照を返す。範囲外なら `None`。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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
        let root = access_index(self.0.get(), i);
        self.0.set(root);
        Some(unsafe { &(*root).value })
    }

    /// 添字 `i` の要素への可変ハンドル（[`Entry`]）を返す。範囲外なら `None`。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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
        let root = access_index(self.0.get(), i);
        self.0.set(root);
        Some(Entry(self))
    }

    /// 添字 `at` 以降を切り離し、新しい木として返す。`self` には `[0, at)` が残る。
    ///
    /// # Panics
    ///
    /// `at > self.len()` のときパニックする。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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

    /// `right` の要素をすべて `self` の末尾に連結し、`right` を空にする。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log n)$。
    ///
    /// # 例
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
    /// assert!(other.is_empty());
    /// ```
    pub fn append(&mut self, right: &Self) {
        let root = merge(self.0.get(), right.0.get());
        self.0.set(root);
        right.0.set(null_mut());
    }

    /// 要素を前から順に返す両端イテレータを返す。
    ///
    /// # 例
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

    /// 区間 `range` の要素を前から順に返す両端イテレータを返す。
    ///
    /// # 例
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

    /// 内部構造を標準出力にダンプする（デバッグ用）。
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
        let mut root: *mut Node<O> = match iter.next() {
            None => return Self::new(),
            Some(value) => Box::into_raw(Box::new(Node::new(value))),
        };
        for value in iter {
            let node: *mut Node<O> = Box::into_raw(Box::new(Node::new(value)));
            unsafe {
                (*root).parent = node;
                (*node).left = root;
                (*node).update();
            }
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

/// [`SplayTree::iter`], [`SplayTree::range`] が返すイテレータ。
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
impl<O: LazyOps> DoubleEndedIterator for Iter<'_, O> {
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

/// [`SplayTree::entry`] が返す、要素への可変ハンドル。`Deref`/`DerefMut` で値にアクセスする。
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
