//! ノードに集約値の更新ロジックを持たせる侵入型（intrusive）のスプレイ木。
//!
//! ノードへのアクセス・挿入・削除のたびに対象ノードを回転でルートまで浮上させる操作
//! （**スプレイ**）によって木を平衡に保つ、自己調整型（self-adjusting）の二分探索木である。
//! 同じノードやその近傍への繰り返しアクセスに対してならし $O(\log n)$ を達成する。
//! 各ノードの集約値（合計・最小値など）は木の構造が変わるたびに [`Op::update`] が再計算するため、
//! 利用側は値そのものではなく更新規則だけを与えればよい。
//!
//! # 解説
//!
//! - 分割・併合は [`Op::update`] の呼び出しを内包する 4 つのプリミティブ（split2 / split3 / merge2 / merge3）
//!   で構成する。対象ノードを splay でルートまで浮かせてから子を切り離す、あるいは 2 つの根を直接つなぐだけでよい。
//! - 二分探索の方向は呼び出し側が渡すクロージャで指定する。[`Navi2`] は必ず葉まで進んで挿入・分割位置を決め、
//!   [`Navi3`] は `Found` で早期終了できるため削除・検索に使う。
//! - [`RangeEntry`] は木を 左 / 中央 / 右 の 3 部分木に分割し、中央だけを一時的な [`Tree`] として貸し出す。
//!   drop 時に 3 部分を結合し直すことで、範囲操作の間も木全体の構造的な不変性を保つ。
//!
//! # 仕様
//!
//! 型は `Tree<O: Op>`（`O::Store` はノードに格納する値の型）。主な操作：
//!
//! - 挿入: [`insert`](Tree::insert), [`insert_by_index`](Tree::insert_by_index),
//!   [`insert_lower_bound_by_key`](Tree::insert_lower_bound_by_key),
//!   [`insert_upper_bound_by_key`](Tree::insert_upper_bound_by_key),
//!   [`push_front`](Tree::push_front), [`push_back`](Tree::push_back)
//! - 削除: [`remove`](Tree::remove), [`remove_by_index`](Tree::remove_by_index),
//!   [`remove_by_key`](Tree::remove_by_key), [`pop_front`](Tree::pop_front), [`pop_back`](Tree::pop_back)
//! - 検索: [`get`](Tree::get), [`get_by_index`](Tree::get_by_index), [`get_by_key`](Tree::get_by_key),
//!   [`front`](Tree::front), [`back`](Tree::back)
//! - 分割・結合: [`split_off`](Tree::split_off), [`split_off_by_index`](Tree::split_off_by_index),
//!   [`split_off_lower_bound_by_key`](Tree::split_off_lower_bound_by_key),
//!   [`split_off_upper_bound_by_key`](Tree::split_off_upper_bound_by_key), [`append`](Tree::append)
//! - 範囲アクセス: [`range_by_key`](Tree::range_by_key), [`range_by_index`](Tree::range_by_index)
//! - 集約取得: [`fold`](Tree::fold)（ルートの集約値を $O(1)$ で返す）
//!
//! # 例
//!
//! ```
//! use intrusive_splay_tree::Op;
//! use intrusive_splay_tree::Tree;
//!
//! struct Store {
//!     value: i32,
//!     sum: i32,
//! }
//!
//! enum O {}
//! impl Op for O {
//!     type Store = Store;
//!
//!     fn update(node: &mut Store, left: Option<&Store>, right: Option<&Store>) {
//!         node.sum = node.value + left.map_or(0, |l| l.sum) + right.map_or(0, |r| r.sum);
//!     }
//! }
//!
//! let mut tree = Tree::<O>::new();
//! tree.insert_lower_bound_by_key(Store { value: 10, sum: 10 }, |v| v.value);
//! tree.insert_lower_bound_by_key(Store { value: 5, sum: 5 }, |v| v.value);
//!
//! assert_eq!(tree.fold().unwrap().sum, 15);
//! ```
//!
//! # 計算量
//!
//! 挿入・削除・検索・分割・結合・範囲アクセス — いずれもならし $O(\log n)$（$n$ はノード数）

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::ops::Bound;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::RangeBounds;
use std::ptr::NonNull;

mod node;
use crate::node::visit;
use node::Node;
use node::Onn;
use node::Split3Result;
use node::free_subtree;
use node::merge2;
use node::merge3;
use node::split2;
use node::split3;

/// 必ず葉まで進む二分探索の方向（早期終了なし）。
///
/// [`insert`](Tree::insert) や [`split_off`](Tree::split_off) など、常に特定の位置への
/// 挿入・分割で終わる操作に使う。
///
/// # 例
///
/// ```
/// use intrusive_splay_tree::Navi2;
/// use intrusive_splay_tree::Op;
/// use intrusive_splay_tree::Tree;
///
/// enum O {}
/// impl Op for O {
///     type Store = i32;
///
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<O>::new();
/// tree.insert(5, |center, _, _| {
///     if 5 < *center { Navi2::GoDownLeft } else { Navi2::GoDownRight }
/// });
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Navi2 {
    GoDownLeft,
    GoDownRight,
}
impl Navi2 {
    fn by_index<T>(
        index: &mut usize,
        size: &mut impl FnMut(&T) -> usize,
        left: Option<&T>,
    ) -> Self {
        let lsize = left.map_or(0, size);
        match (*index).cmp(&lsize) {
            Ordering::Less | Ordering::Equal => Self::GoDownLeft,
            Ordering::Greater => {
                *index -= lsize + 1;
                Self::GoDownRight
            }
        }
    }

    fn lower_bound_by_key<T, K: Borrow<Q>, Q: ?Sized + Ord>(
        probe: &Q,
        center: &T,
        f: &mut impl FnMut(&T) -> K,
    ) -> Self {
        match probe.cmp(f(center).borrow()) {
            Ordering::Less | Ordering::Equal => Self::GoDownLeft,
            Ordering::Greater => Self::GoDownRight,
        }
    }

    fn upper_bound_by_key<T, K: Borrow<Q>, Q: ?Sized + Ord>(
        probe: &Q,
        center: &T,
        f: &mut impl FnMut(&T) -> K,
    ) -> Self {
        match probe.cmp(f(center).borrow()) {
            Ordering::Less => Self::GoDownLeft,
            Ordering::Equal | Ordering::Greater => Self::GoDownRight,
        }
    }
}

/// 目的のノードが見つかったら早期終了できる二分探索の方向。
///
/// [`remove`](Tree::remove) や [`get`](Tree::get) など、探索対象が存在するとは限らない操作に使う。
/// 現在のノードが目的地なら [`Found`](Navi3::Found) を返す。
///
/// # 例
///
/// ```
/// use intrusive_splay_tree::Navi3;
/// use intrusive_splay_tree::Op;
/// use intrusive_splay_tree::Tree;
///
/// enum O {}
/// impl Op for O {
///     type Store = i32;
///
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<O>::new();
/// tree.insert_lower_bound_by_key(5, |v| *v);
/// tree.insert_lower_bound_by_key(3, |v| *v);
///
/// let removed = tree.remove(|center, _, _| {
///     if 3 < *center {
///         Navi3::GoDownLeft
///     } else if 3 > *center {
///         Navi3::GoDownRight
///     } else {
///         Navi3::Found
///     }
/// });
/// assert_eq!(removed, Some(3));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Navi3 {
    GoDownLeft,
    Found,
    GoDownRight,
}
impl Navi3 {
    fn by_index<T>(
        index: &mut usize,
        size: &mut impl FnMut(&T) -> usize,
        left: Option<&T>,
    ) -> Self {
        let lsize = left.map_or(0, size);
        match (*index).cmp(&lsize) {
            Ordering::Less => Self::GoDownLeft,
            Ordering::Equal => Self::Found,
            Ordering::Greater => {
                *index -= lsize + 1;
                Self::GoDownRight
            }
        }
    }

    fn by_key<T, K: Borrow<Q>, Q: ?Sized + Ord>(
        probe: &Q,
        center: &T,
        f: &mut impl FnMut(&T) -> K,
    ) -> Self {
        match probe.cmp(f(center).borrow()) {
            Ordering::Less => Self::GoDownLeft,
            Ordering::Equal => Self::Found,
            Ordering::Greater => Self::GoDownRight,
        }
    }
}

/// スプレイ木。ノードの値の型は `O::Store`。
///
/// # 例
///
/// ```
/// use intrusive_splay_tree::{Op, Tree, Navi2, Navi3};
/// use std::cmp::Ordering;
///
/// // ボイラープレート。
/// struct Store {
///     value: u32,
///     sum: u32,
/// }
///
/// enum O {}
/// impl Op for O {
///     type Store = Store;
///
///     fn update(root: &mut Self::Store, left: Option<&Self::Store>, right: Option<&Self::Store>) {
///         root.sum = root.value;
///         if let Some(left) = left {
///             root.sum = left.sum + root.sum;
///         }
///         if let Some(right) = right {
///             root.sum = root.sum + right.sum;
///         }
///     }
/// }
///
///
/// let mut tree = Tree::<O>::new();
///
/// // 挿入。挿入するときは、ノードの完全な値と二分探索方法を指定する必要があります。
/// for value in 10..=13 {
///     tree.insert(Store { value, sum: value }, |center, _left, _right| {
///         match value.cmp(&center.value) {
///             Ordering::Less | Ordering::Equal => Navi2::GoDownLeft,
///             Ordering::Greater => Navi2::GoDownRight,
///         }
///     });
/// }
///
/// // 削除。削除するときもこれを指定する必要があります。
/// tree.remove(|center, _left, _right| {
///     match center.value.cmp(&12) {
///         Ordering::Less => Navi3::GoDownRight,
///         Ordering::Equal => Navi3::Found,
///         Ordering::Greater => Navi3::GoDownLeft,
///    }
/// });
///
/// // デバッグ。
/// assert_eq!(
///     tree.collect(|value| value.value).as_slice(),
///     &[
///         10,
///         11,
///         13,
///     ],
/// );
///
/// // 集約。全体的な集約（`fold()`）のみが利用可能です。
/// assert_eq!(tree.fold().unwrap().sum, 34);
/// ```
pub struct Tree<O: Op> {
    root: Onn<O>,
}

impl<O: Op> Default for Tree<O> {
    fn default() -> Self {
        Self { root: None }
    }
}

impl<O: Op> Drop for Tree<O> {
    fn drop(&mut self) {
        free_subtree(self.root);
    }
}

/// [`range_by_key`](Tree::range_by_key) / [`range_by_index`](Tree::range_by_index) が返す、
/// 範囲への一時的な可変参照。
///
/// 内部では木を 左 / 中央 / 右 の 3 部分木に分割し、中央だけを [`Tree`] として貸し出す
/// （[`Deref`] / [`DerefMut`] で `Tree<O>` として扱える）。左右の部分木には触れないため、
/// 中央への変更が範囲外の要素に影響することはない。drop されると 3 部分を結合し直し、
/// 元のツリーに戻す。
///
/// # 例
///
/// ```
/// use intrusive_splay_tree::Op;
/// use intrusive_splay_tree::Tree;
///
/// enum O {}
/// impl Op for O {
///     type Store = i32;
///
///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
/// }
///
/// let mut tree = Tree::<O>::new();
/// tree.insert_lower_bound_by_key(1, |v| *v);
/// tree.insert_lower_bound_by_key(2, |v| *v);
/// tree.insert_lower_bound_by_key(3, |v| *v);
///
/// // 範囲 [1, 3] を抽出して修正
/// let mut range = tree.range_by_key(1..=3, |v| *v);
/// // 範囲への修正は範囲内に留まります
/// ```
pub struct RangeEntry<'a, O: Op> {
    tree: &'a mut Tree<O>,
    left: Onn<O>,
    center: Tree<O>,
    right: Onn<O>,
}
impl<'a, O: Op> RangeEntry<'a, O> {
    fn new(tree: &'a mut Tree<O>, left: Onn<O>, center: Onn<O>, right: Onn<O>) -> Self {
        Self {
            tree,
            left,
            center: Tree { root: center },
            right,
        }
    }
}
impl<O: Op> Deref for RangeEntry<'_, O> {
    type Target = Tree<O>;

    fn deref(&self) -> &Self::Target {
        &self.center
    }
}
impl<O: Op> DerefMut for RangeEntry<'_, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.center
    }
}
impl<O: Op> Drop for RangeEntry<'_, O> {
    fn drop(&mut self) {
        self.tree.root = merge2(merge2(self.left, self.center.root.take()), self.right);
    }
}

impl<T, O: Op<Store = T>> Tree<O> {
    /// 空のツリーを作る。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let tree = Tree::<O>::new();
    /// assert!(tree.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// ツリーが空なら `true` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let tree = Tree::<O>::new();
    /// assert!(tree.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    /// ツリーの集約サイズを $O(1)$ で返す。
    ///
    /// `size` はノードの値からサイズ成分を取り出す関数（1 ノードが複数要素をまとめる場合の要素数など）。
    /// ツリーが空なら 0 を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     size: usize,
    /// }
    /// impl Store {
    ///     fn size(&self) -> usize {
    ///         self.size
    ///     }
    /// }
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left {
    ///             center.size += left.size;
    ///         }
    ///         if let Some(right) = right {
    ///             center.size += right.size;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { size: 1 }, |_| 0);
    /// tree.insert_lower_bound_by_key(Store { size: 1 }, |_| 0);
    ///
    /// assert_eq!(tree.len(Store::size), 2);
    /// ```
    pub fn len(&self, size: impl Fn(&T) -> usize) -> usize {
        self.root
            .map_or(0, |root| unsafe { size(&(*root.as_ptr()).store) })
    }

    /// キー範囲 `range` に含まれる要素を [`RangeEntry`] として切り出す。
    ///
    /// 木を 左 / 中央 / 右 に分割し、中央部分だけを一時的な [`Tree`] として貸し出す。
    /// `f` は各要素からソートキーを取り出す関数。[`RangeEntry`] が drop されると 3 部分が
    /// 自動的に元のツリーへ再結合される。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// // 範囲 [2, 3] 内の要素を取得
    /// let range = tree.range_by_key(2..=3, |v| *v);
    /// let collected = range.collect(|v| *v);
    /// ```
    pub fn range_by_key<K: Borrow<Q>, Q: ?Sized + Ord>(
        &mut self,
        range: impl RangeBounds<Q>,
        mut f: impl FnMut(&T) -> K,
    ) -> RangeEntry<'_, O> {
        let root = self.root.take();
        let (lc, right) = match range.end_bound() {
            Bound::Unbounded => (root, None),
            Bound::Included(key) => split2(root, |center, _, _| {
                Navi2::upper_bound_by_key(key, center, &mut f)
            }),
            Bound::Excluded(key) => split2(root, |center, _, _| {
                Navi2::lower_bound_by_key(key, center, &mut f)
            }),
        };
        let (left, center) = match range.start_bound() {
            Bound::Unbounded => (None, lc),
            Bound::Included(key) => split2(lc, |center, _, _| {
                Navi2::lower_bound_by_key(key, center, &mut f)
            }),
            Bound::Excluded(key) => split2(lc, |center, _, _| {
                Navi2::upper_bound_by_key(key, center, &mut f)
            }),
        };
        RangeEntry::new(self, left, center, right)
    }

    /// インデックス範囲 `range` に含まれる要素を [`RangeEntry`] として切り出す。
    ///
    /// 木を 左 / 中央 / 右 に分割し、中央部分だけを一時的な [`Tree`] として貸し出す。
    /// `size` は各要素の論理的なサイズ（単一要素ノードなら通常 1）。[`RangeEntry`] が drop されると
    /// 3 部分が自動的に元のツリーへ再結合される。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     value: i32,
    ///     size: usize,
    /// }
    /// impl Store {
    ///     fn size(&self) -> usize {
    ///         self.size
    ///     }
    /// }
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left {
    ///             center.size += left.size;
    ///         }
    ///         if let Some(right) = right {
    ///             center.size += right.size;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 10, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Store { value: 20, size: 1 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Store { value: 30, size: 1 }, |v| v.value);
    ///
    /// // インデックス [0, 2) にある要素を取得
    /// let range = tree.range_by_index(0..2, Store::size);
    /// let collected = range.collect(|v| v.value);
    /// ```
    pub fn range_by_index(
        &mut self,
        range: impl RangeBounds<usize>,
        mut size: impl FnMut(&T) -> usize,
    ) -> RangeEntry<'_, O> {
        let root = self.root.take();
        let (root, right) = match range.end_bound() {
            Bound::Unbounded => (root, None),
            Bound::Included(&(mut index)) => {
                index += 1;
                split2(root, |_, left, _| {
                    Navi2::by_index(&mut index, &mut size, left)
                })
            }
            Bound::Excluded(&(mut index)) => split2(root, |_, left, _| {
                Navi2::by_index(&mut index, &mut size, left)
            }),
        };
        let (left, center) = match range.start_bound() {
            Bound::Unbounded => (None, root),
            Bound::Included(&(mut index)) => split2(root, |_, left, _| {
                Navi2::by_index(&mut index, &mut size, left)
            }),
            Bound::Excluded(&(mut index)) => {
                index += 1;
                split2(root, |_, left, _| {
                    Navi2::by_index(&mut index, &mut size, left)
                })
            }
        };
        RangeEntry::new(self, left, center, right)
    }

    /// ツリー全体の集約値への参照を返す（空なら `None`）。
    ///
    /// 集約値は構造が変わるたびに [`Op::update`] が計算済みなので、$O(1)$ で返せる。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     value: i32,
    ///     sum: i32,
    /// }
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.sum = center.value;
    ///         if let Some(l) = left {
    ///             center.sum += l.sum;
    ///         }
    ///         if let Some(r) = right {
    ///             center.sum += r.sum;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 5, sum: 5 }, |v| v.value);
    /// tree.insert_lower_bound_by_key(Store { value: 3, sum: 3 }, |v| v.value);
    ///
    /// assert_eq!(tree.fold().map(|v| v.sum), Some(8));
    /// ```
    pub fn fold(&self) -> Option<&T> {
        unsafe { self.root.map(|root| &(*root.as_ptr()).store) }
    }

    /// クロージャ `f` が指す位置でツリーを2つに分割する。
    ///
    /// `f` は各ノードで [`Navi2`] を返し、進む方向を決める。`self` には分割点までの左側が残り、
    /// 戻り値には右側が入る。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Navi2;
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let mut right =
    ///     tree.split_off(
    ///         |center, _, _| {
    ///             if *center < 3 { Navi2::GoDownRight } else { Navi2::GoDownLeft }
    ///         },
    ///     );
    /// assert_eq!(tree.collect(|_| ()).len(), 1);
    /// assert_eq!(right.collect(|_| ()).len(), 2);
    /// ```
    pub fn split_off(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2) -> Self {
        let (left, right) = split2(self.root.take(), f);
        self.root = left;
        Self { root: right }
    }

    /// インデックス `index` でツリーを分割し、`index` 以降の要素を返す。
    ///
    /// `size` は各要素の論理的なサイズ（単一要素ノードなら通常 1）。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     value: i32,
    ///     size: usize,
    /// }
    /// impl Store {
    ///     fn value(&self) -> i32 {
    ///         self.value
    ///     }
    ///
    ///     fn size(&self) -> usize {
    ///         self.size
    ///     }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left {
    ///             center.size += left.size;
    ///         }
    ///         if let Some(right) = right {
    ///             center.size += right.size;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 1, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 2, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 3, size: 1 }, Store::value);
    ///
    /// let mut rest = tree.split_off_by_index(1, Store::size);
    /// assert_eq!(tree.len(Store::size), 1);
    /// assert_eq!(rest.len(Store::size), 2);
    /// ```
    pub fn split_off_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Self {
        self.split_off(|_center, left, _right| Navi2::by_index(&mut index, &mut size, left))
    }

    /// キー `probe` の下界でツリーを分割し、キーが `probe` 以上の要素を返す。
    ///
    /// プローブ型 `Q` は `Borrow` を介してキー型 `K` と異なっていてもよい。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     key: u32,
    /// }
    /// impl Store {
    ///     fn key(&self) -> u32 {
    ///         self.key
    ///     }
    /// }
    ///
    /// #[derive(Debug, PartialEq)]
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(_: &mut Store, _: Option<&Store>, _: Option<&Store>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { key: 1 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 2 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 3 }, Store::key);
    ///
    /// let mut ge = tree.split_off_lower_bound_by_key(&2, Store::key);
    /// assert_eq!(tree.collect(|_| ()).len(), 1);
    /// assert_eq!(ge.collect(|_| ()).len(), 2);
    /// ```
    pub fn split_off_lower_bound_by_key<K, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Self
    where
        K: Borrow<Q>,
    {
        self.split_off(|center, _left, _right| Navi2::lower_bound_by_key(probe, center, &mut f))
    }

    /// キー `probe` の上界でツリーを分割し、キーが `probe` より大きい要素を返す。
    ///
    /// プローブ型 `Q` は `Borrow` を介してキー型 `K` と異なっていてもよい。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     key: u32,
    /// }
    /// impl Store {
    ///     fn key(&self) -> u32 {
    ///         self.key
    ///     }
    /// }
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(_: &mut Store, _: Option<&Store>, _: Option<&Store>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { key: 1 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 2 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 3 }, Store::key);
    ///
    /// let mut gt = tree.split_off_upper_bound_by_key(&2, Store::key);
    /// assert_eq!(tree.collect(|_| ()).len(), 2);
    /// assert_eq!(gt.collect(|_| ()).len(), 1);
    /// ```
    pub fn split_off_upper_bound_by_key<K, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Self
    where
        K: Borrow<Q>,
    {
        self.split_off(|center, _left, _right| Navi2::upper_bound_by_key(probe, center, &mut f))
    }

    /// `other` を末尾に連結し、`other` を空にする。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree1 = Tree::<O>::new();
    /// tree1.insert_lower_bound_by_key(1, |v| *v);
    /// tree1.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let mut tree2 = Tree::<O>::new();
    /// tree2.insert_lower_bound_by_key(2, |v| *v);
    ///
    /// tree1.append(&mut tree2);
    /// assert_eq!(tree1.collect(|_| ()).len(), 3);
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        self.root = merge2(self.root.take(), other.root.take());
    }

    /// クロージャ `f` に従って探索し、その終端に新しいノードを挿入する。
    ///
    /// `f` は各ノードで [`Navi2`] を返して左右どちらに進むかを決める。指定した方向に子が
    /// 無くなったところへ挿入し、スプレイで木を平衡化する。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Navi2;
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert(5, |center, _, _| {
    ///     if 5 < *center { Navi2::GoDownLeft } else { Navi2::GoDownRight }
    /// });
    /// tree.insert(3, |center, _, _| {
    ///     if 3 < *center { Navi2::GoDownLeft } else { Navi2::GoDownRight }
    /// });
    /// assert_eq!(tree.collect(|_| ()).len(), 2);
    /// ```
    pub fn insert(&mut self, store: T, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi2) {
        let (left, right) = split2(self.root.take(), f);
        let center = unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(Node::new(store)))) };
        self.root = Some(merge3(left, center, right));
    }

    /// インデックス `index` の位置に新しいノードを挿入する。
    ///
    /// `size` は各要素の論理的なサイズ（単一要素ノードなら通常 1）。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     value: i32,
    ///     size: usize,
    /// }
    /// impl Store {
    ///     fn size(&self) -> usize {
    ///         self.size
    ///     }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left {
    ///             center.size += left.size;
    ///         }
    ///         if let Some(right) = right {
    ///             center.size += right.size;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_by_index(Store { value: 1, size: 1 }, 0, Store::size);
    /// tree.insert_by_index(Store { value: 3, size: 1 }, 1, Store::size);
    /// assert_eq!(tree.len(Store::size), 2);
    /// ```
    pub fn insert_by_index(
        &mut self,
        store: T,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) {
        self.insert(store, |_center, left, _right| {
            Navi2::by_index(&mut index, &mut size, left)
        });
    }

    /// キーを抽出し、lower_bound の位置に新しいノードを挿入する。
    ///
    /// 同じキーの要素がある場合は、その左側に挿入される。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    /// tree.insert_lower_bound_by_key(7, |v| *v);
    /// assert_eq!(tree.collect(|_| ()).len(), 3);
    /// ```
    pub fn insert_lower_bound_by_key<K: Ord>(&mut self, store: T, mut f: impl FnMut(&T) -> K) {
        let probe = f(&store);
        self.insert(store, |center, _left, _right| {
            Navi2::lower_bound_by_key(&probe, center, &mut f)
        });
    }

    /// キーを抽出し、upper_bound の位置に新しいノードを挿入する。
    ///
    /// 同じキーの要素がある場合は、その右側に挿入される。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_upper_bound_by_key(5, |v| *v);
    /// tree.insert_upper_bound_by_key(3, |v| *v);
    /// tree.insert_upper_bound_by_key(5, |v| *v);
    /// assert_eq!(tree.collect(|_| ()).len(), 3);
    /// ```
    pub fn insert_upper_bound_by_key<K: Ord>(&mut self, store: T, mut f: impl FnMut(&T) -> K) {
        let probe = f(&store);
        self.insert(store, |center, _left, _right| {
            Navi2::upper_bound_by_key(&probe, center, &mut f)
        });
    }

    /// ツリーの先頭（最も左）に新しいノードを挿入する。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_front(5);
    /// tree.push_front(2);
    ///
    /// assert_eq!(tree.front(), Some(&2));
    /// ```
    pub fn push_front(&mut self, store: T) {
        self.insert(store, |_, _, _| Navi2::GoDownLeft);
    }

    /// ツリーの末尾（最も右）に新しいノードを挿入する。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_back(5);
    /// tree.push_back(7);
    ///
    /// assert_eq!(tree.back(), Some(&7));
    /// ```
    pub fn push_back(&mut self, store: T) {
        self.insert(store, |_, _, _| Navi2::GoDownRight);
    }

    /// クロージャ `f` で目的のノードを特定し、見つかれば削除してその値を返す。
    ///
    /// `f` は各ノードで [`Navi3`] を返し、[`Navi3::Found`] で探索を打ち切れる。
    /// 見つからなければ `None` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Navi3;
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let removed = tree.remove(|center, _, _| {
    ///     if 3 < *center {
    ///         Navi3::GoDownLeft
    ///     } else if 3 > *center {
    ///         Navi3::GoDownRight
    ///     } else {
    ///         Navi3::Found
    ///     }
    /// });
    /// assert_eq!(removed, Some(3));
    /// assert_eq!(tree.collect(|_| ()).len(), 1);
    /// ```
    pub fn remove(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3) -> Option<T> {
        unsafe {
            match split3(self.root.take(), f) {
                Split3Result::Success(left, center, right) => {
                    let store = Box::from_raw(center.as_ptr()).store;
                    self.root = merge2(left, right);
                    Some(store)
                }
                Split3Result::Failure(root) => {
                    self.root = root;
                    None
                }
            }
        }
    }

    /// インデックス `index` のノードを削除し、その値を返す。
    ///
    /// `size` は各要素の論理的なサイズ。インデックスが範囲外なら `None` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     value: i32,
    ///     size: usize,
    /// }
    /// impl Store {
    ///     fn value(&self) -> i32 {
    ///         self.value
    ///     }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left {
    ///             center.size += left.size;
    ///         }
    ///         if let Some(right) = right {
    ///             center.size += right.size;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 1, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 2, size: 1 }, Store::value);
    ///
    /// let removed = tree.remove_by_index(0, |v| v.size);
    /// assert_eq!(removed.as_ref().map(Store::value), Some(1));
    /// ```
    pub fn remove_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<T> {
        self.remove(|_center, left, _right| Navi3::by_index(&mut index, &mut size, left))
    }

    /// 各ノードからキーを抽出し、`probe` と比較してノードを削除する。
    ///
    /// [`remove`](Self::remove) の便利なラッパー。プローブ型 `Q` は `Borrow` を介して
    /// キー型 `K` と異なっていてもよい（例：`String` のノードを `&str` で検索できる）。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let removed = tree.remove_by_key(&3, |v| *v);
    /// assert_eq!(removed, Some(3));
    /// ```
    pub fn remove_by_key<K: Ord + Borrow<Q>, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<T> {
        self.remove(|center, _left, _right| Navi3::by_key(probe, center, &mut f))
    }

    /// ツリーの最小要素（最も左のノード）を削除して返す（空なら `None`）。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_back(5);
    /// tree.push_back(2);
    /// tree.push_back(7);
    ///
    /// assert_eq!(tree.pop_front(), Some(5));
    /// assert_eq!(tree.pop_front(), Some(2));
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.remove(
            |_, left, _| {
                if left.is_some() { Navi3::GoDownLeft } else { Navi3::Found }
            },
        )
    }

    /// ツリーの最大要素（最も右のノード）を削除して返す（空なら `None`）。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.push_back(5);
    /// tree.push_back(2);
    /// tree.push_back(7);
    ///
    /// assert_eq!(tree.pop_back(), Some(7));
    /// assert_eq!(tree.pop_back(), Some(2));
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.remove(
            |_, _, right| {
                if right.is_some() { Navi3::GoDownRight } else { Navi3::Found }
            },
        )
    }

    /// クロージャ `f` に従って探索し、見つかったノードの値への参照を返す。
    ///
    /// ノードは削除されないが、探索経路上のノードはスプレイでルート付近に移動する。
    /// 見つからなければ `None` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Navi3;
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    ///
    /// let found = tree.get(|center, _, _| {
    ///     if 3 < *center {
    ///         Navi3::GoDownLeft
    ///     } else if 3 > *center {
    ///         Navi3::GoDownRight
    ///     } else {
    ///         Navi3::Found
    ///     }
    /// });
    /// assert_eq!(found, Some(&3));
    /// ```
    pub fn get(&mut self, f: impl FnMut(&T, Option<&T>, Option<&T>) -> Navi3) -> Option<&T> {
        unsafe {
            match split3(self.root.take(), f) {
                Split3Result::Success(left, center, right) => {
                    self.root = Some(merge3(left, center, right));
                    Some(&(*center.as_ptr()).store)
                }
                Split3Result::Failure(root) => {
                    self.root = root;
                    None
                }
            }
        }
    }

    /// インデックス `index` のノード値への参照を返す。
    ///
    /// `size` は各要素の論理的なサイズ。インデックスが範囲外なら `None` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     value: i32,
    ///     size: usize,
    /// }
    /// impl Store {
    ///     fn value(&self) -> i32 {
    ///         self.value
    ///     }
    ///
    ///     fn size(&self) -> usize {
    ///         self.size
    ///     }
    /// }
    /// enum O {}
    /// impl Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(center: &mut Store, left: Option<&Store>, right: Option<&Store>) {
    ///         center.size = 1;
    ///         if let Some(left) = left {
    ///             center.size += left.size;
    ///         }
    ///         if let Some(right) = right {
    ///             center.size += right.size;
    ///         }
    ///     }
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { value: 1, size: 1 }, Store::value);
    /// tree.insert_lower_bound_by_key(Store { value: 2, size: 1 }, Store::value);
    ///
    /// let found = tree.get_by_index(1, Store::size);
    /// assert_eq!(found.map(Store::value), Some(2));
    /// ```
    pub fn get_by_index(
        &mut self,
        mut index: usize,
        mut size: impl FnMut(&T) -> usize,
    ) -> Option<&T> {
        self.get(|_center, left, _right| Navi3::by_index(&mut index, &mut size, left))
    }

    /// 各ノードからキーを抽出し、`probe` と比較してノード値への参照を返す。
    ///
    /// プローブ型 `Q` は `Borrow` を介してキー型 `K` と異なっていてもよい。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Tree;
    ///
    /// struct Store {
    ///     key: u32,
    /// }
    /// impl Store {
    ///     fn key(&self) -> u32 {
    ///         self.key
    ///     }
    /// }
    /// enum O {}
    /// impl intrusive_splay_tree::Op for O {
    ///     type Store = Store;
    ///
    ///     fn update(_: &mut Store, _: Option<&Store>, _: Option<&Store>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(Store { key: 5 }, Store::key);
    /// tree.insert_lower_bound_by_key(Store { key: 3 }, Store::key);
    ///
    /// let found = tree.get_by_key(&3, Store::key);
    /// assert_eq!(found.map(Store::key), Some(3));
    /// ```
    pub fn get_by_key<K: Ord + Borrow<Q>, Q: ?Sized + Ord>(
        &mut self,
        probe: &Q,
        mut f: impl FnMut(&T) -> K,
    ) -> Option<&T> {
        self.get(|center, _left, _right| Navi3::by_key(probe, center, &mut f))
    }

    /// ツリーの最小要素（最も左のノード）への参照を返す（空なら `None`）。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    /// tree.insert_lower_bound_by_key(7, |v| *v);
    ///
    /// assert_eq!(tree.front(), Some(&2));
    /// ```
    pub fn front(&mut self) -> Option<&T> {
        self.get(
            |_, left, _| {
                if left.is_some() { Navi3::GoDownLeft } else { Navi3::Found }
            },
        )
    }

    /// ツリーの最大要素（最も右のノード）への参照を返す（空なら `None`）。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(5, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    /// tree.insert_lower_bound_by_key(7, |v| *v);
    ///
    /// assert_eq!(tree.back(), Some(&7));
    /// ```
    pub fn back(&mut self) -> Option<&T> {
        self.get(
            |_, _, right| {
                if right.is_some() { Navi3::GoDownRight } else { Navi3::Found }
            },
        )
    }

    /// 中順（in-order）にたどりながら `f` を各値に適用し、結果を `Vec` に集める。
    ///
    /// キー順（ツリーの自然な並び）でソートされた列が得られる。
    ///
    /// # 例
    ///
    /// ```
    /// use intrusive_splay_tree::Op;
    /// use intrusive_splay_tree::Tree;
    ///
    /// enum O {}
    /// impl Op for O {
    ///     type Store = i32;
    ///
    ///     fn update(_: &mut i32, _: Option<&i32>, _: Option<&i32>) {}
    /// }
    ///
    /// let mut tree = Tree::<O>::new();
    /// tree.insert_lower_bound_by_key(3, |v| *v);
    /// tree.insert_lower_bound_by_key(1, |v| *v);
    /// tree.insert_lower_bound_by_key(2, |v| *v);
    ///
    /// let values = tree.collect(|v| *v);
    /// assert_eq!(values, vec![1, 2, 3]);
    /// ```
    pub fn collect<U>(&self, f: impl Fn(&T) -> U) -> Vec<U> {
        let mut out = vec![];
        visit::<T, O>(self.root, &mut |store| out.push(f(store)));
        out
    }
}

/// 構造変更のたびに集約値を再計算するロジックを定義するトレイト。
///
/// [`update`](Op::update) は、ノードが挿入・削除・回転されるたびに呼ばれる。
/// ノードの値と左右の子の集約値を受け取り、そのノードの集約値（合計・最小値・最大値など）を
/// $O(1)$ で更新することで、ツリー全体の集約を $O(\log n)$ 償却で保守できる。
///
/// `update` の計算は結合律に従い、木の形やトラバース順序に依存してはならない
/// （回転で親子関係が変わっても集約結果が変わらないようにするため）。
///
/// # 例
///
/// ```
/// use intrusive_splay_tree::Navi2;
/// use intrusive_splay_tree::Op;
/// use intrusive_splay_tree::Tree;
///
/// struct Store {
///     value: i32,
///     sum: i32,
/// }
///
/// enum MyOp {}
/// impl Op for MyOp {
///     type Store = Store;
///
///     fn update(root: &mut Store, left: Option<&Store>, right: Option<&Store>) {
///         root.sum = root.value;
///         if let Some(l) = left {
///             root.sum += l.sum;
///         }
///         if let Some(r) = right {
///             root.sum += r.sum;
///         }
///     }
/// }
///
/// let mut tree = Tree::<MyOp>::new();
/// tree.insert(Store { value: 5, sum: 5 }, |_, _, _| Navi2::GoDownRight);
/// tree.insert(Store { value: 3, sum: 3 }, |_, _, _| Navi2::GoDownRight);
/// assert_eq!(tree.fold().unwrap().sum, 8);
/// ```
pub trait Op: Sized {
    type Store;
    fn update(center: &mut Self::Store, left: Option<&Self::Store>, right: Option<&Self::Store>);
}
