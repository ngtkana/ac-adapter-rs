//! 動的集約に対応した柔軟な二分探索木のための割り込み型スプレイ木。
//!
//! このクレートは、[`Op`] トレイトを介してノード構造と集約ロジックを定義するスプレイ木を提供します。
//! 部分木に対して任意の集約値（合計、最小値、最大値など）を計算しながら、
//! 効率的なツリー操作が可能になります。
//!
//! # 使用時期
//!
//! 以下が必要な場合に、このクレートを使用してください：
//! - O(log n) 償却時間の自己平衡二分探索木
//! - ノード値とツリー集約に対する柔軟な制御
//! - 同じデータセットに対する頻繁な挿入、削除、クエリ
//! - 要素への順序付きアクセス（例：ソート済み範囲やk番目要素クエリ）
//!
//! # 仕組み
//!
//! 挿入と削除操作は、各ノードで比較するクロージャを使ってトラバーサルを制御します。
//! ツリーは**スプレイ**（アクセスされたノードをルートに移動）によってリバランスされます。
//! これは、同じノードまたは近くのノードに繰り返しアクセスする場合に特に効率的です。
//!
//! [`Op`] トレイトを実装することで集約（例：値の合計）を定義でき、
//! ツリー構造が変更されるたびに呼び出されます。
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
//! impl Store {
//!     fn value(&self) -> i32 {
//!         self.value
//!     }
//! }
//!
//! enum O {}
//! impl Op for O {
//!     type Store = Store;
//!
//!     fn update(node: &mut Store, left: Option<&Store>, right: Option<&Store>) {
//!         node.sum = node.value;
//!         if let Some(l) = left {
//!             node.sum += l.sum;
//!         }
//!         if let Some(r) = right {
//!             node.sum += r.sum;
//!         }
//!     }
//! }
//!
//! let mut tree = Tree::<O>::new();
//! tree.insert_lower_bound_by_key(Store { value: 10, sum: 10 }, Store::value);
//! tree.insert_lower_bound_by_key(Store { value: 5, sum: 5 }, Store::value);
//!
//! // ツリー全体の集約をクエリ
//! assert_eq!(tree.fold().unwrap().sum, 15);
//! ```
//!
//! # コア要素
//!
//! - [`Tree<O>`] — メインのスプレイ木構造
//! - [`Op`] — 集約ロジックを定義するトレイト
//! - [`Navi2`] — 挿入/分割操作用のナビゲーション列挙型（終わらない検索）
//! - [`Navi3`] — 削除/取得操作用のナビゲーション列挙型（早期終了可能）
//!
//! # 計算量
//!
//! すべての操作（挿入、削除、取得、分割、マージ）は **O(log n) 償却時間**です。
//! スプレイにより、頻繁にアクセスされる要素がルートの近くに移動します。

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

/// 常に進行する二分探索のナビゲーション方向（早期終了しない）。
///
/// この列挙型は [`insert`](Tree::insert)、[`split_off`](Tree::split_off)、
/// および関連操作で使用されます。検索がリーフに達するまで続くため、
/// 常に特定の位置への挿入または分割で終わります。
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

/// ターゲットを見つけたら早期に終了できる二分探索のナビゲーション方向。
///
/// この列挙型は [`remove`](Tree::remove)、[`get`](Tree::get)、
/// および関連操作で使用されます。現在のノードがターゲットであるか、
/// または左または右で検索を続けるかを伝える方法を提供します。
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

/// スプレイ木。
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

/// ツリー内の要素の範囲への可変参照。
///
/// この型は [`range_by_key`](Tree::range_by_key) と [`range_by_index`](Tree::range_by_index) から返されます。
/// ツリー全体の構造を保持しながら、連続した範囲への一時的な可変アクセスを提供します。
/// エントリがドロップされるとき、範囲は自動的にツリーに再統合されます。
///
/// # 不変性
///
/// `RangeEntry` はツリー構造の不変性を保持します：
/// - ツリーは 3 つの部分に分割されます：左（未変更）、中央（範囲）、右（未変更）
/// - 中央を修正しても、左または右の部分木には影響しません
/// - ドロップされるとき、3 つの部分すべてが自動的にマージされます
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
    /// 新しい空のツリーを作成します。
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

    /// ツリーが空の場合 `true` を返します。
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

    /// 提供されたサイズ関数を使用して、ツリーの合計サイズを返します。
    ///
    /// サイズ関数は通常、集約サイズ情報を計算するために使用されます
    /// （例：各要素が複数のインデックスにまたがることができる場合の要素数の合計）。
    /// ツリーが [`Op`] トレイトを介してサイズ情報を保持している場合、
    /// ルートノードの集約値から抽出できます。
    ///
    /// # 引数
    ///
    /// * `size` - 集約値のサイズコンポーネントを計算するクロージャ
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

    /// キーの境界により要素の範囲を抽出し、その範囲への可変参照を返します。
    ///
    /// このメソッドは、指定されたキー範囲内の要素を分離するためにツリーを分割し、
    /// [`Deref`] と [`DerefMut`] を [`Tree<O>`] に実装する [`RangeEntry`] を提供します。
    /// エントリがドロップされるとき、範囲は自動的に元のツリーに再統合されます。
    ///
    /// # 引数
    ///
    /// * `range` - 範囲の境界（標準 Rust [`RangeBounds`] 構文を使用：`..`、`1..`、`..3`、`1..3`、`1..=3` など）
    /// * `f` - 各要素からソート可能なキーを抽出するクロージャ
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

    /// インデックスの境界により要素の範囲を抽出し、その範囲への可変参照を返します。
    ///
    /// このメソッドは、指定された範囲内のインデックスにある要素を分離するためにツリーを分割し、
    /// [`Deref`] と [`DerefMut`] を [`Tree<O>`] に実装する [`RangeEntry`] を提供します。
    /// エントリがドロップされるとき、範囲は自動的に元のツリーに再統合されます。
    ///
    /// # 引数
    ///
    /// * `range` - インデックスの境界（標準 Rust [`RangeBounds`] 構文を使用）
    /// * `size` - 各要素の論理的なサイズを計算するクロージャ（単一要素ノードの場合は通常 1）
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

    /// ツリー全体の集約値を計算して返します。
    ///
    /// このメソッドは、ツリーのルートで管理される集約値への参照を返します。
    /// 集約は、ツリー構造が変更されるたびに [`Op`] トレイトの [`update`](Op::update) メソッドによって計算されます。
    /// 集約は常に最新に保たれているため、これは O(1) です。
    ///
    /// ツリーが空の場合は `None` を返します。
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

    /// カスタムクロージャを使用してツリーを分割します。
    ///
    /// クロージャは各ノードで呼び出され、左または右に下降するかを決定します。
    /// ツリーは、このツリーが左の部分木を保持し、返されるツリーが
    /// 分割ポイントで右の部分木を取得するように分割されます。
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

    /// 指定されたインデックスでツリーを分割し、そのインデックス以降の要素を返します。
    ///
    /// サイズ関数を使用してサブツリーサイズを計算し、分割操作を制御します。
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

    /// キーの下限でツリーを分割し、キー以上の要素を返します。
    ///
    /// プローブ型 `Q` は `Borrow` を介してキー型 `K` と異なる場合があります。
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

    /// キーの上限でツリーを分割し、キーより大きい要素を返します。
    ///
    /// プローブ型 `Q` は `Borrow` を介してキー型 `K` と異なる場合があります。
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

    /// 別のツリーをこのツリーに連結し、他のツリーを消費します。
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

    /// クロージャを使用してトラバーサルを制御して、新しいノードを挿入します。
    ///
    /// クロージャは各ノードで呼び出され、左または右に下降するかを決定します。
    /// 新しいノードは境界を遭遇したとき（選択された方向に子がない）に挿入されます。
    /// ツリーはスプレイによってリバランスされます。
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

    /// 指定されたインデックス位置に新しいノードを挿入します。
    ///
    /// サイズ関数を使用してサブツリーサイズを計算し、挿入を制御します。
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

    /// キーを抽出して lower_bound のセマンティクスを使用して、新しいノードを挿入します。
    ///
    /// 重複は左に挿入されます（複数の同じキーを許可）。
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

    /// キーを抽出して upper_bound のセマンティクスを使用して、新しいノードを挿入します。
    ///
    /// 重複は右に挿入されます（複数の同じキーを許可）。
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

    /// ツリーの前（最も左の位置）に新しいノードを挿入します。
    ///
    /// このメソッドは常にリーフに達するまで左にナビゲートし、
    /// 新しいノードを最も左の要素として挿入します。ツリーはスプレイによってリバランスされます。
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

    /// ツリーの後ろ（最も右の位置）に新しいノードを挿入します。
    ///
    /// このメソッドは常にリーフに達するまで右にナビゲートし、
    /// 新しいノードを最も右の要素として挿入します。ツリーはスプレイによってリバランスされます。
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

    /// クロージャを使用してトラバーサルを制御し、ターゲットを識別してノードを削除します。
    ///
    /// クロージャは各ノードで呼び出され、左、右に下降するか、またはノードが見つかったかを決定します。
    /// 見つかった場合、ノードが削除され、その値が返されます。そうでない場合は `None` が返されます。
    /// ツリーはスプレイによってリバランスされます。
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

    /// 指定されたインデックスのノードを削除し、その値を返します。
    ///
    /// サイズ関数を使用してサブツリーサイズを計算し、削除を制御します。
    /// インデックスが範囲外の場合は `None` を返します。
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

    /// 各ノードからキーを抽出し、プローブと比較してノードを削除します。
    ///
    /// これは [`remove`](Self::remove) の便利なラッパーで、各ノード値からキーを抽出し、
    /// `Ord` を使用してプローブと比較します。プローブ型 `Q` はキー型 `K` と正確に一致する必要はありません。
    /// `K` が `Borrow<Q>` を実装している限り（例えば、`String` ノードが `&str` で検索できるようにします）。
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

    /// ツリーの最小要素（最も左のノード）を削除して返します。
    ///
    /// このメソッドは最も左のノードにナビゲートし、それを削除して、その値を返します。
    /// ツリーが空の場合は `None` を返します。ツリーはスプレイによってリバランスされます。
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

    /// ツリーの最大要素（最も右のノード）を削除して返します。
    ///
    /// このメソッドは最も右のノードにナビゲートし、それを削除して、その値を返します。
    /// ツリーが空の場合は `None` を返します。ツリーはスプレイによってリバランスされます。
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

    /// クロージャで導かれたトラバーサルを介してノード値への参照を取得します。
    ///
    /// クロージャは各ノードで呼び出され、左、右に下降するか、見つかったかを決定します。
    /// ツリーはスプレイによってリバランスされますが、ノードは削除されません。
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

    /// 指定されたインデックスのノード値への参照を取得します。
    ///
    /// サイズ関数を使用してサブツリーサイズを計算し、検索を制御します。
    /// インデックスが範囲外の場合は `None` を返します。
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

    /// キーを抽出して比較することで、ノード値への参照を取得します。
    ///
    /// プローブ型 `Q` は `Borrow` を介してキー型 `K` と異なる場合があります。
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

    /// ツリーの最小要素（最も左のノード）への参照を返します。
    ///
    /// このメソッドはツリーの最も左のノードにナビゲートします。このノードは
    /// 最小値を含んでいます。ツリーが空の場合は `None` を返します。
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

    /// ツリーの最大要素（最も右のノード）への参照を返します。
    ///
    /// このメソッドはツリーの最も右のノードにナビゲートします。このノードは
    /// 最大値を含んでいます。ツリーが空の場合は `None` を返します。
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

    /// ツリーから変換を適用してすべての要素をベクターに集約します。
    ///
    /// このメソッドは、提供された変換関数を適用した後、各要素を集約して
    /// ツリーの中順トラバーサルを実行します。結果はツリーの自然な順序
    /// （左から右の中順トラバーサル）でソート済みです。
    ///
    /// # 引数
    ///
    /// * `f` - 各要素値を出力型に変換するクロージャ
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

/// 構造的な変更の際に実行する内容を指定するアダプタトレイト。
///
/// [`update`](Op::update) メソッドは、ノードが挿入、削除、または回転されるたびに呼び出されます。
/// このメソッドは、ノードの値と左および右の子の集約値への参照を受け取り、
/// ツリー全体の集約（例：合計、最小値、最大値）を O(log n) 時間で保守できます。
///
/// # 不変性
///
/// `update` メソッドは結合法則に従う必要があり、ツリー構造またはトラバーサル順序に依存しないようにする必要があります。
/// この不変性に違反する実装は、不正な集約結果を生成します。
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
