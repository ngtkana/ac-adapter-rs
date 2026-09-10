//! 二分ヒープを用いた要素の遅延削除と、順序統計量（中央値等）の管理。
//!
//! [`RemovableHeap`] は本体用・削除予定用の二本の二分ヒープを持ち、要素の削除を
//! $O(\log n)$ で行う。削除は要素を削除予定ヒープに積むだけで、本体ヒープの
//! 最大値と削除予定ヒープの最大値が一致する間はその場で両方から取り除く
//! （settle）ことで、実際の削除を遅延させる。
//!
//! [`DoubleHeap`] は [`RemovableHeap`] を左右2本組み合わせ、「左側の最大値 $\le$
//! 右側の最小値」という不変条件を保ったまま要素を管理する。
//! [`DoubleHeap::balance_left`] で左側の要素数をちょうど $k$ 個に揃えれば、
//! 右側の最小値が $(k+1)$ 番目に小さい要素になるので、中央値やより一般の
//! 順序統計量を追跡できる。要素が左右間を移動するたびに [`Handler`] のコール
//! バックが呼ばれるので、総和などの集約値も移動と同時に $O(1)$ で更新できる。
//!
//! # 仕様
//!
//! - [`RemovableHeap::push`][]: 要素を挿入する
//! - [`RemovableHeap::remove_unchecked`][]: ヒープに入っている要素を1つ削除する — ヒープに入っていない要素を指定すると以降の結果が不正になる
//! - [`RemovableHeap::pop`] / [`RemovableHeap::peek`][]: 最大要素の削除・参照
//! - [`DoubleHeap::push_front`] / [`DoubleHeap::push_back`][]: 左右いずれかへ要素を挿入する
//! - [`DoubleHeap::move_left`] / [`DoubleHeap::move_right`][]: 反対側の境界の要素を1つ移動する
//! - [`DoubleHeap::balance_left`] / [`DoubleHeap::balance_right`][]: 左（右）側の要素数をちょうど $k$ 個に揃える
//! - [`Handler`][]: `push_front` / `pop_front` / `push_back` / `pop_back` の4つのコールバックを持つトレイト — [`Nop`]（何もしない）と [`Sum`]（総和を集計）を用意
//!
//! # 例
//!
//! ```
//! use heap_tricks::DoubleHeap;
//!
//! let mut heap = DoubleHeap::new();
//! heap.push_front(3);
//! heap.push_front(1);
//! heap.push_front(4);
//! heap.balance_left(1); // 左側を要素数1に揃える
//! assert_eq!(heap.peek_back(), Some(3)); // ソート列 [1, 3, 4] の中央値
//! ```
//!
//! # 計算量
//!
//! - [`RemovableHeap`] の各操作: $O(\log n)$
//! - [`DoubleHeap`] の各操作: $O(\log n)$

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::AddAssign;
use std::ops::SubAssign;

/// 要素の挿入・削除に応じて集約値を更新するためのコールバック。
///
/// [`DoubleHeap`] が要素を左右へ挿入・削除・移動するたびに対応するメソッドを
/// 呼び出す。何もしない実装として [`Nop`]、総和を集計する実装として [`Sum`]
/// を用意しているので、通常はどちらかを使えば十分。必要なら自分で実装もできる。
pub trait Handler<T> {
    /// 左側への挿入時に呼ばれる。
    fn push_front(&mut self, value: T);
    /// 左側からの削除時に呼ばれる。
    fn pop_front(&mut self, value: T);
    /// 右側への挿入時に呼ばれる。
    fn push_back(&mut self, value: T);
    /// 右側からの削除時に呼ばれる。
    fn pop_back(&mut self, value: T);
}
/// 何も集約しない [`Handler`]。
///
/// [`DoubleHeap::new`] で構築すると自動的に採用される。Unit-like struct なので、
/// 同名の定数 `Nop` がそのまま値として使える。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, Copy)]
pub struct Nop;
impl<T> Handler<T> for Nop {
    fn push_front(&mut self, _value: T) {}

    fn pop_front(&mut self, _value: T) {}

    fn push_back(&mut self, _value: T) {}

    fn pop_back(&mut self, _value: T) {}
}
/// 左右それぞれの要素の総和を集約する [`Handler`]。
///
/// `left` に左側ヒープの要素の総和、`right` に右側ヒープの要素の総和を保つ。
/// [`Sum::default()`] で総和 0 の状態から構築できる。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, Copy)]
pub struct Sum<T> {
    /// 左側ヒープの要素の総和
    pub left: T,
    /// 右側ヒープの要素の総和
    pub right: T,
}
impl<T> Handler<T> for Sum<T>
where
    T: AddAssign<T> + SubAssign<T>,
{
    fn push_front(&mut self, value: T) {
        self.left += value;
    }

    fn pop_front(&mut self, value: T) {
        self.left -= value;
    }

    fn push_back(&mut self, value: T) {
        self.right += value;
    }

    fn pop_back(&mut self, value: T) {
        self.right -= value;
    }
}

/// 二本の [`RemovableHeap`] で要素を左右に分割して管理し、順序統計量を取得できるヒープ。
///
/// 「左側の最大値 $\le$ 右側の最小値」という不変条件を常に保つ。
/// [`Handler`] が不要なときは [`DoubleHeap::new`] で構築すると自動的に
/// [`Nop`] が採用される。
#[derive(Clone)]
pub struct DoubleHeap<T, H> {
    left: RemovableHeap<T>,
    right: RemovableHeap<Reverse<T>>,
    handler: H,
}
#[allow(clippy::missing_fields_in_debug)]
impl<T, H> Debug for DoubleHeap<T, H>
where
    T: Copy + Ord + Hash + Debug,
    H: Handler<T> + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DoubleHeap")
            .field("elm", &[
                self.collect_left_sorted_vec(),
                self.collect_right_sorted_vec(),
            ])
            .field("handler", &self.handler)
            .finish()
    }
}
impl<T> Default for DoubleHeap<T, Nop>
where
    T: Copy + Ord + Hash,
{
    fn default() -> Self {
        Self {
            left: RemovableHeap::default(),
            right: RemovableHeap::default(),
            handler: Nop,
        }
    }
}
impl<T> DoubleHeap<T, Nop>
where
    T: Copy + Ord + Hash,
{
    /// 空のヒープを構築する。[`Handler`] には [`Nop`] が採用される。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(1);
    /// assert_eq!(heap.collect_sorted_vec(), vec![1]);
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
}
impl<T, H> DoubleHeap<T, H>
where
    T: Copy + Ord + Hash,
    H: Handler<T>,
{
    /// [`Handler`] を指定して空のヒープを構築する。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// assert_eq!(heap.collect_sorted_vec(), vec![42]);
    /// ```
    pub fn with_handler(handler: H) -> Self {
        Self {
            left: RemovableHeap::default(),
            right: RemovableHeap::default(),
            handler,
        }
    }

    /// ヒープが空なら `true` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert!(heap.is_empty());
    /// heap.push_front(42);
    /// assert!(!heap.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.left.is_empty() && self.right.is_empty()
    }

    /// 全体の要素数を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert_eq!(heap.len(), 0);
    /// heap.push_front(42);
    /// assert_eq!(heap.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.left.len() + self.right.len()
    }

    /// 左側ヒープの要素数を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert_eq!(heap.left_len(), 0);
    /// heap.push_front(42);
    /// heap.push_back(42);
    /// heap.push_back(42);
    /// assert_eq!(heap.left_len(), 1);
    /// ```
    pub fn left_len(&self) -> usize {
        self.left.len()
    }

    /// 右側ヒープの要素数を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert_eq!(heap.right_len(), 0);
    /// heap.push_front(42);
    /// heap.push_back(42);
    /// heap.push_back(42);
    /// assert_eq!(heap.right_len(), 2);
    /// ```
    pub fn right_len(&self) -> usize {
        self.right.len()
    }

    /// 左側ヒープの要素数が1増加するように要素を挿入する。$O(\log n)$。
    ///
    /// 不変条件（左側の最大値 $\le$ 右側の最小値）を保つため、必要なら
    /// 右側との間で最大1要素を入れ替える。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    ///
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn push_front(&mut self, elm: T) {
        self.handler.push_front(elm);
        self.left.push(elm);
        self.settle();
    }

    /// 右側ヒープの要素数が1増加するように要素を挿入する。$O(\log n)$。
    ///
    /// 不変条件（左側の最大値 $\le$ 右側の最小値）を保つため、必要なら
    /// 左側との間で最大1要素を入れ替える。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    ///
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn push_back(&mut self, elm: T) {
        self.handler.push_back(elm);
        self.right.push(Reverse(elm));
        self.settle();
    }

    /// 左側ヒープの最大要素があれば返す。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// assert_eq!(heap.peek_front(), Some(13));
    /// ```
    pub fn peek_front(&self) -> Option<T> {
        self.left.peek()
    }

    /// 右側ヒープの最小要素があれば返す。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// assert_eq!(heap.peek_back(), Some(42));
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn peek_back(&self) -> Option<T> {
        self.right.peek().map(|rev| rev.0)
    }

    /// 左側ヒープの最大要素があれば削除して返す。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// assert_eq!(heap.pop_front(), Some(13));
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        let ans = self.left.pop();
        self.settle();
        ans
    }

    /// 右側ヒープの最小要素があれば削除して返す。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// assert_eq!(heap.pop_back(), Some(42));
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![45]);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        let ans = self.right.pop().map(|rev| rev.0);
        self.settle();
        ans
    }

    /// 右側ヒープの最小要素を左側へ移動する。左側の要素数が1増加する。$O(\log n)$。
    ///
    /// # Panics
    ///
    /// 右側ヒープが空のとき。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// heap.move_left();
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13, 42]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![45]);
    /// ```
    pub fn move_left(&mut self) {
        let elm = self.right.pop().expect("右側ヒープは空です。").0;
        self.handler.pop_back(elm);
        self.handler.push_front(elm);
        self.left.push(elm);
        self.settle();
    }

    /// 左側ヒープの最大要素を右側へ移動する。右側の要素数が1増加する。$O(\log n)$。
    ///
    /// # Panics
    ///
    /// 左側ヒープが空のとき。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// heap.move_right();
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![13, 42, 45]);
    /// ```
    pub fn move_right(&mut self) {
        let elm = self.left.pop().expect("左側ヒープは空です。");
        self.handler.pop_front(elm);
        self.handler.push_back(elm);
        self.right.push(Reverse(elm));
        self.settle();
    }

    /// 左側ヒープの要素数が1減少するように、ヒープ中の要素 `elm` を1つ削除する。$O(\log n)$。
    ///
    /// `elm` がどちら側にあるかは問わない（右側にあれば削除後に
    /// [`move_right`](Self::move_right) 相当の移動を行い、左側の要素数の
    /// 減少だけを保証する）。
    ///
    /// `elm` と等しい要素がヒープに入っていない場合、以降のすべての操作の
    /// 結果が不正になる。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// heap.remove_left_unchecked(42);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![13, 45]);
    /// ```
    pub fn remove_left_unchecked(&mut self, elm: T) {
        if self.left.peek().is_some_and(|lmax| elm <= lmax) {
            self.handler.pop_front(elm);
            self.left.remove_unchecked(elm);
            self.settle();
        } else {
            self.handler.pop_back(elm);
            self.right.remove_unchecked(Reverse(elm));
            self.settle();
            self.move_right();
        }
    }

    /// 右側ヒープの要素数が1減少するように、ヒープ中の要素 `elm` を1つ削除する。$O(\log n)$。
    ///
    /// `elm` がどちら側にあるかは問わない（左側にあれば削除後に
    /// [`move_left`](Self::move_left) 相当の移動を行い、右側の要素数の
    /// 減少だけを保証する）。
    ///
    /// `elm` と等しい要素がヒープに入っていない場合、以降のすべての操作の
    /// 結果が不正になる。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(42);
    /// heap.push_back(45);
    /// heap.push_back(13);
    /// heap.remove_right_unchecked(42);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![45]);
    /// ```
    pub fn remove_right_unchecked(&mut self, elm: T) {
        if self.left.peek().is_some_and(|lmax| elm <= lmax) {
            self.handler.pop_front(elm);
            self.left.remove_unchecked(elm);
            self.settle();
            self.move_left();
        } else {
            self.handler.pop_back(elm);
            self.right.remove_unchecked(Reverse(elm));
            self.settle();
        }
    }

    /// 左側ヒープの要素数がちょうど `k` 個になるまで、左右間で要素を移動する。
    ///
    /// 左側は小さい方から $k$ 個の要素を持つことになるので、
    /// [`peek_back`](Self::peek_back) で $(k+1)$ 番目に小さい要素（順序統計量）
    /// が得られる。$O(|k - \text{左側の要素数}| \log n)$。
    ///
    /// # Panics
    ///
    /// `k` が総要素数よりも大きいとき。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(10);
    /// heap.push_front(11);
    /// heap.push_front(12);
    /// heap.push_back(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![10, 11, 12]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![13]);
    ///
    /// heap.balance_left(1);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![10]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![11, 12, 13]);
    /// ```
    pub fn balance_left(&mut self, k: usize) {
        assert!(k <= self.len());
        while self.left_len() < k {
            self.move_left();
        }
        while self.left_len() > k {
            self.move_right();
        }
    }

    /// 右側ヒープの要素数がちょうど `k` 個になるまで、左右間で要素を移動する。
    ///
    /// 右側は大きい方から $k$ 個の要素を持つことになるので、
    /// [`peek_front`](Self::peek_front) で $(n-k)$ 番目に小さい要素（順序統計量）
    /// が得られる。$O(|k - \text{右側の要素数}| \log n)$。
    ///
    /// # Panics
    ///
    /// `k` が総要素数よりも大きいとき。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(10);
    /// heap.push_front(11);
    /// heap.push_front(12);
    /// heap.push_back(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![10, 11, 12]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![13]);
    ///
    /// heap.balance_right(3);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![10]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![11, 12, 13]);
    /// ```
    pub fn balance_right(&mut self, k: usize) {
        assert!(k <= self.len());
        while self.right_len() < k {
            self.move_right();
        }
        while self.right_len() > k {
            self.move_left();
        }
    }

    /// [`Handler`] への参照を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// use heap_tricks::Sum;
    /// let mut heap = DoubleHeap::with_handler(Sum::default());
    /// heap.push_front(10);
    /// heap.push_front(11);
    /// heap.push_front(12);
    /// heap.push_back(13);
    /// assert_eq!(heap.handler().left, 33);
    /// assert_eq!(heap.handler().right, 13);
    ///
    /// heap.balance_left(1);
    /// assert_eq!(heap.handler().left, 10);
    /// assert_eq!(heap.handler().right, 36);
    /// ```
    pub fn handler(&self) -> &H {
        &self.handler
    }

    /// 左側ヒープの要素を昇順に並べたベクターを構築する。$O(k \log k)$（$k$ は左側の要素数）。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(10);
    /// heap.push_front(11);
    /// heap.push_front(12);
    /// heap.push_back(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![10, 11, 12]);
    /// ```
    pub fn collect_left_sorted_vec(&self) -> Vec<T> {
        self.left.collect_sorted_vec()
    }

    /// 右側ヒープの要素を昇順に並べたベクターを構築する。$O(k \log k)$（$k$ は右側の要素数）。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(10);
    /// heap.push_front(11);
    /// heap.push_front(12);
    /// heap.push_back(13);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![13]);
    /// ```
    pub fn collect_right_sorted_vec(&self) -> Vec<T> {
        self.right
            .collect_sorted_vec()
            .into_iter()
            .rev()
            .map(|rev| rev.0)
            .collect()
    }

    /// すべての要素を昇順に並べたベクターを構築する。$O(n \log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_front(10);
    /// heap.push_front(11);
    /// heap.push_front(12);
    /// heap.push_back(13);
    /// assert_eq!(heap.collect_sorted_vec(), vec![10, 11, 12, 13]);
    /// ```
    pub fn collect_sorted_vec(&self) -> Vec<T> {
        let mut left = self.left.collect_sorted_vec();
        let right = self.right.collect_sorted_vec();
        left.extend(right.into_iter().rev().map(|rev| rev.0));
        left
    }

    fn settle(&mut self) {
        while !self.left.is_empty()
            && !self.right.is_empty()
            && self.left.peek().unwrap() > self.right.peek().unwrap().0
        {
            let elm = self.right.pop().unwrap().0;
            self.handler.pop_back(elm);
            self.handler.push_front(elm);
            self.left.push(elm);
            let elm = self.left.pop().unwrap();
            self.handler.pop_front(elm);
            self.handler.push_back(elm);
            self.right.push(Reverse(elm));
        }
    }
}

/// 遅延削除のできる二分ヒープ。
///
/// 本体用・削除予定用の2本の [`BinaryHeap`] を持つ。削除は要素を削除予定
/// ヒープへ積むだけで完了し（$O(\log n)$）、本体ヒープの最大値と削除予定
/// ヒープの最大値が一致する間はその場で両方から取り除く（settle）ことで、
/// 実際の削除操作を先延ばしにする。
///
/// [`remove_unchecked`](Self::remove_unchecked) にヒープへ入っていない要素を
/// 指定すると、たとえ直後に同じ要素を挿入し直しても、本体・削除予定の対応
/// 関係が崩れたままになり、以降のすべての操作の結果が不正になる。
#[derive(Clone)]
pub struct RemovableHeap<T> {
    heap: BinaryHeap<T>,
    removed: BinaryHeap<T>,
    len: usize,
}
impl<T: Copy + Ord + Hash + Debug> Debug for RemovableHeap<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.collect_sorted_vec()).finish()
    }
}
impl<T: Copy + Ord + Hash> FromIterator<T> for RemovableHeap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let heap = BinaryHeap::from_iter(iter);
        Self {
            len: heap.len(),
            heap,
            removed: BinaryHeap::default(),
        }
    }
}
impl<T: Copy + Ord + Hash> Default for RemovableHeap<T> {
    fn default() -> Self {
        Self {
            heap: BinaryHeap::default(),
            removed: BinaryHeap::default(),
            len: 0,
        }
    }
}
impl<T: Copy + Ord + Hash> RemovableHeap<T> {
    /// 空のヒープを構築する。
    ///
    /// # 例
    ///
    /// ```
    /// use heap_tricks::RemovableHeap;
    /// let heap = RemovableHeap::<i32>::new();
    /// assert!(heap.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    /// ヒープが空なら `true` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// assert!(RemovableHeap::from_iter(Vec::<u32>::new()).is_empty());
    /// assert!(!RemovableHeap::from_iter(vec![42]).is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// ヒープの要素数を返す。
    ///
    /// # 例
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// assert_eq!(RemovableHeap::from_iter(Vec::<u32>::new()).len(), 0);
    /// assert_eq!(RemovableHeap::from_iter(vec![42, 45, 56]).len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// 要素 `x` を挿入する。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// let mut heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// heap.push(48);
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 45, 48, 56]);
    /// ```
    pub fn push(&mut self, x: T) {
        self.len += 1;
        self.heap.push(x);
    }

    /// ヒープに入っている要素 `x` を1つ削除する。$O(\log n)$。
    ///
    /// `x` と等しい要素がヒープに入っていない場合、たとえ直後に同じ要素を
    /// 挿入し直しても、以降のすべての操作の結果が不正になる。
    ///
    /// # 例
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// let mut heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// heap.remove_unchecked(45);
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 56]);
    /// // heap.remove_unchecked(44); のように入っていない要素を指定してはいけない。
    /// ```
    pub fn remove_unchecked(&mut self, x: T) {
        self.len -= 1;
        self.removed.push(x);
        self.settle();
    }

    /// ヒープの最大要素があれば削除して返す。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// let mut heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// assert_eq!(heap.pop(), Some(56));
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 45]);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        let ans = self.heap.pop()?;
        self.len -= 1;
        self.settle();
        Some(ans)
    }

    /// ヒープの最大要素があれば返す。
    ///
    /// # 例
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// let mut heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// assert_eq!(heap.peek(), Some(56));
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 45, 56]);
    /// ```
    pub fn peek(&self) -> Option<T> {
        self.heap.peek().copied()
    }

    /// ヒープの要素を昇順に並べたベクターを構築する。$O(n \log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// let heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 45, 56]);
    /// ```
    pub fn collect_sorted_vec(&self) -> Vec<T> {
        let mut heap = self.heap.clone();
        let mut removed = self.removed.clone();
        let mut ans = Vec::new();
        while let Some(x) = heap.pop() {
            if removed.peek() == Some(&x) {
                removed.pop().unwrap();
            } else {
                ans.push(x);
            }
        }
        ans.reverse();
        ans
    }

    fn settle(&mut self) {
        while !self.heap.is_empty() && self.heap.peek() <= self.removed.peek() {
            self.heap.pop().unwrap();
            self.removed.pop().unwrap();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    #[test]
    fn test_removable_heap() {
        let mut sorted = Vec::new();
        let mut heap = RemovableHeap::new();
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let x = rng.gen_range(0..10);
            match rng.gen_range(0..2) {
                0 => {
                    sorted.push(x);
                    sorted.sort_unstable();
                    heap.push(x);
                }
                1 => {
                    if let Ok(i) = sorted.binary_search(&x) {
                        sorted.remove(i);
                        heap.remove_unchecked(x);
                    }
                }
                _ => unreachable!(),
            }
            assert_eq!(&heap.collect_sorted_vec(), &sorted);
            assert_eq!(heap.len(), sorted.len());
        }
    }

    #[test]
    fn test_median_heap() {
        let mut sorted = Vec::new();
        let mut heap = DoubleHeap::default();
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let x = rng.gen_range(0..10);
            match rng.gen_range(0..2) {
                0 => {
                    sorted.push(x);
                    sorted.sort_unstable();
                    heap.push_front(x);
                }
                1 => {
                    if let Ok(i) = sorted.binary_search(&x) {
                        sorted.remove(i);
                        heap.remove_left_unchecked(x);
                    }
                }
                _ => unreachable!(),
            }
            assert_eq!(&heap.collect_sorted_vec(), &sorted);
            assert_eq!(heap.len(), sorted.len());

            if !sorted.is_empty() {
                let i = rng.gen_range(0..sorted.len());
                let expected = sorted[i];
                heap.balance_left(i);
                assert_eq!(heap.peek_back().unwrap(), expected);
            }
        }
    }
}
