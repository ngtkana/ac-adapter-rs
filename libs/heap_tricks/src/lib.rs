//! [`remove_unchecked`](RemovableHeap::remove_unchecked) のできるヒープです。
//!
//! 本体は [`RemovableHeap`] です。
//!
//! # ⚠️ 注意点
//!
//! [`RemovableHeap`] は、ヒープに入っていない要素を削除すると
//! **たとえその要素をすぐに挿入し直したとしても、
//! その後の挙動がすべて未定義になります。**
//!
//! # パフォーマンスに関する実験
//!
//! ## 実験１: 中央値取得で両方に入れる実装
//!
//! 下記「yukicoder No.738 - 平らな農地」に次の変更を入れたものです。
//! 35 ms だったものが 53 ms に悪化します。
//! 実行時間制限が厳し目なときにはやめたほうが良いかもです。
//!
//! 提出 (53 ms): <https://yukicoder.me/submissions/727802>
//!
//! ```diff
//! 14,19c14,16
//! <     for (i, &x) in a.iter().enumerate().take(k) {
//! <         if i % 2 == 0 {
//! <             heap.push_right(x);
//! <         } else {
//! <             heap.push_left(x);
//! <         }
//! ---
//! >     for &x in &a[..k] {
//! >         heap.push_right(x);
//! >         heap.push_left(x);
//! 30a28,29
//! >         heap.push_left(a[j]);
//! >         heap.remove_left_unchecked(a[i]);
//! 33c32
//! <     println!("{}", ans)
//! ---
//! >     println!("{}", ans / 2)
//! ```
//!
//!
//! # このライブラリを使える問題
//!
//! 固定された数列の順位を答えるだけなら、ウェーブレット行列
//! のほうが楽という説はあります。
//!
//! - JAG Practice Contest for ACM-ICPC Asia Regional 2016 C - We Don't Wanna Work!
//!   - 問題: <https://atcoder.jp/contests/jag2016autumn/tasks/icpc2016autumn_c>
//!   - 提出: TODO
//!   - 出題日: 2016-09-04
//!   - 難易度: 易しめ。
//!   - 制約: N + Q ≤ 70,000
//!   - コメント: キーに [`Copy`] を課しているので [`String`] がくるとかなり
//!   めんどくさいことに！！ むーん……
//!   - 使う構造体: [`DoubleHeap`] （左右移動の明示的追跡あり）
//! - yukicoder No.649 - ここでちょっとQK！
//!   - 問題: <https://yukicoder.me/problems/no/649>
//!   - 提出 (262 ms): <https://yukicoder.me/submissions/727871>
//!   - 出題日: 2018-02-09
//!   - 難易度: 易しめ。
//!   - 制約: N, Q ≤ 200,000
//!   - コメント: 中央削除があります。
//!   - 使う構造体: [`DoubleHeap`] (削除は中央のみです。）
//! - yukicoder No.738 - 平らな農地
//!   - 問題: <https://yukicoder.me/problems/no/738>
//!   - 提出 (35 ms): <https://yukicoder.me/submissions/727798>
//!   - 出題日: 2018-09-28
//!   - 難易度: 易しめ。
//!   - 制約: N, Q ≤ 100,000
//!   - コメント: 固定個数中央値は、両方に入れると楽です。
//!   - 使う構造体: [`DoubleHeap`] (削除も使います。)
//! - ABC 127 F -  Absolute Minima
//!   - 問題: <https://atcoder.jp/contests/abc127/tasks/abc127_f>
//!   - 提出 (211 ms): <https://atcoder.jp/contests/abc127/submissions/28290935>
//!   - 出題日: 2019-05-25
//!   - 難易度: 易しめ。`heap_slope_trick` クレートがあるので
//!   そちらを使ったほうが楽です。
//!   - 制約: Q ≤ 200,000
//!   - 使う構造体: [`DoubleHeap`] （`heap_slope_trick` クレートを使ったほうがよいです。)
//! - ABC 128 E - Roadwork
//!   - 問題: <https://atcoder.jp/contests/abc128/tasks/abc128_e>
//!   - 提出 (156 ms): <https://atcoder.jp/contests/abc128/submissions/28294898>
//!   - 出題日: 2019-05-26
//!   - 難易度: 易しめ。
//!   - 制約: N ≤ 200,000
//!   - 使う構造体: [`RemovableHeap`]
//! - yukicoder No.919 - You Are A Project Manager
//!   - 問題: <https://yukicoder.me/problems/no/919>
//!   - 提出: TODO
//!   - 出題日: 2019-10-25
//!   - 難易度: そこそこ
//!   - 制約: N ≤ 100,000
//!   - 使う構造体: [`DoubleHeap`]
//!   - 難易度: Mo 書かないといけないので先延ばしに……
//!   ウェーブレット行列で解く問題を Mo で無理やりクエリ
//!   先読みしているイメージですかね。
//! - ABC 170 E - Smart Infants
//!   - 問題: <https://atcoder.jp/contests/abc170/tasks/abc170_e>
//!   - 提出 (163 ms): <https://atcoder.jp/contests/abc170/submissions/28296739>
//!   - 出題日: 2020-06-14
//!   - 難易度: そこそこ。
//!   - 制約: N ≤ 200,000
//!   - 使う構造体: [`RemovableHeap`]
//!   - 他の解法:
//!     - C++ の `std::multiset` (488 ms): <https://atcoder.jp/contests/abc170/submissions/14328933>
//!     - AVL 木 (2477 ms): <https://atcoder.jp/contests/abc170/submissions/24165251>
//!   - コメント: これフルクラッチで書くとけっこう混乱するので、
//!   ライブラリがるとかなり助かります。
//! - OUPC 2020 D - 仲良しスライム
//!   - 問題: <https://onlinejudge.u-aizu.ac.jp/beta/room.html#OUPC2020/problems/D>
//!   - 提出 (90 ms): <https://onlinejudge.u-aizu.ac.jp/beta/review.html#OUPC2020/6171242>
//!   - 出題日: 2020-12-12
//!   - 難易度: 簡単。
//!   - 制約: N ≤ 100,000
//!   - 使う構造体: [`DoubleHeap`]
//!   - 他の解法:
//!     - ウェーブレット行列 (440 ms): <https://onlinejudge.u-aizu.ac.jp/beta/review.html#OUPC2020/6171281>
//!   - コメント: A:B 重み付き中央値クエリ。平衡基準を抽象化して良かった〜〜
//!   これもウェーブレット行列のほうが思いつきやすそうですが、
//!   ウェーブレット行列ライブラリの累積和系の機能が使いづらい（あの！？）ので、
//!   実装は [`DoubleHeap`] を使うほうが楽です。
//! - ABC 213 G - Game on Tree 2
//!   - 問題: <https://atcoder.jp/contests/abc218/tasks/abc218_g>
//!   - 提出 (115 ms): <https://atcoder.jp/contests/abc218/submissions/28295770>
//!   - 出題日: 2021-09-11
//!   - 難易度: そこそこ。
//!   - 制約: N ≤ 100,000
//!   - 使う構造体: [`DoubleHeap`] (削除も使います。)
//!   - コメント: 本番二分探索を考えてうまく行かず、
//!   後日 [`std::collections::BTreeMap`] で multiset もどきを作って
//!   なんとか通して (181 ms) いました。ヒープ４本の方が速くてきれいで嬉しいですね。
//! - yukicoder No.1786 - Maximum Suffix Median (Online)
//!   - 問題: <https://yukicoder.me/problems/no/1786>
//!   - 提出 TODO
//!   - 出題日: 2021-12-01
//!   - 難易度: 解けていません。
//!   - 制約: N ≤ 200,000
//!   - 使う構造体: [`DoubleHeap`] （らしいです。)
//!   - コメント: むーん

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::AddAssign;
use std::ops::SubAssign;

/// 集約操作を指定するためのトレイトです。
/// 単なるマーカートレイトではなく、集約結果を管理するための
/// オブジェクトとして使用されます
///
/// [`Nop`] か [`Sum`] を使っておけばだいたい大丈夫ですが、
/// 必要なら自分で定義することができます。
pub trait Handler<T> {
    /// 左側に挿入するときのコールバック関数
    fn push_left(&mut self, value: T);
    /// 左側から削除するときのコールバック関数
    fn pop_left(&mut self, value: T);
    /// 右側に挿入するときのコールバック関数
    fn push_right(&mut self, value: T);
    /// 右側から削除するときのコールバック関数
    fn pop_right(&mut self, value: T);
}
/// 何も集約しないことを表す型です。
/// [`Handler`] の一種です。
/// [`DoubleHeap::new()`] で構築すると自動的に採用されます。
/// Unit-like struct なので、同名の定数が自動定義されています。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, Copy)]
pub struct Nop;
impl<T> Handler<T> for Nop {
    fn push_left(&mut self, _value: T) {}

    fn pop_left(&mut self, _value: T) {}

    fn push_right(&mut self, _value: T) {}

    fn pop_right(&mut self, _value: T) {}
}
/// 総和を集約するための型です。
/// [`Handler`] の一種です。
/// [`Sum::default()`] でデフォルト構築できます。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, Copy)]
pub struct Sum<T> {
    pub left: T,
    pub right: T,
}
impl<T> Handler<T> for Sum<T>
where
    T: AddAssign<T> + SubAssign<T>,
{
    fn push_left(&mut self, value: T) { self.left += value; }

    fn pop_left(&mut self, value: T) { self.left -= value; }

    fn push_right(&mut self, value: T) { self.right += value; }

    fn pop_right(&mut self, value: T) { self.right -= value; }
}

/// ヒープを４本使って中央値などを管理するデータ構造です。
/// [`Handler`] が必要ないときには [`DoubleHeap::new()`] で構築すると
/// 勝手に [`Nop`] が採用されます。
#[derive(Clone)]
pub struct DoubleHeap<T, H> {
    left: RemovableHeap<T>,
    right: RemovableHeap<Reverse<T>>,
    handler: H,
}
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
    pub fn new() -> Self { Self::default() }
}
impl<T, H> DoubleHeap<T, H>
where
    T: Copy + Ord + Hash,
    H: Handler<T>,
{
    /// [`Handler`] を指定して構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// assert_eq!(heap.collect_sorted_vec(), vec![42]);
    /// ```
    pub fn with_handler(handler: H) -> Self {
        Self {
            left: RemovableHeap::default(),
            right: RemovableHeap::default(),
            handler,
        }
    }

    /// ヒープが空ならば `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert_eq!(heap.is_empty(), true);
    /// heap.push_left(42);
    /// assert_eq!(heap.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool { self.left.is_empty() && self.right.is_empty() }

    /// 全体の要素数を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert_eq!(heap.len(), 0);
    /// heap.push_left(42);
    /// assert_eq!(heap.len(), 1);
    /// ```
    pub fn len(&self) -> usize { self.left.len() + self.right.len() }

    /// 左側ヒープの要素数を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert_eq!(heap.left_len(), 0);
    /// heap.push_left(42);
    /// heap.push_right(42);
    /// heap.push_right(42);
    /// assert_eq!(heap.left_len(), 1);
    /// ```
    pub fn left_len(&self) -> usize { self.left.len() }

    /// 右側ヒープの要素数を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// assert_eq!(heap.right_len(), 0);
    /// heap.push_left(42);
    /// heap.push_right(42);
    /// heap.push_right(42);
    /// assert_eq!(heap.right_len(), 2);
    /// ```
    pub fn right_len(&self) -> usize { self.right.len() }

    /// 左側ヒープの要素数が１増加するように、要素を挿入します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    ///
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn push_left(&mut self, elm: T) {
        self.handler.push_left(elm);
        self.left.push(elm);
        self.settle();
    }

    /// 右側ヒープの要素数が１増加するように、要素を挿入します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    ///
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn push_right(&mut self, elm: T) {
        self.handler.push_right(elm);
        self.right.push(Reverse(elm));
        self.settle();
    }

    /// 左側ヒープの最大要素があれば返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// assert_eq!(heap.peek_left(), Some(13));
    /// ```
    pub fn peek_left(&self) -> Option<T> { self.left.peek() }

    /// 右側ヒープの最大要素があれば返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// assert_eq!(heap.peek_left(), Some(13));
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn peek_right(&self) -> Option<T> { self.right.peek().map(|rev| rev.0) }

    /// 左側ヒープの最大要素があれば削除して返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// assert_eq!(heap.pop_left(), Some(13));
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![42, 45]);
    /// ```
    pub fn pop_left(&mut self) -> Option<T> {
        let ans = self.left.pop();
        self.settle();
        ans
    }

    /// 右側ヒープの最大要素があれば削除して返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// assert_eq!(heap.pop_right(), Some(42));
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![45]);
    /// ```
    pub fn pop_right(&mut self) -> Option<T> {
        let ans = self.right.pop().map(|rev| rev.0);
        self.settle();
        ans
    }

    /// 左側ヒープの要素数が１増加するように、右側ヒープから要素を移動します
    ///
    /// # Panics
    ///
    /// 右側ヒープが空のとき。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// heap.move_left();
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13, 42]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![45]);
    /// ```
    pub fn move_left(&mut self) {
        let elm = self.right.pop().expect("右側ヒープは空です。").0;
        self.handler.pop_right(elm);
        self.handler.push_left(elm);
        self.left.push(elm);
        self.settle();
    }

    /// 右側ヒープの要素数が１増加するように、左側ヒープから要素を移動します
    ///
    /// # Panics
    ///
    /// 左側ヒープが空のとき。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// heap.move_right();
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![13, 42, 45]);
    /// ```
    pub fn move_right(&mut self) {
        let elm = self.left.pop().expect("左側ヒープは空です。");
        self.handler.pop_left(elm);
        self.handler.push_right(elm);
        self.right.push(Reverse(elm));
        self.settle();
    }

    /// ヒープに入っている要素を１つ指定して、左側ヒープの要素数が
    /// １減少するように削除します。
    ///
    /// # ⚠️  Undefined Behavior
    ///
    /// 指定された要素がヒープに入っていないとき、
    /// 以降の挙動すべてが未定義になります。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// heap.remove_left_unchecked(42);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![13, 45]);
    /// ```
    pub fn remove_left_unchecked(&mut self, elm: T) {
        if self.left.peek().map_or(false, |lmax| elm <= lmax) {
            self.handler.pop_left(elm);
            self.left.remove_unchecked(elm);
            self.settle();
        } else {
            self.handler.pop_right(elm);
            self.right.remove_unchecked(Reverse(elm));
            self.settle();
            self.move_right();
        }
    }

    /// ヒープに入っている要素を１つ指定して、右側ヒープの要素数が
    /// １減少するように削除します。
    ///
    /// # ⚠️  Undefined Behavior
    ///
    /// 指定された要素がヒープに入っていないとき、
    /// 以降の挙動すべてが未定義になります。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(42);
    /// heap.push_right(45);
    /// heap.push_right(13);
    /// heap.remove_right_unchecked(42);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![13]);
    /// assert_eq!(heap.collect_right_sorted_vec(), vec![45]);
    /// ```
    pub fn remove_right_unchecked(&mut self, elm: T) {
        if self.left.peek().map_or(false, |lmax| elm <= lmax) {
            self.handler.pop_left(elm);
            self.left.remove_unchecked(elm);
            self.settle();
            self.move_left();
        } else {
            self.handler.pop_right(elm);
            self.right.remove_unchecked(Reverse(elm));
            self.settle();
        }
    }

    /// 左側ヒープの要素が `k` 個になるように動かします。
    ///
    /// # Panics
    ///
    /// `k` が総要素数よりも大きいとき。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(10);
    /// heap.push_left(11);
    /// heap.push_left(12);
    /// heap.push_right(13);
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
            self.move_left()
        }
        while self.left_len() > k {
            self.move_right()
        }
    }

    /// 右側ヒープの要素が `k` 個になるように動かします。
    ///
    /// # Panics
    ///
    /// `k` が総要素数よりも大きいとき。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(10);
    /// heap.push_left(11);
    /// heap.push_left(12);
    /// heap.push_right(13);
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
            self.move_right()
        }
        while self.right_len() > k {
            self.move_left()
        }
    }

    /// ハンドラへの参照を返します。
    ///
    /// # Panics
    ///
    /// `k` が総要素数よりも大きいとき。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// use heap_tricks::Sum;
    /// let mut heap = DoubleHeap::with_handler(Sum::default());
    /// heap.push_left(10);
    /// heap.push_left(11);
    /// heap.push_left(12);
    /// heap.push_right(13);
    /// assert_eq!(heap.handler().left, 33);
    /// assert_eq!(heap.handler().right, 13);
    ///
    /// heap.balance_left(1);
    /// assert_eq!(heap.handler().left, 10);
    /// assert_eq!(heap.handler().right, 36);
    /// ```
    pub fn handler(&self) -> &H { &self.handler }

    /// 左側ヒープの要素を昇順に格納したベクターを構築して返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(10);
    /// heap.push_left(11);
    /// heap.push_left(12);
    /// heap.push_right(13);
    /// assert_eq!(heap.collect_left_sorted_vec(), vec![10, 11, 12]);
    /// ```
    pub fn collect_left_sorted_vec(&self) -> Vec<T> { self.left.collect_sorted_vec() }

    /// 右側ヒープの要素を昇順に格納したベクターを構築して返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(10);
    /// heap.push_left(11);
    /// heap.push_left(12);
    /// heap.push_right(13);
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

    /// すべての要素を昇順に格納したベクターを構築して返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::DoubleHeap;
    /// let mut heap = DoubleHeap::new();
    /// heap.push_left(10);
    /// heap.push_left(11);
    /// heap.push_left(12);
    /// heap.push_right(13);
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
            self.handler.pop_right(elm);
            self.handler.push_left(elm);
            self.left.push(elm);
            let elm = self.left.pop().unwrap();
            self.handler.pop_left(elm);
            self.handler.push_right(elm);
            self.right.push(Reverse(elm));
        }
    }
}

/// 論理削除のできるヒープです。
///
/// # ⚠️  注意点
///
/// ヒープに入っていない要素を削除すると
/// **たとえその要素をすぐに挿入し直したとしても、
/// その後の挙動がすべて未定義になります。**
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
    /// 空のヒープを構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// use heap_tricks::RemovableHeap;
    /// let heap = RemovableHeap::<()>::new();
    /// assert_eq!(heap.collect_sorted_vec(), Vec::new());
    /// ```
    pub fn new() -> Self { Self::default() }

    /// ヒープが空ならば `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// assert_eq!(RemovableHeap::from_iter(Vec::<u32>::new()).is_empty(), true);
    /// assert_eq!(RemovableHeap::from_iter(vec![42]).is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// ヒープの長さを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// assert_eq!(RemovableHeap::from_iter(Vec::<u32>::new()).len(), 0);
    /// assert_eq!(RemovableHeap::from_iter(vec![42, 45, 56]).len(), 3);
    /// ```
    pub fn len(&self) -> usize { self.len }

    /// ヒープに新しい要素 `x` を追加します。
    ///
    /// # Examples
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

    /// ヒープに含まれる要素 `x` を削除します。
    /// ただし、ヒープに含まれない要素を指定した場合、このメソッドの呼び出し
    /// 及びその後の挙動は全て未定義になります。
    ///
    /// # Examples
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// let mut heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// heap.remove_unchecked(45);
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 56]);
    /// // heap.remove_unchecked(44); やってはいけません。
    /// ```
    pub fn remove_unchecked(&mut self, x: T) {
        self.len -= 1;
        self.removed.push(x);
        self.settle();
    }

    /// ヒープの最大要素が存在すれば、削除して返します。
    ///
    /// # Examples
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

    /// ヒープの最大要素が存在すれば、返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use heap_tricks::RemovableHeap;
    /// # use std::iter::FromIterator;
    /// let mut heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// assert_eq!(heap.peek(), Some(56));
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 45, 56]);
    /// ```
    pub fn peek(&self) -> Option<T> { self.heap.peek().copied() }

    /// ヒープの要素を昇順に格納したベクターを構築します。
    ///
    /// # Examples
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
                    heap.push_left(x);
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
                assert_eq!(heap.peek_right().unwrap(), expected);
            }
        }
    }
}
