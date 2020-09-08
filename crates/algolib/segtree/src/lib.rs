#![warn(missing_docs)]

//! セグツリーです。
//!
//! 本体は [`Segtree`] です。
//!
//! # 使い方
//!
//! このように、値を演算のラッパー型で包んで、イテレータから構築します。
//!
//! ```
//! use segtree::*;
//!
//! let mut seg = (0..10).map(|x| Add(x)).collect::<Segtree<_>>();
//! assert_eq!(seg.fold(4..6), Some(Add(9)));
//! assert_eq!(seg.fold(4..4), None);
//! assert_eq!(seg.fold(..), Some(Add(45)));
//!
//! seg.update(4, Add(5));
//! assert_eq!(seg.fold(4..6), Some(Add(10)));
//! ```
//!
//!
//! このように、値を演算のラッパー型を自動で開封してくれるものもあります。
//!
//! ```
//! use segtree::*;
//!
//! let mut seg = (0..10).map(|x| Add(x)).collect::<Segtree<_>>();
//! assert_eq!(seg.fold_inner(4..6), Some(9));
//! ```
//!
//!
//! # 提供しているラッパー型
//!
//! - [`Cat`] : 文字列結合
//! - [`Add`] : 足し算
//! - [`Mul`] : 掛け算
//! - [`Min`] : 最小
//! - [`Max`] : 最大
//! - [`Inversion`] : 転倒数
//! - [`First`] : 第一成分
//! - [`Second`] : 第二成分
//! - [`Affine`] : アフィン（未テスト）
//!
//! # ほしいラッパー型
//!
//! - 行列
//! - 2 ×2 行列
//! - 多項式
//! - 多項式の合成
//! - [`Value`] を実装した型のタプルやベクター
//! - ...
//!
//!
//! # ラッパー型の作り方
//!
//! このように、[`Value`] トレイトを実装した型を定義すると良いです。
//!
//! ```
//! use segtree::*;
//!
//! #[derive(Debug, Clone, PartialEq, Eq)]
//! struct First<T: std::fmt::Debug + Clone>(pub T);
//! impl<T: std::fmt::Debug + Clone> Value for First<T> {
//!     fn op(&self, rhs: &Self) -> Self {
//!         self.clone()
//!     }
//! }
//! ```
//!
//! # 基本的な機能
//!
//! - [`update`] : 更新
//! - [`fold`] : 区間クエリ
//!
//!
//! # その他便利な機能
//!
//! - [`partition_point`] : 二分探索
//! - [`as_slice`] : デバッグにどうぞです。
//!
//! [`Segtree`]: struct.Segtree.html
//! [`Cat`]: struct.Cat.html
//! [`Add`]: struct.Add.html
//! [`Mul`]: struct.Mul.html
//! [`Min`]: struct.Min.html
//! [`Max`]: struct.Max.html
//! [`Inversion`]: struct.Inversion.html
//! [`First`]: struct.First.html
//! [`Second`]: struct.Second.html
//! [`Affine`]: struct.Affine.html
//!
//! [`Value`]: trait.Value.html
//!
//! [`update`]: struct.Segtree.html#method.update
//! [`fold`]: struct.Segtree.html#method.fold
//! [`partition_point`]: struct.Segtree.html#method.partition_point
//! [`as_slice`]: struct.Segtree.html#method.as_slice

pub use traits::{Value, Wrapper};
pub use values::{Add, Affine, Cat, First, Inversion, Max, Min, Mul, Second};

use std::{cmp, iter, ops};

/// 本体です。
///
/// 詳しくはモジュールレベルドキュメントをどうぞです。
///
#[derive(Debug, Clone)]
pub struct Segtree<T>
where
    T: Value,
{
    geta: usize,
    table: Vec<T>,
}

impl<T: Value> Segtree<T> {
    /// 空かどうかです。
    ///
    /// 概念的な配列が空であることと、内部実装が空であることは同値です。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// assert!((0..0).map(|x| Add(x)).collect::<Segtree<_>>().is_empty());
    /// assert!(!(0..1).map(|x| Add(x)).collect::<Segtree<_>>().is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    /// 概念的な配列の長さです。
    ///
    /// 内部実装は、`(2 * len()).saturating_sub(1)` の長さを持ちます。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// assert_eq!(0, (0..0).map(|x| Add(x)).collect::<Segtree<_>>().len());
    /// assert_eq!(1, (0..1).map(|x| Add(x)).collect::<Segtree<_>>().len());
    /// assert_eq!(2, (0..2).map(|x| Add(x)).collect::<Segtree<_>>().len());
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        (self.table.len() + 1) / 2
    }

    /// スライスから変換します。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20)]);
    /// assert_eq!(seg.fold(..), Some(Add(30)));
    /// ```
    pub fn from_slice(src: &[T]) -> Self {
        iter::FromIterator::from_iter(src.iter().cloned())
    }

    /// スライスに変換します。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let a = [Add(10), Add(20)];
    /// assert_eq!(&a, Segtree::from_slice(&a).as_slice());
    /// ```
    pub fn as_slice(&self) -> &[T] {
        &self.table[self.geta..]
    }

    fn update_node_unckecked(&mut self, i: usize) {
        let (left, right) = self.table.split_at_mut(i * 2 + 1);
        left[i] = right[0].op(&right[1]);
    }

    /// 値を変更します。
    ///
    /// 場所 `i` の値が `x` になります。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let mut seg = Segtree::from_slice(&[Add(10), Add(20)]);
    /// seg.update(0, Add(5));
    /// assert_eq!(seg.fold(..), Some(Add(25)));
    /// ```
    pub fn update(&mut self, mut i: usize, x: T) {
        assert!(i <= self.len(), "添字がはみ出していてですね……");
        i += self.len() - 1;
        self.table[i] = x;
        while i != 0 {
            i = (i - 1) / 2;
            self.update_node_unckecked(i);
        }
    }

    /// 値を編集します。
    ///
    /// 場所 `i` の値を編集します。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let mut seg = Segtree::from_slice(&[Add(10), Add(20)]);
    /// seg.modify(0, |Add(ref mut x)| *x = *x + 1);
    /// assert_eq!(seg.fold(..), Some(Add(31)));
    /// ```
    pub fn modify<F>(&mut self, mut i: usize, mut modifier: F)
    where
        F: FnMut(&mut T),
    {
        assert!(i <= self.len(), "添字がはみ出していてですね……");
        i += self.len() - 1;
        modifier(&mut self.table[i]);
        while i != 0 {
            i = (i - 1) / 2;
            self.update_node_unckecked(i);
        }
    }

    /// 畳み込みます。
    ///
    /// 値の [`Value`] トレイトの [`op`] メソッドで畳み込みます。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20)]);
    /// assert_eq!(seg.fold(0..0), None);
    /// assert_eq!(seg.fold(0..1), Some(Add(10)));
    /// assert_eq!(seg.fold(..), Some(Add(30)));
    /// ```
    ///
    /// [`Value`]: trait.Value.html
    /// [`op`]: trait.Value.html#method.op
    pub fn fold(&self, range: impl ops::RangeBounds<usize>) -> Option<T> {
        let mut start = match range.start_bound() {
            ops::Bound::Excluded(&x) => x + 1,
            ops::Bound::Included(&x) => x,
            ops::Bound::Unbounded => 0,
        };
        let mut end = match range.end_bound() {
            ops::Bound::Excluded(&x) => x,
            ops::Bound::Included(&x) => x + 1,
            ops::Bound::Unbounded => self.len(),
        };

        assert!(start <= end, "変な区間を渡すのをやめませんか？");
        assert!(end <= self.len(), "添字がはみ出していてですね……");

        if start == end {
            None
        } else if start + 1 == end {
            Some(self.table[self.geta + start].clone())
        } else {
            start += self.geta;
            end += self.geta;
            let mut left = self.table[start].clone();
            start += 1;
            end -= 1;
            let mut right = self.table[end].clone();

            while start != end {
                if start % 2 == 0 {
                    left.op_assign_from_the_right(&self.table[start]);
                    start += 1;
                }
                if end % 2 == 0 {
                    end -= 1;
                    right.op_assign_from_the_left(&self.table[end]);
                }
                start = (start - 1) / 2;
                end = (end - 1) / 2;
            }

            Some(left.op(&right))
        }
    }

    /// 二分探索をします。
    ///
    /// さて、関数 `f: start..=len() -> bool` を `f(i) = pred(seg.fold(start..=i))`
    /// で定義しましょう。このとき、
    ///
    /// - `start..i` 内の任意の `j` について `f(j)` が `true`
    /// - `i..=seg.len()` 内の任意の `j` について `f(j)` が `false`
    ///
    /// を満たす `i` が `start..=seg.len() + 1` 内にただ一つ存在するとき、それを返します。
    ///
    ///
    /// # 定義上の注意
    ///
    /// 単位元がないという事情を鑑み、`f` の定義は閉区間です。
    ///
    ///
    /// # 未定義
    ///
    /// そのような `i` が存在しないとき（つまり、`pred` によって区分化されていないとき）
    /// の結果は未定義です。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.partition_point(1, |&Add(x)| x <= -500000));
    /// assert_eq!(1, seg.partition_point(1, |&Add(x)| x <= 19));
    /// assert_eq!(2, seg.partition_point(1, |&Add(x)| x <= 20));
    /// assert_eq!(2, seg.partition_point(1, |&Add(x)| x <= 49));
    /// assert_eq!(3, seg.partition_point(1, |&Add(x)| x <= 50));
    /// assert_eq!(3, seg.partition_point(1, |&Add(x)| x <= 500000));
    /// ```
    pub fn partition_point(&self, start: usize, mut pred: impl FnMut(&T) -> bool) -> usize {
        let mut i = self.geta + start;
        if !pred(&self.table[i]) {
            start
        } else if self
            .fold(start..)
            .map(|folded| pred(&folded))
            .unwrap_or(true)
        {
            self.len()
        } else {
            let mut value = self.table[i].clone();
            i += 1;

            loop {
                match i % 2 {
                    0 => {
                        let next_value = value.op(&self.table[i]);
                        if !pred(&next_value) {
                            break;
                        }
                        i += 1;
                        value = next_value;
                    }
                    1 => {
                        i /= 2;
                    }
                    _ => unreachable!(),
                }
            }

            loop {
                let next_value = value.op(&self.table[i]);
                if pred(&next_value) {
                    i += 1;
                    value = next_value;
                }
                let next_i = i * 2 + 1;
                if self.table.len() < next_i {
                    break;
                }
                i = next_i;
            }

            i - self.geta
        }
    }

    /// 二分探索をします。
    ///
    /// さて、関数 `g: 0..end -> bool` を `g(i) = pred(seg.fold(start..=i))`
    /// で定義しましょう。このとき、
    ///
    /// - `i..end` 内の任意の `j` について `g(j)` が `true`
    /// - `0..i` 内の任意の `j` について `g(j)` が `false`
    ///
    /// を満たす `i` が `0..end` 内にただ一つ存在するとき、それを返します。
    ///
    ///
    /// # 定義上の注意
    ///
    /// 単位元がないという事情を鑑み、`g` の定義は閉区間です。
    ///
    ///
    /// # 未定義
    ///
    /// そのような `i` が存在しないとき（つまり、`pred` によって区分化されていないとき）
    /// の結果は未定義です。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(2, seg.reverse_partition_point(2, |&Add(x)| x <= -500000));
    /// assert_eq!(2, seg.reverse_partition_point(2, |&Add(x)| x <= 19));
    /// assert_eq!(1, seg.reverse_partition_point(2, |&Add(x)| x <= 20));
    /// assert_eq!(1, seg.reverse_partition_point(2, |&Add(x)| x <= 29));
    /// assert_eq!(0, seg.reverse_partition_point(2, |&Add(x)| x <= 30));
    /// assert_eq!(0, seg.reverse_partition_point(2, |&Add(x)| x <= 500000));
    /// ```
    pub fn reverse_partition_point(&self, end: usize, mut pred: impl FnMut(&T) -> bool) -> usize {
        let mut i = self.geta + end;
        if end == 0 || !pred(&self.table[i - 1]) {
            end
        } else if self.fold(..end).map(|folded| pred(&folded)).unwrap_or(true) {
            0
        } else {
            i -= 1;
            let mut value = self.table[i].clone();

            while i != 0 {
                match i % 2 {
                    0 => {
                        let next_value = self.table[i - 1].op(&value);
                        if !pred(&next_value) {
                            break;
                        }
                        i -= 1;
                        value = next_value;
                    }
                    1 => {
                        i = (i - 1) / 2;
                    }
                    _ => unreachable!(),
                }
            }

            loop {
                if i != 0 {
                    let next_value = self.table[i - 1].op(&value);
                    if pred(&next_value) {
                        i -= 1;
                        value = next_value;
                    }
                }
                let next_i = i * 2 + 1;
                if self.table.len() < next_i {
                    break;
                }
                i = next_i;
            }

            i - self.geta
        }
    }
}

impl<T> Segtree<T>
where
    T: Value + Wrapper,
{
    /// ラッパーの中身の値を変更します。
    ///
    /// 場所 `i` の値が `Wrapper::from_inner(x)` になります。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let mut seg = Segtree::from_slice(&[Add(10), Add(20)]);
    /// seg.update_inner(0, 5);
    /// assert_eq!(seg.fold(..), Some(Add(25)));
    /// ```
    #[inline]
    pub fn update_inner(&mut self, i: usize, x: T::Inner) {
        self.update(i, T::from_inner(x));
    }

    /// ラッパーの中身の値を編集します。
    ///
    /// 場所 `i` の値を編集します。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let mut seg = Segtree::from_slice(&[Add(10), Add(20)]);
    /// seg.modify_inner(0, |x| *x = *x + 1);
    /// assert_eq!(seg.fold(..), Some(Add(31)));
    /// ```
    #[inline]
    pub fn modify_inner<F>(&mut self, i: usize, mut modifier: F)
    where
        F: FnMut(&mut T::Inner),
    {
        self.modify(i, |x| modifier(x.get_mut()));
    }

    /// 畳み込んでラッパーの中身を取ります。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20)]);
    /// assert_eq!(seg.fold_inner(0..0), None);
    /// assert_eq!(seg.fold_inner(0..1), Some(10));
    /// assert_eq!(seg.fold_inner(..), Some(30));
    /// ```
    ///
    /// [`Value`]: trait.Value.html
    /// [`op`]: trait.Value.html#method.op
    #[inline]
    pub fn fold_inner(&self, range: impl ops::RangeBounds<usize>) -> Option<T::Inner> {
        self.fold(range).map(Wrapper::into_inner)
    }

    /// ラッパー型の中身で二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.partition_point_inner(1, |&x| x <= -500000));
    /// assert_eq!(1, seg.partition_point_inner(1, |&x| x <= 19));
    /// assert_eq!(2, seg.partition_point_inner(1, |&x| x <= 20));
    /// assert_eq!(2, seg.partition_point_inner(1, |&x| x <= 49));
    /// assert_eq!(3, seg.partition_point_inner(1, |&x| x <= 50));
    /// assert_eq!(3, seg.partition_point_inner(1, |&x| x <= 500000));
    /// ```
    #[inline]
    pub fn partition_point_inner(
        &self,
        start: usize,
        mut pred: impl FnMut(&T::Inner) -> bool,
    ) -> usize {
        self.partition_point(start, |x| pred(x.get()))
    }

    /// ラッパー型の中身で逆向きに二分探索をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(2, seg.reverse_partition_point_inner(2, |&x| x <= -500000));
    /// assert_eq!(2, seg.reverse_partition_point_inner(2, |&x| x <= 19));
    /// assert_eq!(1, seg.reverse_partition_point_inner(2, |&x| x <= 20));
    /// assert_eq!(1, seg.reverse_partition_point_inner(2, |&x| x <= 29));
    /// assert_eq!(0, seg.reverse_partition_point_inner(2, |&x| x <= 30));
    /// assert_eq!(0, seg.reverse_partition_point_inner(2, |&x| x <= 500000));
    /// ```
    #[inline]
    pub fn reverse_partition_point_inner(
        &self,
        start: usize,
        mut pred: impl FnMut(&T::Inner) -> bool,
    ) -> usize {
        self.reverse_partition_point(start, |x| pred(x.get()))
    }

    /// ラッパー型の中身で `lower_bound_by` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.lower_bound_inner_by(1, |x| x.cmp(&-500000)));
    /// assert_eq!(1, seg.lower_bound_inner_by(1, |x| x.cmp(&19)));
    /// assert_eq!(1, seg.lower_bound_inner_by(1, |x| x.cmp(&20)));
    /// assert_eq!(2, seg.lower_bound_inner_by(1, |x| x.cmp(&49)));
    /// assert_eq!(2, seg.lower_bound_inner_by(1, |x| x.cmp(&50)));
    /// assert_eq!(3, seg.lower_bound_inner_by(1, |x| x.cmp(&500000)));
    /// ```
    #[inline]
    pub fn lower_bound_inner_by(
        &self,
        start: usize,
        mut cmp: impl FnMut(&T::Inner) -> cmp::Ordering,
    ) -> usize {
        self.partition_point_inner(start, |x| cmp(x) == cmp::Ordering::Less)
    }

    /// ラッパー型の中身で `upper_bound_by` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.upper_bound_inner_by(1, |x| x.cmp(&-500000)));
    /// assert_eq!(1, seg.upper_bound_inner_by(1, |x| x.cmp(&19)));
    /// assert_eq!(2, seg.upper_bound_inner_by(1, |x| x.cmp(&20)));
    /// assert_eq!(2, seg.upper_bound_inner_by(1, |x| x.cmp(&49)));
    /// assert_eq!(3, seg.upper_bound_inner_by(1, |x| x.cmp(&50)));
    /// assert_eq!(3, seg.upper_bound_inner_by(1, |x| x.cmp(&500000)));
    /// ```
    #[inline]
    pub fn upper_bound_inner_by(
        &self,
        start: usize,
        mut cmp: impl FnMut(&T::Inner) -> cmp::Ordering,
    ) -> usize {
        self.partition_point_inner(start, |x| cmp(x) != cmp::Ordering::Greater)
    }

    /// ラッパー型の中身で `lower_bound_by_key` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.lower_bound_inner_by_key(1, &-500000, |&x| x));
    /// assert_eq!(1, seg.lower_bound_inner_by_key(1, &19, |&x| x));
    /// assert_eq!(1, seg.lower_bound_inner_by_key(1, &20, |&x| x));
    /// assert_eq!(2, seg.lower_bound_inner_by_key(1, &49, |&x| x));
    /// assert_eq!(2, seg.lower_bound_inner_by_key(1, &50, |&x| x));
    /// assert_eq!(3, seg.lower_bound_inner_by_key(1, &500000, |&x| x));
    /// ```
    #[inline]
    pub fn lower_bound_inner_by_key<U: Ord>(
        &self,
        start: usize,
        value: &U,
        mut key: impl FnMut(&T::Inner) -> U,
    ) -> usize {
        self.lower_bound_inner_by(start, |x| key(x).cmp(value))
    }

    /// ラッパー型の中身で `upper_bound_by_key` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// use std::convert::identity;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.upper_bound_inner_by_key(1, &-500000, |&x| x));
    /// assert_eq!(1, seg.upper_bound_inner_by_key(1, &19, |&x| x));
    /// assert_eq!(2, seg.upper_bound_inner_by_key(1, &20, |&x| x));
    /// assert_eq!(2, seg.upper_bound_inner_by_key(1, &49, |&x| x));
    /// assert_eq!(3, seg.upper_bound_inner_by_key(1, &50, |&x| x));
    /// assert_eq!(3, seg.upper_bound_inner_by_key(1, &500000, |&x| x));
    /// ```
    #[inline]
    pub fn upper_bound_inner_by_key<U: Ord>(
        &self,
        start: usize,
        value: &U,
        mut key: impl FnMut(&T::Inner) -> U,
    ) -> usize {
        self.upper_bound_inner_by(start, |x| key(x).cmp(value))
    }

    /// 中身の [`Vec`] に変換します。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let a = [Add(10), Add(20)];
    /// assert_eq!(vec![10, 20], Segtree::from_slice(&a).to_vec_inner());
    /// ```
    pub fn to_vec_inner(&self) -> Vec<T::Inner> {
        self.as_slice().iter().cloned().map(T::into_inner).collect()
    }
}

impl<T> Segtree<T>
where
    T: Value + Wrapper,
    T::Inner: Ord,
{
    /// ラッパー型の中身で `lower_bound` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.lower_bound_inner(1, &-500000));
    /// assert_eq!(1, seg.lower_bound_inner(1, &19));
    /// assert_eq!(1, seg.lower_bound_inner(1, &20));
    /// assert_eq!(2, seg.lower_bound_inner(1, &49));
    /// assert_eq!(2, seg.lower_bound_inner(1, &50));
    /// assert_eq!(3, seg.lower_bound_inner(1, &500000));
    /// ```
    #[inline]
    pub fn lower_bound_inner(&self, start: usize, value: &T::Inner) -> usize {
        self.partition_point_inner(start, |x| x < value)
    }

    /// ラッパー型の中身で `upper_bound` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(1, seg.upper_bound_inner(1, &-500000));
    /// assert_eq!(1, seg.upper_bound_inner(1, &19));
    /// assert_eq!(2, seg.upper_bound_inner(1, &20));
    /// assert_eq!(2, seg.upper_bound_inner(1, &49));
    /// assert_eq!(3, seg.upper_bound_inner(1, &50));
    /// assert_eq!(3, seg.upper_bound_inner(1, &500000));
    /// ```
    #[inline]
    pub fn upper_bound_inner(&self, start: usize, value: &T::Inner) -> usize {
        self.partition_point_inner(start, |x| x <= value)
    }

    /// ラッパー型の中身で逆向きに `lower_bound` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(2, seg.reverse_lower_bound_inner(2, &-500000));
    /// assert_eq!(2, seg.reverse_lower_bound_inner(2, &19));
    /// assert_eq!(2, seg.reverse_lower_bound_inner(2, &20));
    /// assert_eq!(1, seg.reverse_lower_bound_inner(2, &29));
    /// assert_eq!(1, seg.reverse_lower_bound_inner(2, &30));
    /// assert_eq!(0, seg.reverse_lower_bound_inner(2, &500000));
    /// ```
    #[inline]
    pub fn reverse_lower_bound_inner(&self, end: usize, value: &T::Inner) -> usize {
        self.reverse_partition_point_inner(end, |x| x < value)
    }

    /// ラッパー型の中身で逆向きに `upper_bound` をします。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    /// let seg = Segtree::from_slice(&[Add(10), Add(20), Add(30)]);
    /// assert_eq!(2, seg.reverse_upper_bound_inner(2, &-500000));
    /// assert_eq!(2, seg.reverse_upper_bound_inner(2, &19));
    /// assert_eq!(1, seg.reverse_upper_bound_inner(2, &20));
    /// assert_eq!(1, seg.reverse_upper_bound_inner(2, &29));
    /// assert_eq!(0, seg.reverse_upper_bound_inner(2, &30));
    /// assert_eq!(0, seg.reverse_upper_bound_inner(2, &500000));
    /// ```
    #[inline]
    pub fn reverse_upper_bound_inner(&self, end: usize, value: &T::Inner) -> usize {
        self.reverse_partition_point_inner(end, |x| x <= value)
    }
}

impl<T: Value> iter::FromIterator<T> for Segtree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Segtree<T> {
        let mut iter = iter.into_iter();
        if let Some(head) = iter.next() {
            let mut table = iter.collect::<Vec<_>>();
            let tmp = table.to_vec();
            table.push(head);
            table.extend(tmp.into_iter());

            let geta = table.len() / 2;

            for i in (0..geta).rev() {
                table[i] = table[2 * i + 1].op(&table[2 * i + 2]);
            }

            if !table.is_empty() {
                let mut i = table.len();
                while i != 0 {
                    i = (i - 1) / 2;
                }
            }

            Self { geta, table }
        } else {
            Self {
                geta: 0,
                table: Vec::new(),
            }
        }
    }
}

impl<T: Value, I: std::slice::SliceIndex<[T]>> std::ops::Index<I> for Segtree<T> {
    type Output = I::Output;

    /// 対応する配列の要素にアクセスです。
    ///
    /// # Examples
    ///
    /// ```
    /// use segtree::*;
    ///
    /// let seg = (0..10).map(|x| Add(x)).collect::<Segtree<_>>();
    /// assert_eq!(seg[4], Add(4));
    /// ```
    ///
    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        std::ops::Index::index(self.as_slice(), index)
    }
}

mod traits {
    /// 演算 [`op`] の入っている型です。
    ///
    /// [`op`]: traits.Value.html#methods.op
    pub trait Value: Clone {
        /// 演算をします。
        fn op(&self, rhs: &Self) -> Self;

        /// 右から演算をします。
        fn op_assign_from_the_right(&mut self, rhs: &Self) {
            *self = self.op(rhs);
        }

        /// 左から演算をします。
        fn op_assign_from_the_left(&mut self, rhs: &Self) {
            *self = rhs.op(self);
        }
    }

    /// ラッパー型です。
    pub trait Wrapper {
        /// [`into_inner`] と [`from_inner`] で使われます。
        ///
        /// [`into_inner`]: traits.Wrapper.html#method.into_inner
        /// [`from_inner`]: traits.Wrapper.html#method.from_inner
        type Inner;

        /// 中身への参照をとります。
        fn get(&self) -> &Self::Inner;

        /// 中身への可変参照をとります。
        fn get_mut(&mut self) -> &mut Self::Inner;

        /// 中身へ変換します。
        fn into_inner(self) -> Self::Inner;

        /// 中身から構築します。
        fn from_inner(src: Self::Inner) -> Self;
    }
}

mod values {
    use super::{Value, Wrapper};
    use std::{cmp, ops};

    macro_rules! impl_wrapper {
        (impl Wrapper for $struct_name:ident {}) => {
            impl<T> Wrapper for $struct_name<T> {
                type Inner = T;

                #[inline]
                fn get(&self) -> &Self::Inner {
                    &self.0
                }
                #[inline]
                fn get_mut(&mut self) -> &mut Self::Inner {
                    &mut self.0
                }
                #[inline]
                fn into_inner(self) -> Self::Inner {
                    self.0
                }
                #[inline]
                fn from_inner(src: Self::Inner) -> Self {
                    Self(src)
                }
            }
        };
    }

    /// 文字列結合
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Cat(pub String);
    impl Value for Cat {
        #[inline]
        fn op(&self, rhs: &Self) -> Self {
            Cat(self.0.chars().chain(rhs.0.chars()).collect())
        }
    }
    impl Wrapper for Cat {
        type Inner = String;

        #[inline]
        fn get(&self) -> &Self::Inner {
            &self.0
        }
        #[inline]
        fn get_mut(&mut self) -> &mut Self::Inner {
            &mut self.0
        }
        #[inline]
        fn into_inner(self) -> Self::Inner {
            self.0
        }
        #[inline]
        fn from_inner(src: Self::Inner) -> Self {
            Self(src)
        }
    }

    /// 足し算
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Add<T>(pub T);
    impl<T> Value for Add<T>
    where
        T: Clone + ops::Add<Output = T>,
    {
        fn op(&self, rhs: &Self) -> Self {
            Add(self.0.clone() + rhs.0.clone())
        }
    }
    impl_wrapper! { impl Wrapper for Add {} }

    /// 掛け算
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Mul<T>(pub T);
    impl<T> Value for Mul<T>
    where
        T: Clone + ops::Mul<Output = T>,
    {
        fn op(&self, rhs: &Self) -> Self {
            Mul(self.0.clone() * rhs.0.clone())
        }
    }
    impl_wrapper! { impl Wrapper for Mul {} }

    /// 最小
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Min<T>(pub T);
    impl<T> Value for Min<T>
    where
        T: Clone + cmp::Ord,
    {
        fn op(&self, rhs: &Self) -> Self {
            Min(self.0.clone().min(rhs.0.clone()))
        }
    }
    impl_wrapper! { impl Wrapper for Min {} }

    /// 最大
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Max<T>(pub T);
    impl<T> Value for Max<T>
    where
        T: Clone + cmp::Ord,
    {
        fn op(&self, rhs: &Self) -> Self {
            Max(self.0.clone().max(rhs.0.clone()))
        }
    }
    impl_wrapper! { impl Wrapper for Max {} }

    /// 転倒数
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Inversion {
        zeros: usize,
        ones: usize,
        inv: usize,
    }
    impl Inversion {
        /// 転倒数を返します。
        pub fn inv(&self) -> usize {
            self.inv
        }
        /// bit ひとつ分のデータであればその bit を返します。
        pub fn try_into_bool(self) -> Option<bool> {
            match self {
                Self {
                    zeros: 1,
                    ones: 0,
                    inv: 0,
                } => Some(false),
                Self {
                    zeros: 0,
                    ones: 1,
                    inv: 0,
                } => Some(true),
                _ => None,
            }
        }
        /// bit 0 に対応するオブジェクトを作ります。
        pub fn zero() -> Self {
            Self {
                zeros: 1,
                ones: 0,
                inv: 0,
            }
        }
        /// bit 1 に対応するオブジェクトを作ります。
        pub fn one() -> Self {
            Self {
                zeros: 0,
                ones: 1,
                inv: 0,
            }
        }
        /// ひとつの bit からオブジェクトを構築します。
        pub fn from_bool(b: bool) -> Self {
            if b {
                Self::one()
            } else {
                Self::zero()
            }
        }
    }
    impl Value for Inversion {
        fn op(&self, rhs: &Self) -> Self {
            let zeros = self.zeros + rhs.zeros;
            let ones = self.ones + rhs.ones;
            let inv = self.inv + rhs.inv + self.ones * rhs.zeros;
            Self { zeros, ones, inv }
        }
    }

    /// 第一成分を返します。
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct First<T>(pub T);
    impl<T: std::fmt::Debug + Clone> Value for First<T> {
        fn op(&self, _rhs: &Self) -> Self {
            self.clone()
        }
    }
    impl_wrapper! { impl Wrapper for First {} }

    /// 第二成分を返します。
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Second<T>(pub T);
    impl<T: std::fmt::Debug + Clone> Value for Second<T> {
        fn op(&self, rhs: &Self) -> Self {
            rhs.clone()
        }
    }
    impl_wrapper! { impl Wrapper for Second {} }

    /// アフィンです。
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Affine<T> {
        a: T,
        b: T,
    }
    impl<T: std::fmt::Debug + Clone> Value for Affine<T>
    where
        T: ops::Add<Output = T> + ops::Mul<Output = T>,
    {
        fn op(&self, rhs: &Self) -> Self {
            let a = self.a.clone() * rhs.a.clone();
            let b = self.b.clone() + self.a.clone() * rhs.b.clone();
            Affine { a, b }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::prelude::*;
    use std::{fmt, iter, marker, mem};

    #[test]
    fn test_add_partition_point_hand() {
        let n = 11;
        let seg = Segtree::from_slice(&vec![Add(1); n]);

        assert_eq!(seg.partition_point_inner(0, |&x| x <= 0), 0);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 1), 1);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 2), 2);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 3), 3);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 4), 4);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 5), 5);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 6), 6);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 7), 7);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 8), 8);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 9), 9);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 10), 10);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 11), 11);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 12), 11);
        assert_eq!(seg.partition_point_inner(0, |&x| x <= 13), 11);

        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 0), 11);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 1), 10);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 2), 9);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 3), 8);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 4), 7);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 5), 6);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 6), 5);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 7), 4);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 8), 3);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 9), 2);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 10), 1);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 11), 0);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 12), 0);
        assert_eq!(seg.reverse_partition_point_inner(11, |&x| x <= 13), 0);
    }

    #[test]
    fn test_add_partition_point_exhaustive() {
        for n in 0..40 {
            let seg = Segtree::from_slice(&vec![Add(1); n]);
            for l in 0..n {
                for d in 0..n + 2 {
                    assert_eq!(seg.partition_point_inner(l, |&x| x <= d), (l + d).min(n));
                    assert_eq!(
                        seg.reverse_partition_point_inner(l, |&x| x <= d),
                        l.saturating_sub(d)
                    );
                }
            }
        }
    }

    #[test]
    fn test_cat_hand() {
        let a = ('0'..='9')
            .map(|c| Cat(iter::once(c).collect::<String>()))
            .collect::<Vec<_>>();
        let mut seg = Segtree::from_slice(&a);

        assert_eq!(seg.as_slice(), a.as_slice());
        assert_eq!(seg.fold_inner(3..5), Some("34".to_owned()));
        assert_eq!(seg.fold_inner(2..9), Some("2345678".to_owned()));
        assert_eq!(seg.fold_inner(0..4), Some("0123".to_owned()));
        assert_eq!(seg.fold_inner(8..8), None);

        seg.update_inner(3, "d".to_owned());
        seg.update_inner(6, "g".to_owned());
    }

    const NUMBER_OF_TEST_CASES: usize = 20;
    const NUMBER_OF_QUERIES: usize = 50;

    #[derive(Debug)]
    struct Test<T, F, G> {
        rng: rand::rngs::StdRng,
        gen: F,
        gen_large: G,
        marker: marker::PhantomData<T>,
    }

    impl<T, F, G> Test<T, F, G>
    where
        T: Value + Wrapper,
        T::Inner: fmt::Debug + cmp::PartialEq + Clone,
        F: Fn(&mut rand::rngs::StdRng) -> T::Inner,
        G: Fn(&mut rand::rngs::StdRng) -> T::Inner,
    {
        pub fn new(seed: u64, gen: F, gen_large: G) -> Self {
            Self {
                rng: rand::SeedableRng::seed_from_u64(seed),
                gen,
                gen_large: gen_large,
                marker: marker::PhantomData::<T>,
            }
        }

        pub fn run(&mut self, spec: Spec) {
            let n = self.rng.gen_range(16, 32);
            let a = iter::repeat_with(|| (self.gen)(&mut self.rng))
                .take(n)
                .collect::<Vec<_>>();
            let seg = a.iter().cloned().map(T::from_inner).collect::<Segtree<_>>();
            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);
            let mut instance = Instance { a, seg };

            for _ in 0..NUMBER_OF_QUERIES {
                match spec.what(self.rng.gen_range(0, spec.sum())) {
                    TestNames::UpdateInner => {
                        let i = self.rng.gen_range(0, n);
                        let x = (self.gen)(&mut self.rng);
                        instance.test_update_inner(i, x);
                    }
                    TestNames::FoldInner => {
                        let range = gen_valid_range(&mut self.rng, n);
                        instance.test_fold_inner(range);
                    }
                    TestNames::LowerBoundInner => panic!(),
                    TestNames::ReverseLowerBoundInner => panic!(),
                }
            }
        }

        pub fn run_ord(&mut self, spec: Spec)
        where
            T::Inner: Ord,
        {
            let n = self.rng.gen_range(16, 32);
            let a = iter::repeat_with(|| (self.gen)(&mut self.rng))
                .take(n)
                .collect::<Vec<_>>();
            let seg = a.iter().cloned().map(T::from_inner).collect::<Segtree<_>>();
            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);
            let mut instance = Instance { a, seg };

            for _ in 0..NUMBER_OF_QUERIES {
                match spec.what(self.rng.gen_range(0, spec.sum())) {
                    TestNames::UpdateInner => {
                        let i = self.rng.gen_range(0, n);
                        let x = (self.gen)(&mut self.rng);
                        instance.test_update_inner(i, x);
                    }
                    TestNames::FoldInner => {
                        let range = gen_valid_range(&mut self.rng, n);
                        instance.test_fold_inner(range);
                    }
                    TestNames::LowerBoundInner => {
                        let start = self.rng.gen_range(0, n);
                        let value = (self.gen_large)(&mut self.rng);
                        instance.test_lower_bound_inner(start, value);
                    }
                    TestNames::ReverseLowerBoundInner => {
                        let end = self.rng.gen_range(1, n + 1);
                        let value = (self.gen_large)(&mut self.rng);
                        instance.test_reverse_lower_bound_inner(end, value);
                    }
                }
            }
        }
    }

    #[derive(Debug)]
    struct Instance<T>
    where
        T: Value + Wrapper,
    {
        a: Vec<T::Inner>,
        seg: Segtree<T>,
    }

    impl<T> Instance<T>
    where
        T: Value + Wrapper,
        T::Inner: fmt::Debug + Clone + cmp::PartialEq,
    {
        pub fn test_update_inner(&mut self, i: usize, x: T::Inner) {
            self.a[i] = x.clone();
            self.seg.update_inner(i, x.clone());

            println!(
                "\tUpdate (i = {}, x = {:?}) -> a = {:?}",
                i,
                &x,
                self.a.iter().collect::<Vec<_>>()
            );
        }

        pub fn test_fold_inner(&self, range: ops::Range<usize>) {
            let expected = self.a[range.clone()]
                .iter()
                .cloned()
                .map(T::from_inner)
                .fold(None, |acc: Option<T>, x| {
                    Some(if let Some(acc) = acc {
                        acc.op(&x)
                    } else {
                        x.clone()
                    })
                })
                .map(T::into_inner);
            let result = self.seg.fold_inner(range.clone());
            println!(
                "\tFold {:?}, expected = {:?}, result = {:?}",
                &range, expected, result
            );
            assert_eq!(&expected, &result);
        }

        pub fn test_lower_bound_inner(&self, start: usize, value: T::Inner)
        where
            T::Inner: Ord,
        {
            use span::Span;

            let a = self.a[start..]
                .iter()
                .cloned()
                .map(T::from_inner)
                .collect::<Vec<_>>();
            let mut v = vec![a[0].clone()];
            for x in a.iter().skip(1).cloned() {
                let x = v.last().unwrap().op(&x);
                v.push(x);
            }
            let a = v.iter().cloned().map(T::into_inner).collect::<Vec<_>>();

            let expected = start + a.lower_bound(&value);
            let result = self.seg.lower_bound_inner(start, &value);

            println!(
                "\tLower bound (start = {}, value = {:?}) -> (expected = {}, result = {}, fold_inner(start..result) = {:?})",
                start, value, expected, result, self.seg.fold_inner(start..result)
            );
            assert_eq!(expected, result);
        }

        pub fn test_reverse_lower_bound_inner(&self, end: usize, value: T::Inner)
        where
            T::Inner: Ord,
        {
            use span::Span;

            let a = self.a[..end]
                .iter()
                .rev()
                .cloned()
                .map(T::from_inner)
                .collect::<Vec<_>>();
            let mut v = vec![a[0].clone()];
            for x in a.iter().skip(1).cloned() {
                let x = v.last().unwrap().op(&x);
                v.push(x);
            }
            let a = v.iter().cloned().map(T::into_inner).collect::<Vec<_>>();

            let expected = end - a.lower_bound(&value);
            let result = self.seg.reverse_lower_bound_inner(end, &value);

            println!(
                "\tReverse lower bound (start = {}, value = {:?}) -> (expected = {}, result = {}, fold_inner(start..result) = {:?})",
                end, value, expected, result, self.seg.fold_inner(result..end)
            );
            assert_eq!(expected, result);
        }
    }

    #[derive(Debug, Clone)]
    enum TestNames {
        UpdateInner,
        FoldInner,
        LowerBoundInner,
        ReverseLowerBoundInner,
    }

    #[derive(Debug, Clone)]
    struct Spec {
        update_inner: u32,
        fold_inner: u32,
        lower_bound_inner: u32,
        reverse_lower_bound_inner: u32,
    }
    impl Spec {
        fn sum(&self) -> u32 {
            self.update_inner
                + self.fold_inner
                + self.lower_bound_inner
                + self.reverse_lower_bound_inner
        }
        fn what(&self, x: u32) -> TestNames {
            assert!(x < self.sum());
            if x < self.update_inner {
                TestNames::UpdateInner
            } else if x < self.update_inner + self.fold_inner {
                TestNames::FoldInner
            } else if x < self.update_inner + self.fold_inner + self.lower_bound_inner {
                TestNames::LowerBoundInner
            } else {
                TestNames::ReverseLowerBoundInner
            }
        }
    }

    #[test]
    fn test_cat_random() {
        let mut test = Test::<Cat, _, _>::new(
            42,
            |rng| rng.sample(rand::distributions::Alphanumeric).to_string(),
            |rng| rng.sample(rand::distributions::Alphanumeric).to_string(),
        );

        for _ in 0..NUMBER_OF_TEST_CASES {
            test.run(Spec {
                update_inner: 100,
                fold_inner: 20,
                lower_bound_inner: 0,
                reverse_lower_bound_inner: 0,
            });
        }
    }

    #[test]
    fn test_add_random() {
        let mut test = Test::<Add<u32>, _, _>::new(
            42,
            |rng| rng.gen_range(0, 100),
            |rng| rng.gen_range(0, 3000),
        );

        for _ in 0..NUMBER_OF_TEST_CASES {
            test.run_ord(Spec {
                update_inner: 100,
                fold_inner: 20,
                lower_bound_inner: 20,
                reverse_lower_bound_inner: 20,
            });
        }
    }

    #[test]
    fn test_mul_random() {
        let mut test = Test::<Mul<u128>, _, _>::new(
            42,
            |rng| rng.gen_range(1, 5),
            |rng| rng.gen_range(1, 100000),
        );

        for _ in 0..NUMBER_OF_TEST_CASES {
            test.run_ord(Spec {
                update_inner: 100,
                fold_inner: 20,
                lower_bound_inner: 20,
                reverse_lower_bound_inner: 20,
            });
        }
    }

    #[test]
    fn test_min_random() {
        let mut test = Test::<Min<i32>, _, _>::new(
            42,
            |rng| rng.gen_range(-99, 100),
            |rng| rng.gen_range(-99, 100),
        );

        for _ in 0..NUMBER_OF_TEST_CASES {
            test.run_ord(Spec {
                update_inner: 100,
                fold_inner: 20,
                lower_bound_inner: 0,
                reverse_lower_bound_inner: 0,
            });
        }
    }

    #[test]
    fn test_max_random() {
        let mut test = Test::<Max<i32>, _, _>::new(
            42,
            |rng| rng.gen_range(-99, 100),
            |rng| rng.gen_range(-99, 100),
        );

        for _ in 0..NUMBER_OF_TEST_CASES {
            test.run_ord(Spec {
                update_inner: 100,
                fold_inner: 20,
                lower_bound_inner: 20,
                reverse_lower_bound_inner: 20,
            });
        }
    }

    #[test]
    fn test_inversion_random() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(32, 64);
            let mut a = iter::repeat_with(|| rng.gen_ratio(1, 2))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a
                .iter()
                .copied()
                .map(Inversion::from_bool)
                .collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=84 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.gen_ratio(1, 2);

                        a[i] = x;
                        seg.update(i, Inversion::from_bool(x));

                        println!(
                            "\tSet (i = {}, x = {}) -> a = {:?}",
                            i,
                            x,
                            a.iter()
                                .map(|&b| if b { '1' } else { '0' })
                                .collect::<String>()
                        );
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let mut expected = 0;
                        let mut ones = 0;
                        for &x in &a[range.clone()] {
                            match x {
                                false => {
                                    expected += ones;
                                }
                                true => {
                                    ones += 1;
                                }
                            }
                        }

                        let result = seg.fold(range.clone()).map(|x| x.inv()).unwrap_or(0);
                        println!(
                            "\tFold (a[range] = {:?}) -> (expected = {:?}, result = {:?})",
                            a[range]
                                .iter()
                                .map(|&b| if b { '1' } else { '0' })
                                .collect::<String>(),
                            expected,
                            result
                        );
                        assert_eq!(&expected, &result);
                    }
                    _ => unreachable!(),
                }
            }
            println!();
        }
    }

    #[test]
    fn test_first_random() {
        let mut test = Test::<First<i32>, _, _>::new(
            42,
            |rng| rng.gen_range(-99, 100),
            |rng| rng.gen_range(-99, 100),
        );

        for _ in 0..NUMBER_OF_TEST_CASES {
            test.run_ord(Spec {
                update_inner: 100,
                fold_inner: 20,
                lower_bound_inner: 0,
                reverse_lower_bound_inner: 0,
            });
        }
    }

    #[test]
    fn test_second_random() {
        let mut test = Test::<First<i32>, _, _>::new(
            42,
            |rng| rng.gen_range(-99, 100),
            |rng| rng.gen_range(-99, 100),
        );

        for _ in 0..NUMBER_OF_TEST_CASES {
            test.run_ord(Spec {
                update_inner: 100,
                fold_inner: 20,
                lower_bound_inner: 0,
                reverse_lower_bound_inner: 0,
            });
        }
    }

    fn gen_valid_range(rng: &mut impl rand::Rng, len: usize) -> ops::Range<usize> {
        let mut u = rng.gen_range(0, len);
        let mut v = rng.gen_range(0, len);
        if u > v {
            mem::swap(&mut u, &mut v);
        }
        v += 1;
        u..v
    }
}
