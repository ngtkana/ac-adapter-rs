//! SWAG をします。
//!
//! # 基本的な使い方
//!
//! 構造体 [`Swag`] を構築して、メソッド [`fold`](Swag::fold) を呼んでいきましょう。与える配列は `Borrow<[T]>`
//! を実装していればよいです。
//!
//! # Tips
//!
//! * [`fold`](Swag::fold) の戻り値は `Option` です。`unwrap_`
//! 系のメソッドと組み合わせるには、[`fold_or`](Swag::fold_or),
//! [`fold_or_else`](Swag::fold_or_else) を使いましょう。
//!
//! * [`fold`](Swag::fold) は `self` の内部状態を書き換えるので `mut self` メソッドです。
//!
//! # Examples
//!
//! ```
//! use {swag::Swag, std::ops::Add};
//!
//! // Vec 版
//! let _swag = Swag::new(vec![0, 1, 2], Add::add);
//!
//! // スライス版
//! let a = vec![0, 1, 2];
//! let mut swag = Swag::new(a.as_slice(), Add::add);
//!
//! // 畳み込み
//! assert_eq!(swag.fold(..), Some(3));
//! ```
use std::{
    borrow::Borrow,
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
    ops::{Bound, Range, RangeBounds},
};

/// SWAG をします。
///
/// # 計算量
///
/// 長さ N の配列を管理しているとし、`fold` を Q 回呼ぶとき、Θ( N + Q ) です。
///
#[derive(Clone, Default, Hash, PartialEq, Eq)]
pub struct Swag<T, V, F> {
    v: V,
    folder: F,
    stack: Vec<T>,
    center: usize,
    end: usize,
    accum: Option<T>,
    _marker: PhantomData<fn(T) -> T>,
}
impl<T, V, F> Debug for Swag<T, V, F>
where
    T: Copy + Debug,
    V: Borrow<[T]>,
    F: Fn(T, T) -> T,
{
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        w.debug_struct("Swag")
            .field("v", &self.v.borrow())
            .field("stack", &self.stack)
            .field("center", &self.center)
            .field("end", &self.end)
            .field("accum", &self.accum)
            .finish()
    }
}
impl<T, V, F> Swag<T, V, F>
where
    T: Copy,
    V: Borrow<[T]>,
    F: Fn(T, T) -> T,
{
    /// 新しい `Swag` を構築します。
    ///
    /// # 引数
    ///
    /// * `v` は走査する配列です。`Vec` やスライスなど、`Borrow<[T]>` を実装した型ならばよいです。
    /// * `folder` は畳み込む演算です。結合的であればよいです。
    ///
    /// # Examples
    ///
    /// ```
    /// use {swag::Swag, std::ops::Add};
    ///
    /// // Vec 版
    /// let _swag = Swag::new(vec![0, 1, 2], Add::add);
    ///
    /// // スライス版
    /// let a = vec![0, 1, 2];
    /// let _swag = Swag::new(a.as_slice(), Add::add);
    /// ```
    pub fn new(v: V, folder: F) -> Self {
        Self {
            v,
            folder,
            stack: Vec::new(),
            center: 0,
            end: 0,
            accum: None,
            _marker: PhantomData,
        }
    }
    /// 与えられた区間における aggregation を返します。
    ///
    ///
    /// # 要件
    ///
    /// 始点・終点ともに、現在の内部状態よりも小さくなく、スライスのサイズより大きくないこと
    ///
    ///
    /// # 戻り値
    ///
    /// `range` が開区間 [l, r[ に対応するとき、 f { v_i: l <= i < r } を返します。
    ///
    pub fn fold(&mut self, range: impl RangeBounds<usize>) -> Option<T> {
        let Range { start, end } = open(range, self.v.borrow().len());
        self.advance_end(end);
        self.advance_start(start);
        self.current_fold()
    }
    /// [`fold`](Swag::fold) + `unwrap_or`
    pub fn fold_or(&mut self, range: impl RangeBounds<usize>, default: T) -> T {
        self.fold(range).unwrap_or(default)
    }
    /// [`fold`](Swag::fold) + `unwrap_or_else`
    pub fn fold_or_else(&mut self, range: impl RangeBounds<usize>, f: impl FnOnce() -> T) -> T {
        self.fold(range).unwrap_or_else(f)
    }
    /// 現在の内部状態の始点を返します。
    pub fn start(&self) -> usize {
        self.center - self.stack.len()
    }
    /// 現在の内部状態の終点を返します。
    pub fn end(&self) -> usize {
        self.end
    }
    /// 現在の内部状態の始点・終点を `start..end` の形で返します。
    pub fn current_index_range(&self) -> Range<usize> {
        self.start()..self.end()
    }
    /// 現在の内部状態の window をスライスの形で返します。
    pub fn current_window(&self) -> &[T] {
        &self.v.borrow()[self.current_index_range()]
    }
    /// 現在の内部状態の window における aggregation を返します。
    pub fn current_fold(&self) -> Option<T> {
        match (self.stack.last(), self.accum) {
            (None, None) => None,
            (Some(&x), None) => Some(x),
            (None, Some(y)) => Some(y),
            (Some(&x), Some(y)) => Some((self.folder)(x, y)),
        }
    }
    fn advance_start(&mut self, start: usize) {
        debug_assert!(
            start <= self.v.borrow().len(),
            "Out of range: start = {}, len = {}",
            start,
            self.v.borrow().len()
        );
        debug_assert!(
            start <= self.end,
            "Start will exceed end: start = {}, self.end = {}",
            start,
            self.end,
        );
        debug_assert!(
            self.start() <= start,
            "Non-monotone advance_start: self.start = {}, start = {}",
            self.start(),
            start,
        );
        if let Some(d) = self.stack.len().checked_sub(start - self.start()) {
            self.stack.truncate(d);
        } else {
            self.accum = None;
            self.stack.clear();
            self.center = self.end;
            self.stack = self.v.borrow()[start..self.end]
                .iter()
                .copied()
                .rev()
                .collect::<Vec<_>>();
            if !self.stack.is_empty() {
                for i in 0..self.stack.len() - 1 {
                    let x = (self.folder)(self.stack[i + 1], self.stack[i]);
                    self.stack[i + 1] = x;
                }
            }
        }
    }
    fn advance_end(&mut self, end: usize) {
        debug_assert!(
            end <= self.v.borrow().len(),
            "Out of range: end = {}, len = {}",
            end,
            self.v.borrow().len()
        );
        debug_assert!(
            self.end <= end,
            "Non-monotone advance_start: self.end = {}, end = {}",
            self.end,
            end,
        );
        let mut iter = self
            .accum
            .iter()
            .chain(self.v.borrow()[self.end..end].iter())
            .copied();
        self.accum = iter.next().map(|first| iter.fold(first, &self.folder));
        self.end = end;
    }
}
fn open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
    use Bound::{Excluded, Included, Unbounded};
    let start = match range.start_bound() {
        Unbounded => 0,
        Included(&x) => x,
        Excluded(&x) => x - 1,
    };
    let end = match range.end_bound() {
        Excluded(&x) => x,
        Included(&x) => x + 1,
        Unbounded => len,
    };
    start..end
}

#[cfg(test)]
mod tests {
    use {super::Swag, itertools::Itertools, std::ops::Add};

    #[test]
    fn test_vec() {
        let a = vec![0, 1, 2, 3, 4];
        let mut swag = Swag::new(a, Add::add);
        swag.advance_end(3);
        swag.advance_start(1);
        println!("swag = {:?}", &swag);
        assert_eq!(swag.current_index_range(), 1..3);
        assert_eq!(swag.current_window(), &[1, 2]);
        assert_eq!(swag.current_fold(), Some(3));
    }
    #[test]
    fn test_slice() {
        let a = vec![0, 1, 2, 3, 4];
        let mut swag = Swag::new(a.as_slice(), Add::add);
        swag.advance_end(3);
        swag.advance_start(1);
        assert_eq!(swag.current_index_range(), 1..3);
        assert_eq!(swag.current_window(), &[1, 2]);
        assert_eq!(swag.current_fold(), Some(3));
    }
    #[test]
    fn test_call_methods() {
        let mut swag = Swag::new(vec![0, 1, 2, 3, 4], Add::add);
        assert_eq!(swag.fold(0..0), None);
        assert_eq!(swag.fold_or(0..0, 42), 42);
        assert_eq!(swag.fold_or_else(0..0, || 42), 42);
    }
    #[test]
    fn test_algo_hand() {
        let mut swag = Swag::new((0..10).map(|i| (i, 1)).collect_vec(), |(x, d), (y, e)| {
            (10_u32.pow(e) * x + y, d + e)
        });
        assert_eq!(swag.fold(1..3), Some((12, 2)));
        assert_eq!(swag.fold(4..4), None);
        assert_eq!(swag.fold(4..7), Some((456, 3)));
        assert_eq!(swag.fold(5..8), Some((567, 3)));
        assert_eq!(swag.fold(6..9), Some((678, 3)));
        assert_eq!(swag.fold(7..10), Some((789, 3)));
        assert_eq!(swag.fold(9..10), Some((9, 1)));
    }
}
