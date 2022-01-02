//! [`remove_unchecked`](RemovableHeap::remove_unchecked) のできるヒープです。
//!
//! 本体は [`RemovableHeap`] です。
//!
//! # 注意点
//!
//! ヒープに入っていない要素で [`remove_unchecked`](RemovableHeap::remove_unchecked)
//! を呼び出すと、内部状態が壊れ、その後あらゆる挙動が未定義になります。
//! ヒープに入っているかどうかを知りたいときには、別途 [`std::collections::HashMap`]
//! を併用するなどしてください。
//!
//! # このライブラリを使える問題
//!
//! - Yukicoder No.738 - 平らな農地
//!   - 問題: <https://yukicoder.me/problems/no/738>
//!   - 提出 (38 ms): <https://yukicoder.me/submissions/727771>
//!   - 難易度: ほぼ貼るだけ
//!   - 制約: N, Q ≤ 100,000
//!   - コメント: 固定個数中央値は、最初の時点で右、左、右、左と入れるか、
//!   入れ終わったときに [`balance`](MedianHeap::balance) を呼ぶかがよいです。
//!

use std::{
    cmp::{Ordering, Reverse},
    collections::BinaryHeap,
    fmt::Debug,
    hash::Hash,
    iter::FromIterator,
};

pub trait Handler<T> {
    fn push_left(&mut self, value: T);
    fn pop_left(&mut self, value: T);
    fn push_right(&mut self, value: T);
    fn pop_right(&mut self, value: T);
}
struct Nop;
impl<T> Handler<T> for Nop {
    fn push_left(&mut self, _value: T) {}
    fn pop_left(&mut self, _value: T) {}
    fn push_right(&mut self, _value: T) {}
    fn pop_right(&mut self, _value: T) {}
}

#[derive(Clone)]
pub struct MedianHeap<T, H> {
    left: RemovableHeap<T>,
    right: RemovableHeap<Reverse<T>>,
    handler: H,
}
impl<T, H> Debug for MedianHeap<T, H>
where
    T: Copy + Ord + Hash + Debug,
    H: Handler<T>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MedianHeap")
            .field("left", &self.left)
            .field(
                "right",
                &self
                    .right
                    .collect_sorted_vec()
                    .into_iter()
                    .rev()
                    .map(|rev| rev.0)
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}
impl<T> Default for MedianHeap<T, Nop>
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
impl<T> MedianHeap<T, Nop>
where
    T: Copy + Ord + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }
}
impl<T, H> MedianHeap<T, H>
where
    T: Copy + Ord + Hash,
    H: Handler<T>,
{
    pub fn with_handler(handler: H) -> Self {
        Self {
            left: RemovableHeap::default(),
            right: RemovableHeap::default(),
            handler,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.left.is_empty() && self.right.is_empty()
    }
    pub fn len(&self) -> usize {
        self.left.len() + self.right.len()
    }
    pub fn left_len(&self) -> usize {
        self.left.len()
    }
    pub fn right_len(&self) -> usize {
        self.right.len()
    }
    pub fn push_left(&mut self, elm: T) {
        self.handler.push_left(elm);
        self.left.push(elm);
        self.settle();
    }
    pub fn push_right(&mut self, elm: T) {
        self.handler.push_right(elm);
        self.right.push(Reverse(elm));
        self.settle();
    }
    pub fn peek_left(&self) -> Option<T> {
        self.left.peek()
    }
    pub fn peek_right(&self) -> Option<T> {
        self.right.peek().map(|rev| rev.0)
    }
    pub fn pop_left(&mut self) -> Option<T> {
        let ans = self.left.pop();
        self.settle();
        ans
    }
    pub fn pop_right(&mut self) -> Option<T> {
        let ans = self.right.pop().map(|rev| rev.0);
        self.settle();
        ans
    }
    pub fn move_left(&mut self) {
        let elm = self.right.pop().unwrap().0;
        self.handler.pop_right(elm);
        self.handler.push_left(elm);
        self.left.push(elm);
        self.settle();
    }
    pub fn move_right(&mut self) {
        let elm = self.left.pop().unwrap();
        self.handler.pop_left(elm);
        self.handler.push_right(elm);
        self.right.push(Reverse(elm));
        self.settle();
    }
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
    pub fn remove_right_unchecked(&mut self, elm: T) {
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
    pub fn balance(&mut self, mut f: impl FnMut(usize, usize) -> Ordering) {
        loop {
            match f(self.left_len(), self.right_len()) {
                Ordering::Less => self.move_left(),
                Ordering::Equal => break,
                Ordering::Greater => self.move_right(),
            }
        }
    }
    pub fn handler(&self) -> &H {
        &self.handler
    }
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

/// 本体です。
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
    /// use removable_heap::RemovableHeap;
    /// let heap = RemovableHeap::<()>::new();
    /// assert_eq!(heap.collect_sorted_vec(), Vec::new());
    /// ```
    pub fn new() -> Self {
        Self::default()
    }
    /// ヒープが空ならば `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use removable_heap::RemovableHeap;
    /// assert_eq!(RemovableHeap::from_iter(Vec::<u32>::new()).is_empty(), true);
    /// assert_eq!(RemovableHeap::from_iter(vec![42]).is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// ヒープの長さを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// use removable_heap::RemovableHeap;
    /// assert_eq!(RemovableHeap::from_iter(Vec::<u32>::new()).len(), 0);
    /// assert_eq!(RemovableHeap::from_iter(vec![42, 45, 56]).len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }
    /// ヒープに新しい要素 `x` を追加します。
    ///
    /// # Examples
    ///
    /// ```
    /// use removable_heap::RemovableHeap;
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
    /// use removable_heap::RemovableHeap;
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
    /// use removable_heap::RemovableHeap;
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
    /// use removable_heap::RemovableHeap;
    /// let mut heap = RemovableHeap::from_iter(vec![42, 45, 56]);
    /// assert_eq!(heap.peek(), Some(56));
    /// assert_eq!(heap.collect_sorted_vec().as_slice(), &[42, 45, 56]);
    /// ```
    pub fn peek(&self) -> Option<T> {
        self.heap.peek().copied()
    }
    /// ヒープの要素を昇順に格納したベクターを構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// use removable_heap::RemovableHeap;
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
    use rand::{prelude::StdRng, Rng, SeedableRng};

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
        let mut heap = MedianHeap::default();
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
            dbg!(&heap, &sorted);
            assert_eq!(&heap.collect_sorted_vec(), &sorted);
            assert_eq!(heap.len(), sorted.len());

            if !sorted.is_empty() {
                let i = rng.gen_range(0..sorted.len());
                let expected = sorted[i];
                heap.balance(|l, _r| l.cmp(&i));
                assert_eq!(heap.peek_right().unwrap(), expected);
            }
            dbg!(&heap, &sorted);
        }
    }
}
