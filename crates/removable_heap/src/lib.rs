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
//!   - 提出 (33 ms): <https://yukicoder.me/submissions/727723>
//!   - 解法: メディアンで切って、[`RemovableHeap`] ２本とそれぞれの要素総和を管理します。
//!     メディアン版ライブラリにしたいですが、きれいな方法が思いつかず……
//!   - 制約: N, Q ≤ 100,000
//!

use std::{collections::BinaryHeap, fmt::Debug, hash::Hash, iter::FromIterator};

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
}
