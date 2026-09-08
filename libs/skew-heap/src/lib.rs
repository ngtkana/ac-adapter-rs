//! Meld 可能な二分ヒープ（skew heap）
//!
//! 各ノードは高々 2 つの子を持つ二分木で、親の値が両方の子の値以上というヒープ性質を保つ。
//! 2 つのヒープの合併 `meld` は、値の大きい方を根として残し、その右部分木ともう一方を
//! 再帰的に合併したうえで左右の子を入れ替える。明示的な平衡条件は持たないが、
//! この左右反転により長い経路への合併が繰り返されるのを防ぎ、
//! 償却 $O(\log n)$ の合併を達成する。`push`, `pop` はいずれも `meld` を用いて実装する。
//!
//! # 仕様
//!
//! - 型: `SkewHeap<T>`（`T: Ord`）
//! - 構築: `SkewHeap::new()`（空）, `SkewHeap::singleton(value)`（要素 1 つ）
//! - 合併: `SkewHeap::meld(&mut self, rhs)`、フリー関数 `meld(a, b)`
//! - 挿入: `push(value)`
//! - 参照・取り出し: `peek()` は最大要素への参照、`pop()` は最大要素を取り除いて返す
//! - 変換: `into_sorted_vec()` はすべての要素を昇順に並べた `Vec`
//!
//! 親ポインタを持たないため、`iter`, `len`, `is_empty`, `peek_mut` などは提供しない。
//!
//! # 例
//!
//! ```
//! use skew_heap::SkewHeap;
//!
//! let mut heap = SkewHeap::new();
//! heap.push(3);
//! heap.push(4);
//! heap.push(2);
//! assert_eq!(heap.pop(), Some(4));
//! assert_eq!(heap.peek(), Some(&3));
//! assert_eq!(heap.pop(), Some(3));
//! assert_eq!(heap.pop(), Some(2));
//! assert_eq!(heap.pop(), None);
//! ```
//!
//! # 計算量
//!
//! - `meld`: 償却 $O(\log(n + m))$（$n, m$ は合併前の要素数）
//! - `push`, `pop`: 償却 $O(\log n)$
//! - `peek`: $O(1)$
//! - `into_sorted_vec`: $O(n \log n)$
use std::fmt::DebugList;
use std::fmt::Formatter;
use std::fmt::{self};
use std::iter::Extend;
use std::iter::FromIterator;
use std::iter::IntoIterator;
use std::mem::swap;
use std::mem::take;

/// Meld 可能な二分ヒープ。
///
/// 空、またはヒープ性質を満たす二分木として要素を保持する。
///
/// # 例
///
/// ```
/// use skew_heap::SkewHeap;
///
/// let mut heap = SkewHeap::new();
/// heap.push(1);
/// assert_eq!(heap.peek(), Some(&1));
/// ```
#[derive(Clone, Hash, PartialEq)]
pub struct SkewHeap<T>(Option<Box<SkeyHeapNode<T>>>);
impl<T: Ord> Default for SkewHeap<T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<'a, A: 'a + Copy + Ord> Extend<&'a A> for SkewHeap<A> {
    fn extend<T: IntoIterator<Item = &'a A>>(&mut self, iter: T) {
        iter.into_iter().copied().for_each(|x| self.push(x));
    }
}
impl<A: Ord> Extend<A> for SkewHeap<A> {
    fn extend<T: IntoIterator<Item = A>>(&mut self, iter: T) {
        iter.into_iter().for_each(|x| self.push(x));
    }
}
impl<A: Ord> FromIterator<A> for SkewHeap<A> {
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut heap = Self::new();
        heap.extend(iter);
        heap
    }
}
impl<T: fmt::Debug + Ord> fmt::Debug for SkewHeap<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_list();
        if let Some(heap) = self.0.as_ref() {
            push_entries(heap, &mut f);
        }
        f.finish()
    }
}
impl<T: Ord> SkewHeap<T> {
    /// 空のヒープを構築する。
    pub fn new() -> Self {
        Self(None)
    }

    /// ヒープを空にする。
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// 要素 1 つからなるヒープを構築する。
    pub fn singleton(value: T) -> Self {
        Self(Some(Box::new(SkeyHeapNode::singleton(value))))
    }

    /// 2 つのヒープを合併し、`rhs` の要素をすべて `self` に移す。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log(n + m))$（$n$ は `self`、$m$ は `rhs` の要素数）
    ///
    /// # 例
    ///
    /// ```
    /// use skew_heap::SkewHeap;
    ///
    /// let mut a: SkewHeap<i32> = [1, 3].into_iter().collect();
    /// let b: SkewHeap<i32> = [2, 4].into_iter().collect();
    /// a.meld(b);
    /// assert_eq!(a.into_sorted_vec(), vec![1, 2, 3, 4]);
    /// ```
    pub fn meld(&mut self, rhs: Self) {
        *self = meld(take(self), rhs);
    }

    /// 要素を 1 つ挿入する。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log n)$
    ///
    /// # 例
    ///
    /// ```
    /// use skew_heap::SkewHeap;
    ///
    /// let mut heap = SkewHeap::new();
    /// heap.push(5);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    pub fn push(&mut self, value: T) {
        self.meld(Self::singleton(value));
    }

    /// 最大の要素への参照を返す。空なら `None`。
    ///
    /// # 計算量
    ///
    /// $O(1)$
    pub fn peek(&self) -> Option<&T> {
        self.0.as_ref().map(|heap| &heap.value)
    }

    /// 最大の要素を取り除いて返す。空なら `None`。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log n)$
    ///
    /// # 例
    ///
    /// ```
    /// use skew_heap::SkewHeap;
    ///
    /// let mut heap: SkewHeap<i32> = [1, 3, 2].into_iter().collect();
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(2));
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), None);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        let me = take(self);
        let SkeyHeapNode { left, right, value } = *me.0?;
        *self = Self(meld_node(left, right));
        Some(value)
    }

    /// すべての要素を昇順に並べた `Vec` に変換する。
    ///
    /// # 計算量
    ///
    /// $O(n \log n)$
    ///
    /// # 例
    ///
    /// ```
    /// use skew_heap::SkewHeap;
    ///
    /// let heap: SkewHeap<i32> = [3, 1, 2].into_iter().collect();
    /// assert_eq!(heap.into_sorted_vec(), vec![1, 2, 3]);
    /// ```
    pub fn into_sorted_vec(mut self) -> Vec<T> {
        let mut vec = Vec::new();
        while let Some(x) = self.pop() {
            vec.push(x);
        }
        vec.reverse();
        vec
    }
}
/// 2 つのヒープから、その合併を構築する（[`SkewHeap::meld`] のフリー関数版）。
///
/// # 計算量
///
/// 償却 $O(\log(n + m))$（$n, m$ は合併前の要素数）
///
/// # 例
///
/// ```
/// use skew_heap::meld;
/// use skew_heap::SkewHeap;
///
/// let a: SkewHeap<i32> = [0, 2, 4].into_iter().collect();
/// let b: SkewHeap<i32> = [1, 3].into_iter().collect();
/// let heap = meld(a, b);
/// assert_eq!(heap.into_sorted_vec(), vec![0, 1, 2, 3, 4]);
/// ```
pub fn meld<T: Ord>(a: SkewHeap<T>, b: SkewHeap<T>) -> SkewHeap<T> {
    SkewHeap(meld_node(a.0, b.0))
}

#[derive(Clone, Default, Hash, PartialEq)]
struct SkeyHeapNode<T> {
    left: Option<Box<SkeyHeapNode<T>>>,
    right: Option<Box<SkeyHeapNode<T>>>,
    value: T,
}
impl<T: Ord + fmt::Debug> fmt::Debug for SkeyHeapNode<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut f = f.debug_list();
        push_entries(self, &mut f);
        f.finish()
    }
}
fn push_entries<T: fmt::Debug + Ord>(heap: &SkeyHeapNode<T>, f: &mut DebugList) {
    f.entry(&heap.value);
    if let Some(left) = heap.left.as_deref() {
        push_entries(left, f);
    }
    if let Some(right) = heap.right.as_deref() {
        push_entries(right, f);
    }
}
impl<T: Ord> SkeyHeapNode<T> {
    pub fn singleton(value: T) -> Self {
        Self {
            left: None,
            right: None,
            value,
        }
    }
}
fn meld_node<T: Ord>(
    a: Option<Box<SkeyHeapNode<T>>>,
    b: Option<Box<SkeyHeapNode<T>>>,
) -> Option<Box<SkeyHeapNode<T>>> {
    let [mut a, mut b] = match [a, b] {
        [None, None] => return None,
        [Some(a), None] => return Some(a),
        [None, Some(b)] => return Some(b),
        [Some(a), Some(b)] => [a, b],
    };
    if a.value < b.value {
        swap(&mut a, &mut b);
    }
    a.right = meld_node(a.right, Some(b));
    swap(&mut a.left, &mut a.right);
    Some(a)
}

#[cfg(test)]
mod tests {
    use super::meld;
    use super::SkewHeap;
    use itertools::Itertools;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::BinaryHeap;
    use std::iter::repeat_with;

    #[test]
    fn test_heap() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut binary = BinaryHeap::new();
            let mut skew = SkewHeap::new();
            for _ in 0..1000 {
                match rng.gen_range(0..3) {
                    0 => {
                        // push
                        let x = rng.gen_range(0..10);
                        binary.push(x);
                        skew.push(x);
                    }
                    1 => {
                        // pop
                        let expected = binary.pop();
                        let result = skew.pop();
                        assert_eq!(expected, result);
                    }
                    2 => {
                        // collect
                        let mut expected = binary.iter().copied().collect_vec();
                        let mut result = skew.clone().into_sorted_vec();
                        expected.sort_unstable();
                        result.sort_unstable();
                        assert_eq!(expected, result);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_meld() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(0..10);
            let m = rng.gen_range(0..10);
            let a = repeat_with(|| rng.gen_range(0..20)).take(n).collect_vec();
            let b = repeat_with(|| rng.gen_range(0..20)).take(m).collect_vec();
            let skew_a = a.iter().copied().collect::<SkewHeap<_>>();
            let skew_b = b.iter().copied().collect::<SkewHeap<_>>();
            let mut skew = meld(skew_a, skew_b);
            let mut expected_to_be_sorted = Vec::new();
            while let Some(x) = skew.pop() {
                expected_to_be_sorted.push(x);
            }
            assert!(expected_to_be_sorted.windows(2).all(|v| v[0] >= v[1]));
        }
    }
}
