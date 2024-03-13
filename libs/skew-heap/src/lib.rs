//! Meld のできるヒープ
//!
//! # 使い方
//!
//! ## ヒープ
//!
//! ```
//! use skew_heap::meld;
//! use skew_heap::SkewHeap;
//!
//! let mut heap = SkewHeap::new(); // new で構築
//! heap.push(3); // push で挿入
//! heap.push(4);
//! heap.push(2);
//!
//! assert_eq!(heap.pop(), Some(4)); // pop で最大がでてきます。
//!
//! assert_eq!(heap.peek(), Some(&3)); // peek で次が見られます。
//! assert_eq!(heap.pop(), Some(3));
//! assert_eq!(heap.pop(), Some(2));
//! assert_eq!(heap.pop(), None);
//! ```
//!
//!
//! ## Meld
//!
//! ```
//! use skew_heap::meld;
//! use skew_heap::SkewHeap;
//!
//! // フリー関数 `meld` を使う方法
//! let heap_a = [0, 2, 4, 6].iter().copied().collect::<SkewHeap<_>>();
//! let heap_b = [1, 3, 5, 7].iter().copied().collect::<SkewHeap<_>>();
//! let mut heap = meld(heap_a, heap_b);
//! assert_eq!(heap.into_sorted_vec(), vec![0, 1, 2, 3, 4, 5, 6, 7]);
//!
//! // メソッド `SkewHeap::meld` を使う方法
//! let mut heap_a = [0, 2, 4, 6].iter().copied().collect::<SkewHeap<_>>();
//! let mut heap_b = [1, 3, 5, 7].iter().copied().collect::<SkewHeap<_>>();
//! heap_a.meld(heap_b);
//! assert_eq!(heap_a.into_sorted_vec(), vec![0, 1, 2, 3, 4, 5, 6, 7]);
//! ```
//!
//! # ありそうでないもの
//!
//! * `iter()`, `into_iter()`, `into_iter_sorted()`, `drain()`, `drain_sorted()`: 親ポインタないので面倒です。
//! * `len(), is_empty()`: 長さ保持するの面倒です。
//! * `peek_mut()`: 再挿入面倒です。
use std::fmt::DebugList;
use std::fmt::Formatter;
use std::fmt::{self};
use std::iter::Extend;
use std::iter::FromIterator;
use std::iter::IntoIterator;
use std::mem::swap;
use std::mem::take;

/// Meld のできるヒープ
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
    /// 新しく構築します。
    pub fn new() -> Self {
        Self(None)
    }

    /// 中身を殻にします。
    pub fn clear(&mut self) {
        *self = Self::new();
    }

    /// 要素一つからなる `SkewHeap` を構築します。
    pub fn singleton(value: T) -> Self {
        Self(Some(Box::new(SkeyHeapNode::singleton(value))))
    }

    /// 2 つの `SkewHeap` から、その合併を構築します。
    ///
    /// # 計算量
    ///
    /// O ( lg ( self.len(), rhs.len() ) )
    ///
    /// ただし `SkewHeap::len` メソッドはありません。（あの！？）
    pub fn meld(&mut self, rhs: Self) {
        *self = meld(take(self), rhs);
    }

    /// 要素を一つ、追加します。
    pub fn push(&mut self, value: T) {
        self.meld(Self::singleton(value));
    }

    /// 含んでいる最大の要素への参照を返します。
    pub fn peek(&self) -> Option<&T> {
        self.0.as_ref().map(|heap| &heap.value)
    }

    /// 含んでいる最大の要素を取り除き、それを返します。
    pub fn pop(&mut self) -> Option<T> {
        let me = take(self);
        let SkeyHeapNode { left, right, value } = *me.0?;
        *self = Self(meld_node(left, right));
        Some(value)
    }

    /// ソート済みの `Vec` に変換します。
    pub fn into_sorted_vec(mut self) -> Vec<T> {
        let mut vec = Vec::new();
        while let Some(x) = self.pop() {
            vec.push(x);
        }
        vec.reverse();
        vec
    }
}
/// 2 つの `SkewHeap` から、その合併を構築します。
///
/// # 計算量
///
/// O ( lg ( self.len(), rhs.len() ) )
///
/// ただし `SkewHeap::len` メソッドはありません。（あの！？）
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
