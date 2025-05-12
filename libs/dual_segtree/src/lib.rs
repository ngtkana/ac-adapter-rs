//! 双対セグメント木（右作用）
//!
//! 作用の方向迷うのですが、右作用にしました。
//!
//!
//! # Examples
//!
//! ```
//! # use dual_segtree::{DualSegtree, Ops};
//! // 演算定義（historical minimum）
//! enum O {}
//! impl Ops for O {
//!     type Value = [i32; 2];
//!
//!     fn op([a, b]: [i32; 2], [c, d]: [i32; 2]) -> [i32; 2] {
//!         [a.min(b + c), b + d]
//!     }
//!
//!     fn identity() -> [i32; 2] {
//!         [0, 0]
//!     }
//! }
//!
//! // 構築
//! let mut seg = DualSegtree::<O>::new(vec![[0, 0], [0, 0]]);
//! assert_eq!(seg.collect_vec(), vec![[0, 0], [0, 0]]);
//!
//! // 更新
//! seg.apply(0..1, &[-2, -2]); // -2
//! assert_eq!(seg.collect_vec(), vec![[-2, -2], [0, 0]]);
//! seg.apply(0..1, &[0, 3]); // +3
//! assert_eq!(seg.collect_vec(), vec![[-2, 1], [0, 0]]);
//! ```
use std::collections::VecDeque;
use std::fmt::Debug;
use std::iter::repeat_with;
use std::iter::FromIterator;
use std::mem::replace;
use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;

/// 双対セグメント木（右作用）
#[derive(Clone, Default, PartialEq)]
pub struct DualSegtree<O: Ops> {
    table: Vec<O::Value>,
}
/// 演算（右作用）
pub trait Ops {
    /// 値型
    type Value: Clone + Debug;
    /// 作用する演算（右作用）
    fn op(lhs: Self::Value, rhs: Self::Value) -> Self::Value;
    /// [`op`](Self::op) の単位元
    fn identity() -> Self::Value;
    /// `lhs` を `op(lhs, rhs)` で置き換えます。
    fn op_assign_from_right(lhs: &mut Self::Value, rhs: Self::Value) {
        *lhs = Self::op(lhs.clone(), rhs);
    }
}
impl<O: Ops> DualSegtree<O> {
    /// [`ExactSizeIterator`] から作ります。
    pub fn new<
        T: IntoIterator<IntoIter = I, Item = O::Value>,
        I: ExactSizeIterator<Item = O::Value>,
    >(
        iter: T,
    ) -> Self {
        let iter = iter.into_iter();
        Self {
            table: repeat_with(O::identity)
                .take(iter.len())
                .chain(iter)
                .collect::<Vec<_>>(),
        }
    }

    /// 空なら `true` を返します。
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    /// 管理している配列の長さを返します。
    pub fn len(&self) -> usize {
        self.table.len() / 2
    }

    /// `range` に `x` を作用させます。（右作用）
    pub fn apply(&mut self, range: impl RangeBounds<usize>, x: &O::Value) {
        let Range { mut start, mut end } = into_slice_range(self.len(), range);
        if end < start {
            dual_segtree_index_order_fail(start, end);
        }
        if self.len() < end {
            dual_segtree_end_index_len_fail(end, self.len());
        }
        start += self.len();
        end += self.len();
        self.thrust(start);
        self.thrust(end);
        while start != end {
            if start % 2 == 1 {
                O::op_assign_from_right(&mut self.table[start], x.clone());
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                O::op_assign_from_right(&mut self.table[end], x.clone());
            }
            start /= 2;
            end /= 2;
        }
    }

    /// `i` 番目の要素への可変参照を返します。
    pub fn get_mut(&mut self, i: usize) -> &mut O::Value {
        if self.len() <= i {
            dual_segtree_index_out_of_range_fail(i, self.len())
        }
        let i = self.len() + i;
        (1..=self.lg()).rev().for_each(|p| self.push(i >> p));
        &mut self.table[i]
    }

    /// `i` 番目の要素への参照を返します。
    pub fn get(&mut self, i: usize) -> &O::Value {
        self.get_mut(i)
    }

    /// `i` 番目の要素をコピーして返します。
    pub fn get_copied(&mut self, i: usize) -> O::Value
    where
        O::Value: Copy,
    {
        *self.get_mut(i)
    }

    /// `i` 番目の要素をクローンして返します。
    pub fn get_cloned(&mut self, i: usize) -> O::Value
    where
        O::Value: Clone,
    {
        self.get_mut(i).clone()
    }

    /// [`Vec`] に変換します。
    pub fn collect_vec(&mut self) -> Vec<O::Value> {
        update_all::<O>(&mut self.table);
        self.table[self.len()..].to_vec()
    }

    /// [`Vec`] に変換します。
    pub fn into_vec(mut self) -> Vec<O::Value> {
        update_all::<O>(&mut self.table);
        self.table[self.len()..].to_vec()
    }

    fn lg(&self) -> u32 {
        self.len().next_power_of_two().trailing_zeros()
    }

    fn thrust(&mut self, i: usize) {
        (1..=self.lg())
            .rev()
            .filter(|&p| (i >> p) << p != i)
            .for_each(|p| self.push(i >> p));
    }

    fn push(&mut self, i: usize) {
        let x = replace(&mut self.table[i], O::identity());
        self.table[2 * i..2 * i + 2]
            .iter_mut()
            .for_each(|y| O::op_assign_from_right(y, x.clone()));
    }

    fn silent_collect(&self) -> Vec<O::Value> {
        let mut res = self.table.clone();
        update_all::<O>(&mut res);
        res[self.len()..].to_vec()
    }
}
fn update_all<O: Ops>(a: &mut [O::Value]) {
    (0..a.len() / 2).for_each(|i| {
        let x = replace(&mut a[i], O::identity());
        a[2 * i..2 * i + 2]
            .iter_mut()
            .for_each(|y| O::op_assign_from_right(y, x.clone()));
    });
}
// フォーマット
impl<O: Ops> Debug for DualSegtree<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.silent_collect().fmt(f)
    }
}
////////////////////////////////////////////////////////////////////////////////
// プライベート - RangeBounds 関連
////////////////////////////////////////////////////////////////////////////////
#[allow(clippy::redundant_closure)]
fn into_slice_range(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start
            .checked_add(1)
            .unwrap_or_else(|| slice_start_index_overflow_fail()),
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end
            .checked_add(1)
            .unwrap_or_else(|| slice_end_index_overflow_fail()),
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };
    start..end
}

fn dual_segtree_index_out_of_range_fail(index: usize, len: usize) -> ! {
    panic!("index {index} out of range for dual segtree of length {len}");
}
fn dual_segtree_end_index_len_fail(index: usize, len: usize) -> ! {
    panic!("range end index {index} out of range for dual segtree of length {len}");
}
fn dual_segtree_index_order_fail(start: usize, end: usize) -> ! {
    panic!("dual segtree index starts at {start} but ends at {end}");
}
fn slice_start_index_overflow_fail() -> ! {
    panic!("attempted to index slice from after maximum usize");
}
fn slice_end_index_overflow_fail() -> ! {
    panic!("attempted to index slice up to maximum usize");
}

////////////////////////////////////////////////////////////////////////////////
// 変換
////////////////////////////////////////////////////////////////////////////////
impl<O: Ops> From<Vec<O::Value>> for DualSegtree<O> {
    fn from(v: Vec<O::Value>) -> Self {
        Self::new(v)
    }
}
impl<O: Ops> FromIterator<O::Value> for DualSegtree<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let v = iter.into_iter().collect::<VecDeque<_>>();
        Self {
            table: repeat_with(O::identity).take(v.len()).chain(v).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::DualSegtree;
    use super::Ops;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter::repeat_with;
    use std::mem::swap;
    use std::ops::Range;

    #[derive(Clone, Debug, Default, Hash, PartialEq)]
    struct Brute<O: Ops> {
        table: Vec<O::Value>,
    }
    impl<O: Ops> Brute<O> {
        fn new<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
            Self {
                table: iter.into_iter().collect::<Vec<_>>(),
            }
        }

        pub fn apply(&mut self, range: Range<usize>, x: &O::Value) {
            self.table[range]
                .iter_mut()
                .for_each(|y| O::op_assign_from_right(y, x.clone()));
        }

        pub fn get_cloned(&self, i: usize) -> O::Value
        where
            O::Value: Clone,
        {
            self.table[i].clone()
        }
    }

    #[test]
    fn test_dual_segtree() {
        enum O {}
        impl Ops for O {
            type Value = String;

            fn op(lhs: Self::Value, rhs: Self::Value) -> Self::Value {
                lhs.chars().chain(rhs.chars()).collect::<String>()
            }

            fn identity() -> Self::Value {
                String::new()
            }
        }
        let mut rng = StdRng::seed_from_u64(42);
        let new_value = |rng: &mut StdRng| rng.gen_range('a'..='z').to_string();
        for _ in 0..200 {
            let n = rng.gen_range(1..=50);
            let vec = repeat_with(|| new_value(&mut rng))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = DualSegtree::<O>::new(vec.iter().cloned());
            let mut brute = Brute::<O>::new(vec.iter().cloned());
            for _ in 0..20 {
                match rng.gen_range(0..3) {
                    0 | 1 => {
                        let mut l = rng.gen_range(0..n);
                        let mut r = rng.gen_range(0..n);
                        if l > r {
                            swap(&mut l, &mut r);
                            r += 1;
                        }
                        let x = new_value(&mut rng);
                        seg.apply(l..r, &x);
                        brute.apply(l..r, &x);
                    }
                    2 => {
                        let i = rng.gen_range(0..n);
                        let result = seg.get_cloned(i);
                        let expected = brute.get_cloned(i);
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
                assert_eq!(seg.silent_collect(), brute.table);
            }
        }
    }
}
