#![warn(missing_docs)]

//! 任意始点双方向二分探索機能付き非再帰セグメントツリーです。
//!
//! え、[`Segtree`] さんにこちらを参照してくださいと言われて来たですって！？ 困りましたね……
//!
//! [`Segtree`]: struct.Segtree.html

use std::{iter, ops};
use type_traits::*;

/// セグツリー本体です。
///
/// 詳しくは[モジュールレベルドキュメント](index.html)までです。
#[derive(Debug, Clone, PartialEq)]
pub struct Segtree<T> {
    len: usize,
    table: Vec<T>,
}

impl<T: Assoc, I: std::slice::SliceIndex<[T]>> std::ops::Index<I> for Segtree<T> {
    type Output = I::Output;
    fn index(&self, index: I) -> &Self::Output {
        std::ops::Index::index(self.as_slice(), index)
    }
}

impl<T: Assoc> iter::FromIterator<T> for Segtree<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Segtree<T> {
        let mut table = iter.into_iter().collect::<Vec<_>>();
        let okawari = table.to_vec();
        table.extend(okawari.into_iter());
        let len = table.len() / 2;
        for i in (0..len).rev() {
            table[i] = table[2 * i].clone().op(table[2 * i + 1].clone());
        }
        Self { len, table }
    }
}

impl<T: Assoc> Segtree<T> {
    /// 中身をクローンして構築します。
    pub fn from_slice(src: &[T]) -> Self {
        src.iter().cloned().collect::<Self>()
    }

    /// `a[i]` を `x` に書き換えます。
    pub fn set(&mut self, i: usize, x: T) {
        assert!(i < self.len);
        self.modify(i, |y| y.clone_from(&x));
    }
    /// `a[i]` を取得します。
    pub fn get(&self, i: usize) -> &T {
        assert!(i < self.len);
        &self.table[self.len + i]
    }
    /// `a[i]` を編集します。
    pub fn modify(&mut self, mut i: usize, f: impl Fn(&mut T)) {
        assert!(i < self.len);
        i += self.len;
        f(&mut self.table[i]);
        for i in iter::successors(Some(i / 2), |&x| if x == 0 { None } else { Some(x / 2) }) {
            self.update(i);
        }
    }
    /// `a[range]` を `T::op` で畳み込みます。
    pub fn fold_first(&self, range: impl ops::RangeBounds<usize>) -> Option<T> {
        let (mut start, mut end) = open(self.len, range);
        assert!(start <= end, "変な区間を渡すのをやめませんか？");
        assert!(end <= self.len, "範囲外は禁止です！");
        start += self.len;
        end += self.len;

        if start == end {
            None
        } else if start + 1 == end {
            Some(self.table[start].clone())
        } else {
            let mut left = self.table[start].clone();
            start += 1;
            end -= 1;
            let mut right = self.table[end].clone();
            while start != end {
                if start % 2 == 1 {
                    left.op_from_right(&self.table[start]);
                    start += 1;
                }
                if end % 2 == 1 {
                    end -= 1;
                    right.op_from_left(&self.table[end]);
                }
                start /= 2;
                end /= 2;
            }
            Some(T::op(left, right))
        }
    }

    /// `a` への参照を返します。
    pub fn as_slice(&self) -> &[T] {
        &self.table[self.len..]
    }

    /// `self.fold(start..end).unwrap_or(true)` が `true` となる最大の `end` を返します。
    ///
    /// # 計算量
    ///
    /// `O(log(range.len()))` 回の `T::op` 呼び出しをします。
    pub fn forward_partition_point_first(
        &self,
        start: usize,
        mut f: impl FnMut(&T) -> bool,
    ) -> usize {
        assert!(start <= self.len, "範囲外は禁止です！");
        let mut i = self.len + start;
        if self.fold_first(start..).map(|x| f(&x)).unwrap_or(true) {
            self.len
        } else if !f(&self.table[i]) {
            start
        } else {
            let mut current = self.table[i].clone();
            i += 1;
            let mut next = current.clone().op(self.table[i].clone());

            while f(&next) {
                if i % 2 == 0 {
                    i /= 2;
                } else {
                    current = next.clone();
                    i += 1;
                }
                next = current.clone().op(self.table[i].clone());
            }
            loop {
                if f(&next) {
                    current = next.clone();
                    i += 1;
                } else {
                    if self.len < i {
                        return i - self.len;
                    }
                    i *= 2;
                }
                next = current.clone().op(self.table[i].clone());
            }
        }
    }

    /// `self.fold(start..end).unwrap_or(true)` が `true` となる最小の `start` を返します。
    ///
    /// # 計算量
    ///
    /// `O(log(range.len()))` 回の `T::op` 呼び出しをします。
    pub fn backward_partition_point_first(
        &self,
        end: usize,
        mut f: impl FnMut(&T) -> bool,
    ) -> usize {
        assert!(end <= self.len, "範囲外は禁止です！");
        let mut i = self.len + end;
        if self.fold_first(..end).map(|x| f(&x)).unwrap_or(true) {
            0
        } else if !f(&self.table[i - 1]) {
            end
        } else {
            i -= 1;
            let mut current = self.table[i].clone();
            let mut next = self.table[i - 1].clone().op(current.clone());

            while f(&next) {
                if i % 2 == 0 {
                    i /= 2;
                } else {
                    i -= 1;
                    current = next.clone();
                }
                next = self.table[i - 1].clone().op(current.clone());
            }
            loop {
                if f(&next) {
                    i -= 1;
                    current = next.clone();
                } else {
                    if self.len < i {
                        return i - self.len;
                    }
                    i *= 2;
                }
                next = self.table[i - 1].clone().op(current.clone());
            }
        }
    }
    /// `self.fold(start..end).map(|x| &project(x) < value).unwrap_or(true)` が `true` となる最大の
    /// `end` を返します。
    pub fn forward_lower_bound_by_key_first<U: Ord>(
        &self,
        start: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.forward_partition_point_first(start, |x| &project(x) < value)
    }
    /// `self.fold(start..end).map(|x| &project(x) <= value).unwrap_or(true)` が `true` となる最大の
    /// `end` を返します。
    pub fn forward_upper_bound_by_key_first<U: Ord>(
        &self,
        start: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.forward_partition_point_first(start, |x| &project(x) <= value)
    }
    /// `self.fold(start..end).map(|x| &project(x) < value).unwrap_or(true)` が `true` となる最小の
    /// `start` を返します。
    pub fn backward_lower_bound_by_key_first<U: Ord>(
        &self,
        end: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.backward_partition_point_first(end, |x| &project(x) < value)
    }
    /// `self.fold(start..end).map(|x| &project(x) <= value).unwrap_or(true)` が `true` となる最小の
    /// `start` を返します。
    pub fn backward_upper_bound_by_key_first<U: Ord>(
        &self,
        end: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.backward_partition_point_first(end, |x| &project(x) <= value)
    }

    fn update(&mut self, i: usize) {
        let x = T::op(self.table[2 * i].clone(), self.table[2 * i + 1].clone());
        self.table[i] = x;
    }
}

impl<T: Identity> Segtree<T> {
    /// 単位元のある結合的な演算で畳み込みます。
    pub fn fold(&self, range: impl ops::RangeBounds<usize>) -> T {
        let (mut start, mut end) = open(self.len, range);
        start += self.len;
        end += self.len;
        let mut left = T::identity();
        let mut right = T::identity();
        while start != end {
            if start % 2 == 1 {
                left.op_from_right(&self.table[start]);
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                right.op_from_left(&self.table[end]);
            }
            start /= 2;
            end /= 2;
        }
        left.op(right)
    }

    /// `pred(fold(start..end))` が `true` となる細大の `end` を返します。
    ///
    /// # Panics
    ///
    /// `fold(T::Identity())` が `false` なとき、パニックです。
    pub fn forward_partition_point(&self, start: usize, mut pred: impl FnMut(&T) -> bool) -> usize {
        assert!(pred(&T::identity()));
        let mut i = start + self.len;
        let mut crr = T::identity();
        if pred(&self.fold(start..)) {
            self.len
        } else if !pred(&self.table[i]) {
            start
        } else {
            loop {
                i >>= i.trailing_zeros();
                let nxt = crr.clone().op(self.table[i].clone());
                if !pred(&nxt) {
                    break;
                }
                crr = nxt;
                i += 1;
            }
            loop {
                let nxt = crr.clone().op(self.table[i].clone());
                if pred(&nxt) {
                    crr = nxt;
                    i += 1;
                }
                if self.len <= i {
                    break i - self.len;
                }
                i <<= 1;
            }
        }
    }
    /// TODO
    pub fn forward_upper_bound_by_key<U: Ord>(
        &self,
        start: usize,
        value: &U,
        mut project: impl FnMut(&T) -> U,
    ) -> usize {
        self.forward_partition_point(start, |x| &project(x) <= value)
    }
}

impl<T: Assoc + Ord> Segtree<T> {
    /// `self.fold(start..end).map(|x| &x < value).unwrap_or(true)` が `true` となる最大の `end`
    /// を返します。
    pub fn forward_lower_bound_first(&self, start: usize, value: &T) -> usize {
        self.forward_partition_point_first(start, |x| x < value)
    }
    /// `self.fold(start..end).map(|x| &x <= value).unwrap_or(true)` が `true` となる最大の `end`
    /// を返します。
    pub fn forward_upper_bound_first(&self, start: usize, value: &T) -> usize {
        self.forward_partition_point_first(start, |x| x <= value)
    }
    /// `self.fold(start..end).map(|x| &x < value).unwrap_or(true)` が `true` となる最小の `start`
    /// を返します。
    pub fn backward_lower_bound_first(&self, end: usize, value: &T) -> usize {
        self.backward_partition_point_first(end, |x| x < value)
    }
    /// `self.fold(start..end).map(|x| &x <= value).unwrap_or(true)` が `true` となる最小の `start`
    /// を返します。
    pub fn backward_upper_bound_first(&self, end: usize, value: &T) -> usize {
        self.backward_partition_point_first(end, |x| x <= value)
    }
}

fn open(len: usize, range: impl ops::RangeBounds<usize>) -> (usize, usize) {
    use ops::Bound::*;
    (
        match range.start_bound() {
            Unbounded => 0,
            Included(&x) => x,
            Excluded(&x) => x + 1,
        },
        match range.end_bound() {
            Excluded(&x) => x,
            Included(&x) => x + 1,
            Unbounded => len,
        },
    )
}

#[cfg(test)]
mod tests {
    mod impl_query;
    use query_test_2::{
        config,
        gen::{GenFoldedKey, GenLen, GenValue},
        query::{Fold, ForwardUpperBoundByKey, Get, Project, Set},
        Vector,
    };
    use rand::prelude::*;
    use type_traits::{binary::Add, Constant};

    type Fp = fp::F998244353;
    type Tester<T, G> = query_test_2::Tester<StdRng, Vector<T>, crate::Segtree<T>, G>;
    const CONFIG: config::Config = config::Config {
        initialize: config::Initizlize::Short,
        pre: None,
        passing: config::Checked::Short,
        failing: config::Checked::Verbose,
        unchecked: config::Unchecked::Short,
    };

    #[test]
    fn test_add_fp() {
        type Node = Add<Fp>;
        struct G {}
        impl GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 20)
            }
        }
        impl GenValue<Node> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Node {
                Add(Fp::new(rng.gen_range(0, fp::Mod998244353::VALUE)))
            }
        }
        let mut tester = Tester::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 3);
                match command {
                    0 => tester.test_get::<Get<_>>(),
                    1 => tester.test_mut::<Set<_>>(),
                    2 => tester.test::<Fold<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_add_u32() {
        type Node = Add<u32>;
        struct G {}
        impl GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 20)
            }
        }
        impl GenValue<Node> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Node {
                Add(rng.gen_range(0, 10))
            }
        }
        impl GenFoldedKey<u32> for G {
            fn gen_folded_key<R: Rng>(rng: &mut R) -> u32 {
                rng.gen_range(0, 50)
            }
        }
        struct P {}
        impl Project<Add<u32>, u32> for P {
            fn project(Add(x): Add<u32>) -> u32 {
                x
            }
        }
        let mut tester = Tester::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..1000 {
                let command = tester.rng_mut().gen_range(0, 4);
                match command {
                    0 => tester.test_get::<Get<_>>(),
                    1 => tester.test_mut::<Set<_>>(),
                    2 => tester.test::<Fold<_>>(),
                    3 => tester.test::<ForwardUpperBoundByKey<_, _, P>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
