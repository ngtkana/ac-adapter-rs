#![warn(missing_docs)]

//! 二分探索機能付きセグメントツリーです。

use std::{
    iter,
    ops::{self, Range, RangeBounds},
};
use type_traits::*;

/// セグツリー本体です。
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
    pub fn fold_first(&self, range: impl RangeBounds<usize>) -> Option<T> {
        let Range { mut start, mut end } = open(self.len, range);
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

    fn update(&mut self, i: usize) {
        let x = T::op(self.table[2 * i].clone(), self.table[2 * i + 1].clone());
        self.table[i] = x;
    }
}

impl<T: Identity> Segtree<T> {
    /// 単位元のある結合的な演算で畳み込みます。
    pub fn fold(&self, range: impl RangeBounds<usize>) -> T {
        let Range { mut start, mut end } = open(self.len, range);
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

    #[allow(missing_docs)]
    pub fn search_forward(
        &self,
        range: impl RangeBounds<usize>,
        mut pred: impl FnMut(&T) -> bool,
    ) -> usize {
        let Range { mut start, mut end } = open(self.len, range);
        assert!(start <= end && end <= self.len);
        start += self.len;
        end += self.len;
        let orig_end = end;

        let mut crr = T::identity();
        let mut shift = 0;
        while start != end {
            if start % 2 == 1 {
                let nxt = crr.clone().op(self.table[start].clone());
                if !pred(&nxt) {
                    return self.search_subtree_forward(crr, start, pred);
                }
                crr = nxt;
                start += 1;
            }
            start >>= 1;
            end >>= 1;
            shift += 1;
        }
        while shift != 0 {
            shift -= 1;
            end = orig_end >> shift;
            if end % 2 == 1 {
                end -= 1;
                let nxt = crr.clone().op(self.table[end].clone());
                if !pred(&nxt) {
                    return self.search_subtree_forward(crr, end, pred);
                }
                crr = nxt;
            }
        }
        orig_end - self.len
    }

    #[allow(missing_docs)]
    pub fn search_backward(
        &self,
        range: impl RangeBounds<usize>,
        mut pred: impl FnMut(&T) -> bool,
    ) -> usize {
        let Range { mut start, mut end } = open(self.len, range);
        assert!(start <= end && end <= self.len);
        start += self.len;
        end += self.len;
        let orig_start = start;

        let mut crr = T::identity();
        let mut shift = 0;
        while start != end {
            if end % 2 == 1 {
                end -= 1;
                let nxt = self.table[end].clone().op(crr.clone());
                if !pred(&nxt) {
                    return self.search_subtree_backward(crr, end, pred);
                }
                crr = nxt;
            }
            start += 1;
            start >>= 1;
            end >>= 1;
            shift += 1;
        }
        while shift != 0 {
            shift -= 1;
            start = (orig_start - 1 >> shift) + 1;
            if start % 2 == 1 {
                let nxt = self.table[start].clone().op(crr.clone());
                if !pred(&nxt) {
                    return self.search_subtree_backward(crr, start, pred);
                }
                crr = nxt;
            }
        }
        orig_start - self.len
    }

    fn search_subtree_forward(
        &self,
        mut crr: T,
        mut root: usize,
        mut pred: impl FnMut(&T) -> bool,
    ) -> usize {
        while root < self.len {
            let nxt = crr.clone().op(self.table[root * 2].clone());
            root = match pred(&nxt) {
                false => root * 2,
                true => {
                    crr = nxt;
                    root * 2 + 1
                }
            };
        }
        root - self.len
    }
    fn search_subtree_backward(
        &self,
        mut crr: T,
        mut root: usize,
        mut pred: impl FnMut(&T) -> bool,
    ) -> usize {
        while root < self.len {
            let nxt = self.table[root * 2 + 1].clone().op(crr.clone());
            root = match pred(&nxt) {
                true => {
                    crr = nxt;
                    root * 2
                }
                false => root * 2 + 1,
            };
        }
        root + 1 - self.len
    }
}

fn open(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    use ops::Bound::*;
    (match range.start_bound() {
        Unbounded => 0,
        Included(&x) => x,
        Excluded(&x) => x + 1,
    })..(match range.end_bound() {
        Excluded(&x) => x,
        Included(&x) => x + 1,
        Unbounded => len,
    })
}

#[cfg(test)]
mod tests {
    mod impl_query;
    use query_test_2::{gen, query, utils, Vector, CONFIG};
    use rand::prelude::*;
    use type_traits::Constant;

    type Fp = fp::F998244353;
    type Tester<T, G> = query_test_2::Tester<StdRng, Vector<T>, crate::Segtree<T>, G>;

    #[test]
    fn test_add_fp() {
        use type_traits::binary::Add;

        type Node = Add<Fp>;
        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 100)
            }
        }
        impl gen::GenValue<Node> for G {
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
                    0 => tester.compare::<query::Get<_>>(),
                    1 => tester.mutate::<query::Set<_>>(),
                    2 => tester.compare::<query::Fold<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_add_u32() {
        use type_traits::binary::Add;
        type Node = Add<u32>;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 100)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Node {
                Add(rng.gen_range(0, 10))
            }
        }
        impl gen::GenFoldedKey<u32> for G {
            fn gen_folded_key<R: Rng>(rng: &mut R) -> u32 {
                rng.gen_range(0, 50)
            }
        }

        struct P {}
        impl utils::Project<Add<u32>, u32> for P {
            fn project(x: Add<u32>) -> u32 {
                x.0
            }
        }

        let mut tester = Tester::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 5);
                match command {
                    0 => tester.compare::<query::Get<_>>(),
                    1 => tester.mutate::<query::Set<_>>(),
                    2 => tester.compare::<query::Fold<_>>(),
                    3 => tester.judge::<query::ForwardUpperBoundByKey<_, u32, P>>(),
                    4 => tester.judge::<query::BackwardUpperBoundByKey<_, u32, P>>(),
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_cat() {
        use type_traits::binary::Cat;
        type Node = Cat;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 100)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Node {
                Cat(rng.sample(rand::distributions::Alphanumeric).to_string())
            }
        }

        let mut tester = Tester::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 3);
                match command {
                    0 => tester.compare::<query::Get<_>>(),
                    1 => tester.mutate::<query::Set<_>>(),
                    2 => tester.compare::<query::Fold<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }

    #[test]
    fn test_inversion() {
        use type_traits::binary::InvertionNumber;
        type Node = InvertionNumber;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 100)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Node {
                InvertionNumber::from_bool(rng.gen_ratio(1, 2))
            }
        }
        impl gen::GenFoldedKey<u64> for G {
            fn gen_folded_key<R: Rng>(rng: &mut R) -> u64 {
                rng.gen_range(0, 50)
            }
        }

        struct P {}
        impl utils::Project<InvertionNumber, u64> for P {
            fn project(x: InvertionNumber) -> u64 {
                x.invertion
            }
        }

        let mut tester = Tester::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 5);
                match command {
                    0 => tester.compare::<query::Get<_>>(),
                    1 => tester.mutate::<query::Set<_>>(),
                    2 => tester.compare::<query::Fold<_>>(),
                    3 => tester.judge::<query::ForwardUpperBoundByKey<_, u64, P>>(),
                    4 => tester.judge::<query::BackwardUpperBoundByKey<_, u64, P>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
