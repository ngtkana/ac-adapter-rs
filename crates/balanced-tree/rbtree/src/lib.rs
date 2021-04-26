#![warn(missing_docs)]
//! 赤黒木
//!
//! # 主な機能
//!
//! * merge, split
//! * insert, delete
//! * get
//! * fold
//! * iter, [`FromIterator`]
//!
//!
//! # 使い方（fold しない場合）
//!
//! [`RbTree`]
//! の第二ジェネリック型引数をデフォルトのままにしておくと、ランダムアクセスリストを実現します。
//!
//! ```
//! use rbtree::RbTree;
//!
//! let mut a = RbTree::<i32>::new(); // `i32` まで省略すると型推論に失敗します。
//!
//! // 挿入や削除など
//! a.push_back(12);
//! a.push_front(10);
//! a.insert(1, 11);
//! a.push_back(13);
//! a.delete(2);
//! assert_eq!(
//!     a.iter().copied().collect::<Vec<_>>(),
//!     vec![10, 11, 13]
//! );
//! assert_eq!(a.get(0), 10);
//! assert_eq!(a.get(1), 11);
//! assert_eq!(a.get(2), 13);
//!
//! // マージ
//! let a = RbTree::merge(a.clone(), a);
//! assert_eq!(
//!     a.iter().copied().collect::<Vec<_>>(),
//!     vec![10, 11, 13, 10, 11, 13]
//! );
//!
//! // スプリット
//! let [b, c] = a.split(4);
//! assert_eq!(
//!     b.iter().copied().collect::<Vec<_>>(),
//!     vec![10, 11, 13, 10]
//! );
//! assert_eq!(
//!     c.iter().copied().collect::<Vec<_>>(),
//!     vec![11, 13]
//! );
//! ```
//!
//!
//! # 使い方（fold)
//!
//! [`Op`] トレイトを実装した型を作って入れましょう。（これめんどくさいですね……）
//!
//! ```
//! use rbtree::{RbTree, Op};
//!
//! // 加法を実現する型を定義です。
//! enum O {}
//! impl Op for O {
//!     type Summary = i32;
//!     type Value = i32;
//!     fn summarize(value: &i32) -> i32 {
//!         *value
//!     }
//!     fn op(lhs: i32, rhs: i32) -> i32 {
//!         lhs + rhs
//!     }
//! }
//!
//! let mut a = (0..10).collect::<RbTree<_, O>>(); // これは mut ないといけません。
//! assert_eq!(a.fold(..), Some(45));
//! assert_eq!(a.fold(4..=5), Some(9));
//! assert_eq!(a.fold(8..), Some(17));
//! assert_eq!(a.fold(3..3), None);
//! ```
//!
//!
//! # 所有権について
//!
//! [`fold`](RbTree::fold`) が を要求します。ごめんなさい……（これ `RefCell` などにすると今度は
//! 参照を返せなくなって詰んでしまいます。）それと [`get`](RbTree::get) が `T: Copy`
//! を要求しており、値返しとなっております。
//!
//!
//! # 愚痴
//!
//! [`Clone`], [`Hash`], [`PartialEq`] をて実装するはめになったのですが！？
//!

mod detail;

use {
    detail::{Nil, Root},
    std::{
        fmt::{self, Debug},
        hash::{Hash, Hasher},
        iter::FromIterator,
        marker::PhantomData,
        mem::take,
        ops::{Bound, Range, RangeBounds},
    },
};

/// 赤黒木です。
pub struct RbTree<T, O: Op<Value = T> = Nop<T>>(Option<Root<T, O>>);
/// 赤黒木に演算を載せたいときに実装するトレイトです。（演算を載せないときには使いません）
pub trait Op {
    /// 葉に持たせる値
    type Value;
    /// 中間ノードに持たせる値
    type Summary: Clone;
    /// 葉の値から中間ノードの値への変換
    fn summarize(value: &Self::Value) -> Self::Summary;
    /// 演算
    fn op(lhs: Self::Summary, rhs: Self::Summary) -> Self::Summary;
}
/// 赤黒木に演算を載せないときに使う型です。[`RbTree`] のデフォルト引数になっています。
pub struct Nop<T> {
    __marker: PhantomData<fn(T) -> T>,
}
impl<T> Op for Nop<T> {
    type Value = T;
    type Summary = ();
    fn summarize(_value: &Self::Value) -> Self::Summary {}
    fn op(_lhs: Self::Summary, _rhs: Self::Summary) -> Self::Summary {}
}

impl<A, O: Op<Value = A>> FromIterator<A> for RbTree<A, O> {
    /// イテレータから赤黒木を、分割統治法で構築します。
    ///
    /// # 計算量
    ///
    /// N を要素数として、Θ( N )
    ///
    fn from_iter<T: IntoIterator<Item = A>>(iter: T) -> Self {
        let mut nodes = iter.into_iter().map(Self::singleton).collect::<Vec<_>>();
        if nodes.is_empty() {
            return Self::default();
        }
        let mut step = 1;
        while step < nodes.len() {
            for i in (0..nodes.len() - step).step_by(2 * step) {
                nodes[i] = Self::merge(take(&mut nodes[i]), take(&mut nodes[i + step]));
            }
            step *= 2;
        }
        take(&mut nodes[0])
    }
}

/// [`iter`](RbTree::iter) の返す型
pub struct Iter<'a, T, O: Op<Value = T>>(Vec<&'a Root<T, O>>);
impl<'a, T, O: Op<Value = T>> Iterator for Iter<'a, T, O> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.0.pop() {
                None => return None,
                Some(Root::Nil(Nil(x))) => return Some(x),
                Some(Root::Node(node)) => {
                    self.0.push(&node.right);
                    self.0.push(&node.left);
                }
            }
        }
    }
}

impl<T, O: Op<Value = T>> RbTree<T, O> {
    /// 空の赤黒木を生成します。
    pub fn new() -> Self {
        Self(None)
    }
    /// 空ならば `true`、さもなくば `false` を返します。
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
    /// 長さ、すなわち Nil ノードの個数を返します。
    pub fn len(&self) -> usize {
        match &self.0 {
            None => 0,
            Some(node) => node.len(),
        }
    }
    /// 要素を左から順に辿るイテレータを返します。（`rev`, `nth` など未実装です。）
    pub fn iter(&self) -> Iter<'_, T, O> {
        Iter(match &self.0 {
            None => Vec::new(),
            Some(node) => vec![node],
        })
    }
    /// `i` 番目の要素をコピーして返します。
    ///
    /// # Panics
    ///
    /// 範囲外のとき
    pub fn get(&mut self, i: usize) -> T
    where
        T: Copy,
    {
        assert!((0..self.len()).contains(&i));
        let root = take(&mut self.0).unwrap();
        let [l, cr] = Self(Some(root)).split(i);
        let [c, r] = cr.split(1);
        let res = match c.0.as_ref().unwrap() {
            Root::Nil(nil) => nil.0,
            Root::Node(_) => unreachable!(),
        };
        *self = Self::merge(Self::merge(l, c), r);
        res
    }
    /// `range` の範囲で畳み込みます。
    ///
    /// # Panics
    ///
    /// 範囲外のとき
    pub fn fold(&mut self, range: impl RangeBounds<usize>) -> Option<O::Summary> {
        let Range { start, end } = open(range, self.len());
        assert!(start <= end && end <= self.len());
        if start == end {
            None
        } else {
            Some(self.0.as_ref().unwrap().fold(start, end))
        }
    }
    /// Nil ノード一つのみからなる新しい赤黒木を構築します。
    pub fn singleton(x: T) -> Self {
        Self(Some(Root::Nil(Nil(x))))
    }
    /// 新しいノードを先頭に挿入します。
    pub fn push_front(&mut self, x: T) {
        *self = Self::merge(Self::singleton(x), take(self));
    }
    /// 新しいノードを末尾に挿入します。
    pub fn push_back(&mut self, x: T) {
        *self = Self::merge(take(self), Self::singleton(x));
    }
    /// `i` 番目に新しい Nil ノードを挿入します。
    ///
    /// # Panics
    ///
    /// 範囲外のとき
    pub fn insert(&mut self, i: usize, x: T) {
        assert!((0..=self.len()).contains(&i));
        let [l, r] = take(self).split(i);
        *self = Self::merge3(l, Self::singleton(x), r);
    }
    /// `i` 番目の Nil ノードを削除して、保持していたデータを返します。
    ///
    /// # Panics
    ///
    /// 範囲外のとき
    pub fn delete(&mut self, i: usize) -> T {
        assert!((0..self.len()).contains(&i));
        let [l, c, r] = take(self).split3(i, i + 1);
        *self = Self::merge(l, r);
        match c.0 {
            Some(Root::Node(_)) | None => unreachable!(),
            Some(Root::Nil(Nil(value))) => value,
        }
    }
    /// 2 つの赤黒木をマージします。
    pub fn merge(lhs: Self, rhs: Self) -> Self {
        match [lhs.0, rhs.0] {
            [None, None] => Self(None),
            [Some(l), None] => Self(Some(l)),
            [None, Some(r)] => Self(Some(r)),
            [Some(l), Some(r)] => Self(Some(Root::merge(l, r))),
        }
    }
    /// 3 つの赤黒木をマージします。
    pub fn merge3(x: Self, y: Self, z: Self) -> Self {
        Self::merge(Self::merge(x, y), z)
    }
    /// `i` 番目で分割します。
    ///
    /// # Panics
    ///
    /// 範囲外のとき
    pub fn split(self, i: usize) -> [Self; 2] {
        assert!((0..=self.len()).contains(&i));
        if i == 0 {
            [Self(None), self]
        } else if i == self.len() {
            [self, Self(None)]
        } else {
            let [l, r] = self.0.unwrap().split(i);
            [Self(Some(l)), Self(Some(r))]
        }
    }
    /// `l, r` 番目で 3 つに分割します。
    ///
    /// # Panics
    ///
    /// 範囲外のとき
    pub fn split3(self, start: usize, end: usize) -> [Self; 3] {
        let [xy, z] = self.split(end);
        let [x, y] = xy.split(start);
        [x, y, z]
    }
}

impl<T: Clone, O: Op<Value = T>> Clone for RbTree<T, O>
where
    O::Summary: Clone,
{
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<T: PartialEq, O: Op<Value = T>> PartialEq for RbTree<T, O>
where
    O::Summary: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.0.eq(&other.0)
    }
}
impl<T: Hash, O: Op<Value = T>> Hash for RbTree<T, O>
where
    O::Summary: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}
impl<T: Debug, O: Op<Value = T>> Debug for RbTree<T, O> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl<T, O: Op<Value = T>> Default for RbTree<T, O> {
    fn default() -> Self {
        Self::new()
    }
}

fn open(range: impl RangeBounds<usize>, len: usize) -> Range<usize> {
    (match range.start_bound() {
        Bound::Unbounded => 0,
        Bound::Included(&x) => x,
        Bound::Excluded(&x) => x + 1,
    })..match range.end_bound() {
        Bound::Excluded(&x) => x,
        Bound::Included(&x) => x + 1,
        Bound::Unbounded => len,
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{Op, RbTree, Root},
        itertools::Itertools,
        rand::{distributions::Alphanumeric, prelude::StdRng, Rng, SeedableRng},
        randtools::SubRange,
        std::{fmt::Debug, iter::repeat_with},
    };

    fn validate<T: Debug, O: Op<Value = T>>(tree: &RbTree<T, O>) {
        match &tree.0 {
            None => (),
            Some(root) => validate_dfs(root),
        }
    }
    fn validate_dfs<T: Debug, O: Op<Value = T>>(root: &Root<T, O>) {
        if let Some(node) = root.node() {
            let h = node.height;
            assert_eq!(node.len, node.left.len() + node.right.len());
            for x in node.left.node().into_iter().chain(node.right.node()) {
                assert!(x.height == node.height || x.height == node.height - 1);
                for y in x.left.node().into_iter().chain(x.right.node()) {
                    assert_ne!(y.height, h);
                }
            }
            validate_dfs(&node.left);
            validate_dfs(&node.right);
        }
    }

    #[test]
    fn test_iter() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..200);
            let a = repeat_with(|| rng.gen_range(0..100)).take(n).collect_vec();
            let tree = a.iter().copied().collect::<RbTree<_>>();
            validate(&tree);
            let b = tree.iter().copied().collect_vec();
            assert_eq!(&a, &b);
        }
    }

    #[test]
    fn test_insert_delete() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let len = rng.gen_range(0..80);
            let mut a = repeat_with(|| rng.gen_range(0..100))
                .take(len)
                .collect_vec();
            let mut tree = a.iter().copied().collect::<RbTree<_>>();
            validate(&tree);
            let b = tree.iter().copied().collect_vec();
            assert_eq!(&a, &b);

            for _ in 0..10 + 2 * len {
                match rng.gen_range(0..2) {
                    // insert
                    0 => {
                        let i = rng.gen_range(0..=a.len());
                        let x = rng.gen_range(0..100);
                        a.insert(i, x);
                        tree.insert(i, x);
                    }
                    // delete
                    1 => {
                        let i = rng.gen_range(0..a.len());
                        a.remove(i);
                        tree.delete(i);
                    }
                    _ => unreachable!(),
                }
                validate(&tree);
                let b = tree.iter().copied().collect_vec();
                assert_eq!(&a, &b);
            }
        }
    }

    struct O {}
    impl Op for O {
        type Summary = String;
        type Value = char;
        fn summarize(value: &Self::Value) -> Self::Summary {
            value.to_string()
        }
        fn op(lhs: Self::Summary, rhs: Self::Summary) -> Self::Summary {
            lhs.chars().chain(rhs.chars()).collect()
        }
    }

    #[test]
    fn test_fold() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let len = rng.gen_range(0..20);
            let a = repeat_with(|| rng.sample(Alphanumeric))
                .map(|c| c as char)
                .take(len)
                .collect_vec();
            let mut tree = a.iter().copied().collect::<RbTree<_, O>>();
            validate(&tree);

            for _ in 0..10 + 2 * len {
                let range = rng.sample(SubRange(0..len));
                let result = tree.fold(range.clone()).unwrap_or_default();
                let expected = a[range].iter().collect::<String>();
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_insert_delete_fold_get() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let len = rng.gen_range(0..80);
            let mut a = repeat_with(|| rng.sample(Alphanumeric))
                .map(|c| c as char)
                .take(len)
                .collect_vec();
            let mut tree = a.iter().copied().collect::<RbTree<_, O>>();
            validate(&tree);
            let b = tree.iter().copied().collect_vec();
            assert_eq!(&a, &b);

            for _ in 0..10 + 2 * len {
                match rng.gen_range(0..3) {
                    // insert
                    0 => {
                        let i = rng.gen_range(0..=a.len());
                        let x = rng.sample(Alphanumeric) as char;
                        a.insert(i, x);
                        tree.insert(i, x);
                    }
                    // delete
                    1 => {
                        let i = rng.gen_range(0..a.len());
                        a.remove(i);
                        tree.delete(i);
                    }
                    // fold
                    2 => {
                        let range = rng.sample(SubRange(0..a.len()));
                        let result = tree.fold(range.clone()).unwrap_or_default();
                        let expected = a[range].iter().collect::<String>();
                        assert_eq!(result, expected);
                    }
                    // get
                    3 => {
                        let i = rng.gen_range(0..a.len());
                        let result = tree.get(i);
                        let expected = a[i];
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
                validate(&tree);
                let b = tree.iter().copied().collect_vec();
                assert_eq!(&a, &b);
            }
        }
    }
}
