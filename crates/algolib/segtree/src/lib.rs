//! セグツリーです。
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
//! seg.set(4, Add(5));
//! assert_eq!(seg.fold(4..6), Some(Add(10)));
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
//! - [`set`] : 更新
//! - [`fold`] : 区間クエリ
//!
//!
//! # その他便利な機能
//!
//! - [`partition_point`] : 二分探索
//! - [`as_slice`] : デバッグにどうぞです。
//!
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
//! [`set`]: struct.Segtree.html#method.set
//! [`fold`]: struct.Segtree.html#method.fold
//! [`partition_point`]: struct.Segtree.html#method.partition_point
//! [`as_slice`]: struct.Segtree.html#method.as_slice

pub use traits::Value;
pub use values::{Add, Affine, Cat, First, Inversion, Max, Min, Mul, Second};

use std::{iter, ops};

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
    /// seg.set(0, Add(5));
    /// assert_eq!(seg.fold(..), Some(Add(25)));
    /// ```
    pub fn set(&mut self, mut i: usize, x: T) {
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
    /// seg.update(0, |Add(ref mut x)| *x = *x + 1);
    /// assert_eq!(seg.fold(..), Some(Add(31)));
    /// ```
    pub fn update<F>(&mut self, mut i: usize, modifier: F)
    where
        F: Fn(&mut T),
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
    /// 概念的な配列を `a` として、`start..end` 内の任意の `i` について `pred(&a[i])`
    /// が `true` であり、`end..self.len()` 内の任意の `i` について `pred(&a[i])` が `false`
    /// であるような `end` を返します。
    ///
    /// そのような `end` が存在しないとき（つまり、`pred` によって区分化されていないとき）
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
    pub fn partition_point(&self, start: usize, pred: impl Fn(&T) -> bool) -> usize {
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
    pub trait Value: Clone {
        fn op(&self, rhs: &Self) -> Self;

        fn op_assign_from_the_right(&mut self, rhs: &Self) {
            *self = self.op(rhs);
        }

        fn op_assign_from_the_left(&mut self, rhs: &Self) {
            *self = rhs.op(self);
        }
    }
}

mod values {
    use super::Value;
    use std::{cmp, ops};

    /// 文字列結合
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Cat(pub String);
    impl Value for Cat {
        fn op(&self, rhs: &Self) -> Self {
            Cat(self.0.chars().chain(rhs.0.chars()).collect())
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

    /// 転倒数
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Inversion {
        zeros: usize,
        ones: usize,
        inv: usize,
    }
    impl Inversion {
        pub fn inv(&self) -> usize {
            self.inv
        }
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
        pub fn zero() -> Self {
            Self {
                zeros: 1,
                ones: 0,
                inv: 0,
            }
        }
        pub fn one() -> Self {
            Self {
                zeros: 0,
                ones: 1,
                inv: 0,
            }
        }
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
    pub struct First<T: std::fmt::Debug + Clone>(pub T);
    impl<T: std::fmt::Debug + Clone> Value for First<T> {
        fn op(&self, _rhs: &Self) -> Self {
            self.clone()
        }
    }

    /// 第二成分を返します。
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Second<T: std::fmt::Debug + Clone>(pub T);
    impl<T: std::fmt::Debug + Clone> Value for Second<T> {
        fn op(&self, rhs: &Self) -> Self {
            rhs.clone()
        }
    }

    /// アフィンです。
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Affine<T: std::fmt::Debug + Clone> {
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
    use std::{iter, mem};

    #[test]
    fn test_add_partition_point_hand() {
        let n = 11;
        let seg = Segtree::from_slice(&vec![Add(1); n]);

        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 0), 0);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 1), 1);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 2), 2);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 3), 3);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 4), 4);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 5), 5);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 6), 6);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 7), 7);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 8), 8);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 9), 9);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 10), 10);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 11), 11);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 12), 11);
        assert_eq!(seg.partition_point(0, |&Add(x)| x <= 13), 11);
    }

    #[test]
    fn test_add_partition_point_exhaustive() {
        for n in 0..40 {
            let seg = Segtree::from_slice(&vec![Add(1); n]);
            for l in 0..n {
                for d in 0..n + 2 {
                    assert_eq!(seg.partition_point(l, |&Add(x)| x <= d), (l + d).min(n));
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
        assert_eq!(seg.fold(3..5), Some(Cat("34".to_owned())));
        assert_eq!(seg.fold(2..9), Some(Cat("2345678".to_owned())));
        assert_eq!(seg.fold(0..4), Some(Cat("0123".to_owned())));
        assert_eq!(seg.fold(8..8), None);

        seg.set(3, Cat("d".to_owned()));
        seg.set(6, Cat("g".to_owned()));
    }

    const NUMBER_OF_TEST_CASES: usize = 20;
    const NUMBER_OF_QUERIES: usize = 50;

    #[test]
    fn test_cat_random() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(32, 64);
            let mut a = iter::repeat_with(|| rng.sample(rand::distributions::Alphanumeric))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a
                .iter()
                .map(|&c| Cat(c.to_string()))
                .collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {}", n, &a.iter().collect::<String>());

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=84 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.sample(rand::distributions::Alphanumeric);

                        a[i] = x;
                        seg.set(i, Cat(x.to_string()));

                        println!("\tSet {}, {}, a = {:?}", i, x, a.iter().collect::<String>());
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let expected = a[range.clone()].iter().copied().collect::<String>();
                        let result = seg
                            .fold(range.clone())
                            .map(|x| x.0)
                            .unwrap_or_else(Default::default);
                        println!(
                            "\tFold {:?}, expected = {}, result = {}",
                            &range, expected, result
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
    fn test_add_random() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(32, 64);
            let mut a = iter::repeat_with(|| rng.gen_range(0, 100))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a.iter().map(|&x| Add(x)).collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=69 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.gen_range(0, 100);

                        a[i] = x;
                        seg.set(i, Add(x));

                        println!("\tSet (i = {}, x = {}) -> a = {:?}", i, x, &a);
                    }
                    // Partition point
                    70..=84 => {
                        let start = rng.gen_range(0, n);
                        let value = rng.gen_range(0, 1000);

                        let mut now = 0;
                        let mut i = start;
                        while i < n && (now + a[i]) <= value {
                            now += a[i];
                            i += 1;
                        }

                        let expected = i;
                        let result = seg.partition_point(start, |&Add(x)| x <= value);

                        println!(
                            "\tLower bound (start = {}, value = {}) -> (expected = {}, result = {})",
                            start, value, expected, result
                        );
                        assert_eq!(expected, result);
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let expected = a[range.clone()].iter().sum::<u32>();
                        let result = seg
                            .fold(range.clone())
                            .map(|x| x.0)
                            .unwrap_or_else(Default::default);
                        println!(
                            "\tFold (range = {:?}) -> (expected = {}, result = {})",
                            &range, expected, result
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
    fn test_mul_random() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(8, 16);
            let mut a = iter::repeat_with(|| rng.gen_range::<u128, _, _>(1, 256))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a.iter().map(|&x| Mul(x)).collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=69 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.gen_range(1, 256);

                        a[i] = x;
                        seg.set(i, Mul(x));

                        println!("\tSet (i = {}, x = {}) -> a = {:?}", i, x, &a);
                    }
                    // Partition point
                    70..=84 => {
                        let start = rng.gen_range(0, n);
                        let value = rng.gen_range(0u128, 100000);

                        let mut now = 1;
                        let mut i = start;
                        while i < n && (now * a[i]) <= value {
                            now *= a[i];
                            i += 1;
                        }

                        let expected = i;
                        let result = seg.partition_point(start, |&Mul(x)| x <= value);

                        println!(
                            "\tLower bound (start = {}, value = {}) -> (expected = {}, result = {})",
                            start, value, expected, result
                        );
                        assert_eq!(expected, result);
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let expected = a[range.clone()].iter().product::<u128>();
                        let result = seg
                            .fold(range.clone())
                            .map(|x| x.0)
                            .unwrap_or_else(Default::default);
                        println!(
                            "\tFold (range = {:?}) -> (expected = {}, result = {})",
                            &range, expected, result
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
    fn test_min_random() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(32, 64);
            let mut a = iter::repeat_with(|| rng.gen_range(-99, 100))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a.iter().map(|&x| Min(x)).collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=84 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.gen_range(0, 100);

                        a[i] = x;
                        seg.set(i, Min(x));

                        println!("\tSet (i = {}, x = {}) -> a = {:?}", i, x, &a);
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let expected = a[range.clone()].iter().min().copied();
                        let result = seg.fold(range.clone()).map(|x| x.0);
                        println!(
                            "\tFold (range = {:?}) -> (expected = {:?}, result = {:?})",
                            &range, expected, result
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
    fn test_max_random() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(32, 64);
            let mut a = iter::repeat_with(|| rng.gen_range(-99, 100))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a.iter().map(|&x| Max(x)).collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=84 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.gen_range(0, 100);

                        a[i] = x;
                        seg.set(i, Max(x));

                        println!("\tSet (i = {}, x = {}) -> a = {:?}", i, x, &a);
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let expected = a[range.clone()].iter().max().copied();
                        let result = seg.fold(range.clone()).map(|x| x.0);
                        println!(
                            "\tFold (range = {:?}) -> (expected = {:?}, result = {:?})",
                            &range, expected, result
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
                        seg.set(i, Inversion::from_bool(x));

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
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(32, 64);
            let mut a = iter::repeat_with(|| rng.gen_range(-99, 100))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a.iter().map(|&x| First(x)).collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=84 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.gen_range(0, 100);

                        a[i] = x;
                        seg.set(i, First(x));

                        println!("\tSet (i = {}, x = {}) -> a = {:?}", i, x, &a);
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let expected = if range.start == range.end {
                            None
                        } else {
                            Some(a[range.start])
                        };
                        let result = seg.fold(range.clone()).map(|x| x.0);
                        println!(
                            "\tFold (range = {:?}) -> (expected = {:?}, result = {:?})",
                            &range, expected, result
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
    fn test_second_random() {
        use rand::prelude::*;
        let mut rng: rand::rngs::StdRng = rand::SeedableRng::seed_from_u64(42);

        for _ in 0..NUMBER_OF_TEST_CASES {
            let n = rng.gen_range(32, 64);
            let mut a = iter::repeat_with(|| rng.gen_range(-99, 100))
                .take(n)
                .collect::<Vec<_>>();
            let mut seg = a.iter().map(|&x| Second(x)).collect::<Segtree<_>>();

            println!(" === Created an instance === ");
            println!("n = {}, a = {:?}", n, &a);

            for _ in 0..NUMBER_OF_QUERIES {
                let command = rng.gen_range(0, 100);
                match command {
                    // Update
                    0..=84 => {
                        let i = rng.gen_range(0, n);
                        let x = rng.gen_range(0, 100);

                        a[i] = x;
                        seg.set(i, Second(x));

                        println!("\tSet (i = {}, x = {}) -> a = {:?}", i, x, &a);
                    }
                    // Fold
                    85..=100 => {
                        let range = gen_valid_range(&mut rng, n);
                        let expected = if range.start == range.end {
                            None
                        } else {
                            Some(a[range.end - 1])
                        };
                        let result = seg.fold(range.clone()).map(|x| x.0);
                        println!(
                            "\tFold (range = {:?}) -> (expected = {:?}, result = {:?})",
                            &range, expected, result
                        );
                        assert_eq!(&expected, &result);
                    }
                    _ => unreachable!(),
                }
            }
            println!();
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
