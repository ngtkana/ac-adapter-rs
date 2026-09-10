//! 区間 chmin・chmax・区間加算と、区間 min・max・sum 取得に対応する Segment Tree Beats。
//!
//! 各ノードに区間の最大値上位 2 種類（`max[0]` が最大値、`max[1]` はそれ未満で最大の値）とその個数、
//! 最小値についても対称な情報、および区間和を持たせる。区間 chmin（$a_i \gets \min(a_i, x)$）は、
//! 最大値が $x$ 以下ならその区間は変化しないので打ち切り、２番目に大きい値が $x$ 未満なら
//! 最大値だけを $x$ に書き換えて総和を差分更新するだけで済み、それ以外の場合だけ子に再帰する。
//! chmax・区間加算も対称に実装する。再帰するたびに区間内の相異なる値の個数が真に減ることを用いた
//! ならし解析（potential 論法）により、これらの更新はならし $O(\log^2 n)$ で処理できる。
//!
//! # 仕様
//!
//! 半開区間 $[l, r)$ に対する操作。
//!
//! - `change_min`: $a_i \gets \min(a_i, x)$（chmin）
//! - `change_max`: $a_i \gets \max(a_i, x)$（chmax）
//! - `range_add`: $a_i \gets a_i + x$（区間加算）
//! - `query_min`, `query_max`, `query_sum`: 区間の最小値・最大値・総和の取得
//!
//! 要素の型は [`Value`] トレイトを実装すること（符号付き・符号なし整数型に実装済み）。
//!
//! # 例
//!
//! ```
//! use lazy_segbeats::Segbeats;
//!
//! let mut segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
//! segbeats.change_min(1..4, 3); // [1, 3, 2, 3, 5]
//! assert_eq!(segbeats.query_sum(..), 1 + 3 + 2 + 3 + 5);
//! segbeats.range_add(0..2, 10); // [11, 13, 2, 3, 5]
//! assert_eq!(segbeats.query_max(..), 13);
//! ```
//!
//! # 計算量
//!
//! - 構築（[`Segbeats::new`]）: $O(n)$
//! - chmin・chmax・区間加算（[`Segbeats::change_min`], [`Segbeats::change_max`], [`Segbeats::range_add`]）: ならし $O(\log^2 n)$
//! - 区間 min・max・sum（[`Segbeats::query_min`], [`Segbeats::query_max`], [`Segbeats::query_sum`]）: $O(\log n)$

use std::cell::RefCell;
use std::fmt::Debug;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;
use std::ops::Sub;
use std::ops::SubAssign;

/// `RangeBounds` を半開区間 $[l, r)$ に変換する。
///
/// # 例
///
/// ```
/// use lazy_segbeats::open;
/// assert_eq!(open(10, 2..5), 2..5);
/// assert_eq!(open(10, ..), 0..10);
/// assert_eq!(open(10, 2..=5), 2..6);
/// ```
pub fn open(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    use Bound::Excluded;
    use Bound::Included;
    use Bound::Unbounded;
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

/// chmin・chmax・区間加算と、区間 min・max・sum 取得に対応する Segment Tree Beats。
///
/// 各ノードが最大値上位 2 種類・最小値下位 2 種類とその個数、区間和、区間加算の遅延値を持つ。
/// 仕組みの詳細はモジュールドキュメントを参照。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Segbeats<T> {
    len: usize,
    lg: u32,
    table: RefCell<Vec<Node<T>>>,
}

impl<T: Value> Segbeats<T> {
    /// 配列から構築する。
    ///
    /// # 計算量
    ///
    /// $O(n)$
    ///
    /// # 例
    ///
    /// ```
    /// use lazy_segbeats::Segbeats;
    /// let segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
    /// assert_eq!(segbeats.query_sum(..), 20);
    /// ```
    pub fn new(src: &[T]) -> Self {
        let len = src.len().next_power_of_two();
        let lg = len.trailing_zeros();
        let mut table = vec![Node::new(); 2 * len];
        for (i, &x) in src.iter().enumerate() {
            table[len + i] = Node::single(x);
        }
        (1..len)
            .rev()
            .for_each(|i| table[i] = Node::merge(table[2 * i], table[2 * i + 1]));
        Self {
            len,
            lg,
            table: RefCell::new(table),
        }
    }

    /// 区間 $[l, r)$ を chmin する: $a_i \gets \min(a_i, x)$。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log^2 n)$
    ///
    /// # 例
    ///
    /// ```
    /// use lazy_segbeats::Segbeats;
    /// let mut segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
    /// segbeats.change_min(1..4, 3);
    /// assert_eq!(segbeats.query_sum(..), 1 + 3 + 2 + 3 + 5);
    /// ```
    pub fn change_min(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMin<T>>(range, x);
    }

    /// 区間 $[l, r)$ を chmax する: $a_i \gets \max(a_i, x)$。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log^2 n)$
    ///
    /// # 例
    ///
    /// ```
    /// use lazy_segbeats::Segbeats;
    /// let mut segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
    /// segbeats.change_max(0..3, 3);
    /// assert_eq!(segbeats.query_sum(..), 3 + 4 + 3 + 8 + 5);
    /// ```
    pub fn change_max(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMax<T>>(range, x);
    }

    /// 区間 $[l, r)$ に $x$ を加算する: $a_i \gets a_i + x$。
    ///
    /// # 計算量
    ///
    /// ならし $O(\log^2 n)$
    ///
    /// # 例
    ///
    /// ```
    /// use lazy_segbeats::Segbeats;
    /// let mut segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
    /// segbeats.range_add(0..2, 10);
    /// assert_eq!(segbeats.query_sum(..), 11 + 14 + 2 + 8 + 5);
    /// ```
    pub fn range_add(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<RangeAdd<T>>(range, x);
    }

    /// 区間 $[l, r)$ の最小値 $\min_{i \in [l, r)} a_i$ を返す。
    ///
    /// # 計算量
    ///
    /// $O(\log n)$
    ///
    /// # 例
    ///
    /// ```
    /// use lazy_segbeats::Segbeats;
    /// let segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
    /// assert_eq!(segbeats.query_min(1..4), 2);
    /// ```
    pub fn query_min(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMin<T>>(range, ())
    }

    /// 区間 $[l, r)$ の最大値 $\max_{i \in [l, r)} a_i$ を返す。
    ///
    /// # 計算量
    ///
    /// $O(\log n)$
    ///
    /// # 例
    ///
    /// ```
    /// use lazy_segbeats::Segbeats;
    /// let segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
    /// assert_eq!(segbeats.query_max(1..4), 8);
    /// ```
    pub fn query_max(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMax<T>>(range, ())
    }

    /// 区間 $[l, r)$ の総和 $\sum_{i \in [l, r)} a_i$ を返す。
    ///
    /// # 計算量
    ///
    /// $O(\log n)$
    ///
    /// # 例
    ///
    /// ```
    /// use lazy_segbeats::Segbeats;
    /// let segbeats = Segbeats::new(&[1_i64, 4, 2, 8, 5]);
    /// assert_eq!(segbeats.query_sum(1..4), 4 + 2 + 8);
    /// ```
    pub fn query_sum(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QuerySum<T>>(range, ())
    }

    fn push(&self, i: usize) {
        let lz = std::mem::replace(&mut self.table.borrow_mut()[i].lazy_add, T::ZERO);
        if lz != T::ZERO {
            (2 * i..2 * i + 2).for_each(|j| self.table.borrow_mut()[j].add(lz));
        }

        let x = self.table.borrow()[i].max[0];
        for j in 2 * i..2 * i + 2 {
            let node = self.table.borrow()[j];
            if node.max[1] < x && x < node.max[0] {
                self.table.borrow_mut()[j].change_min(x);
            }
        }
        let x = self.table.borrow()[i].min[0];
        for j in 2 * i..2 * i + 2 {
            let node = self.table.borrow()[j];
            if node.min[0] < x && x < node.min[1] {
                self.table.borrow_mut()[j].change_max(x);
            }
        }
    }

    fn dfs<D: Dfs<Value = T>>(&self, range: Range<usize>, x: D::Param) -> D::Output {
        self.dfs_impl::<D>(1, 0..self.len, range, x)
    }

    fn dfs_impl<D: Dfs<Value = T>>(
        &self,
        root: usize,
        subtree: Range<usize>,
        range: Range<usize>,
        x: D::Param,
    ) -> D::Output {
        if disjoint(&range, &subtree) || D::break_condition(self.table.borrow()[root], x) {
            D::identity()
        } else if contains(&range, &subtree) && D::tag_condition(self.table.borrow()[root], x) {
            D::tag(&mut self.table.borrow_mut()[root], x);
            D::extract(self.table.borrow()[root])
        } else {
            let Range { start, end } = subtree;
            let mid = usize::midpoint(start, end);
            self.push(root);
            let l = self.dfs_impl::<D>(root * 2, start..mid, range.clone(), x);
            let r = self.dfs_impl::<D>(root * 2 + 1, mid..end, range, x);
            self.update(root);
            D::merge(l, r)
        }
    }

    fn update(&self, i: usize) {
        let x = Node::merge(self.table.borrow()[2 * i], self.table.borrow()[2 * i + 1]);
        self.table.borrow_mut()[i] = x;
    }
}

trait Dfs {
    type Value: Value;
    type Param: Copy + Debug;
    type Output: Debug;
    fn identity() -> Self::Output;
    fn break_condition(_node: Node<Self::Value>, _x: Self::Param) -> bool {
        false
    }
    fn tag_condition(_node: Node<Self::Value>, _x: Self::Param) -> bool {
        true
    }
    fn tag(_node: &mut Node<Self::Value>, _x: Self::Param) {}
    fn merge(left: Self::Output, right: Self::Output) -> Self::Output;
    fn extract(node: Node<Self::Value>) -> Self::Output;
}
struct ChangeMin<T>(std::marker::PhantomData<T>);
impl<T: Value> Dfs for ChangeMin<T> {
    type Output = ();
    type Param = T;
    type Value = T;

    fn identity() -> Self::Output {}

    fn break_condition(node: Node<T>, x: Self::Param) -> bool {
        node.max[0] <= x
    }

    fn tag_condition(node: Node<T>, x: Self::Param) -> bool {
        node.max[1] < x
    }

    fn tag(node: &mut Node<Self::Value>, x: Self::Param) {
        node.change_min(x);
    }

    fn merge((): (), (): ()) {}

    fn extract(_node: Node<T>) {}
}
struct ChangeMax<T>(std::marker::PhantomData<T>);
impl<T: Value> Dfs for ChangeMax<T> {
    type Output = ();
    type Param = T;
    type Value = T;

    fn identity() -> Self::Output {}

    fn break_condition(node: Node<T>, x: Self::Param) -> bool {
        x <= node.min[0]
    }

    fn tag_condition(node: Node<T>, x: Self::Param) -> bool {
        x < node.min[1]
    }

    fn tag(node: &mut Node<Self::Value>, x: Self::Param) {
        node.change_max(x);
    }

    fn merge((): (), (): ()) {}

    fn extract(_node: Node<T>) {}
}
struct RangeAdd<T>(std::marker::PhantomData<T>);
impl<T: Value> Dfs for RangeAdd<T> {
    type Output = ();
    type Param = T;
    type Value = T;

    fn identity() -> Self::Output {}

    fn tag(node: &mut Node<Self::Value>, x: Self::Param) {
        node.add(x);
    }

    fn merge((): (), (): ()) {}

    fn extract(_node: Node<T>) {}
}
struct QueryMin<T>(std::marker::PhantomData<T>);
impl<T: Value> Dfs for QueryMin<T> {
    type Output = T;
    type Param = ();
    type Value = T;

    fn identity() -> Self::Output {
        T::max_value()
    }

    fn merge(left: T, right: T) -> T {
        left.min(right)
    }

    fn extract(node: Node<T>) -> T {
        node.min[0]
    }
}
struct QueryMax<T>(std::marker::PhantomData<T>);
impl<T: Value> Dfs for QueryMax<T> {
    type Output = T;
    type Param = ();
    type Value = T;

    fn identity() -> Self::Output {
        T::min_value()
    }

    fn merge(left: T, right: T) -> T {
        left.max(right)
    }

    fn extract(node: Node<T>) -> T {
        node.max[0]
    }
}
struct QuerySum<T>(std::marker::PhantomData<T>);
impl<T: Value> Dfs for QuerySum<T> {
    type Output = T;
    type Param = ();
    type Value = T;

    fn identity() -> Self::Output {
        T::ZERO
    }

    fn merge(left: T, right: T) -> T {
        left + right
    }

    fn extract(node: Node<T>) -> T {
        node.sum
    }
}

#[derive(Debug, Clone, PartialEq, Copy, Eq)]
struct Node<T> {
    max: [T; 2],
    c_max: u32,
    min: [T; 2],
    c_min: u32,
    sum: T,
    lazy_add: T,
    len: u32,
}
impl<T: Value> Node<T> {
    fn new() -> Self {
        Self {
            max: [T::min_value(), T::min_value()],
            c_max: 0,
            min: [T::max_value(), T::max_value()],
            c_min: 0,
            sum: T::ZERO,
            lazy_add: T::ZERO,
            len: 0,
        }
    }

    fn single(x: T) -> Self {
        Self {
            max: [x, T::min_value()],
            c_max: 1,
            min: [x, T::max_value()],
            c_min: 1,
            sum: x,
            lazy_add: T::ZERO,
            len: 1,
        }
    }

    fn add(&mut self, x: T) {
        self.max
            .iter_mut()
            .filter(|y| **y != T::min_value())
            .for_each(|y| *y += x);
        self.min
            .iter_mut()
            .filter(|y| **y != T::max_value())
            .for_each(|y| *y += x);
        self.sum += x.mul_u32(self.len);
        self.lazy_add += x;
    }

    fn change_min(&mut self, x: T) {
        assert!(self.max[1] < x && x < self.max[0]);
        self.sum += (x - self.max[0]).mul_u32(self.c_max);
        for i in 0..2 {
            if self.min[i] == self.max[0] {
                self.min[i] = x;
            }
        }
        self.max[0] = x;
    }

    fn change_max(&mut self, x: T) {
        assert!(self.min[0] < x && x < self.min[1]);
        self.sum += (x - self.min[0]).mul_u32(self.c_min);
        for i in 0..2 {
            if self.max[i] == self.min[0] {
                self.max[i] = x;
            }
        }
        self.min[0] = x;
    }

    fn merge(left: Self, right: Self) -> Self {
        use std::cmp::Ordering;
        let (max, c_max) = {
            let [a, b] = left.max;
            let [c, d] = right.max;
            match a.cmp(&c) {
                Ordering::Equal => ([a, c.max(d)], left.c_max + right.c_max),
                Ordering::Greater => ([a, b.max(c)], left.c_max),
                Ordering::Less => ([c, a.max(d)], right.c_max),
            }
        };
        let (min, c_min) = {
            let [a, b] = left.min;
            let [c, d] = right.min;
            match a.cmp(&c) {
                Ordering::Equal => ([a, c.min(d)], left.c_min + right.c_min),
                Ordering::Less => ([a, b.min(c)], left.c_min),
                Ordering::Greater => ([c, a.min(d)], right.c_min),
            }
        };
        Self {
            max,
            c_max,
            min,
            c_min,
            sum: left.sum + right.sum,
            len: left.len + right.len,
            lazy_add: T::ZERO,
        }
    }
}

fn contains(i: &Range<usize>, j: &Range<usize>) -> bool {
    i.start <= j.start && j.end <= i.end
}
fn disjoint(i: &Range<usize>, j: &Range<usize>) -> bool {
    i.end <= j.start || j.end <= i.start
}

/// [`Segbeats`] の要素として使える型の要件。
///
/// 全順序（`Ord`）と加減算（`Add`/`Sub` とその代入版）を持つことに加え、
/// 番兵として使う最大値・最小値、加法の単位元、`u32` 倍を提供する。
/// 符号付き・符号なし整数型（`u8` から `u128`, `usize`, `i8` から `i128`, `isize`）に実装済み。
pub trait Value:
    Sized
    + std::fmt::Debug
    + Copy
    + Ord
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
{
    /// 番兵として使う最大値（`min` 配列の空きスロットや chmin の初期打ち切り値に使用）。
    fn max_value() -> Self;
    /// 番兵として使う最小値（`max` 配列の空きスロットや chmax の初期打ち切り値に使用）。
    fn min_value() -> Self;
    /// 加法の単位元 $0$。
    const ZERO: Self;
    /// $u32$ 倍を返す: $\mathrm{self} \times x$（区間和の差分更新に使用）。
    fn mul_u32(&self, x: u32) -> Self;
}
macro_rules! impl_value {
    {$($ty:ident;)*} => {
        $(
            impl Value for $ty {
                fn min_value() -> Self {
                    $ty::MIN
                }
                fn max_value() -> Self {
                    $ty::MAX
                }
                const ZERO: Self = 0;
                fn mul_u32(&self, x: u32) -> Self {
                    self * (x as $ty)
                }
            }
        )*
    }
}
impl_value! {
    u8; u16; u32; u64; u128; usize;
    i8; i16; i32; i64; i128; isize;
}

// #[cfg(test)]
// mod tests {
//     mod impl_query;
//     mod queries;
//     mod vector;
//
//     use super::Segbeats;
//     use queries::{ChangeMax, ChangeMin, QueryMax, QueryMin, QuerySum, RangeAdd};
//     use query_test::{impl_help, Config};
//     use rand::prelude::*;
//     use vector::{Len, Value, Vector};
//
//     type Tester<T, G> = query_test::Tester<StdRng, Vector<T>, Segbeats<T>, G>;
//
//     #[test]
//     fn test_i64() {
//         #[derive(Debug, Clone, PartialEq, Copy, Eq)]
//         struct G {}
//         impl_help! {Len, |rng| rng.gen_range(1..100); }
//         impl_help! {Value<i64>, |rng| rng.gen_range(-1_000_000_000, 1_000_000_000); }
//
//         let mut tester = Tester::<i64, G>::new(StdRng::seed_from_u64(42), Config::Short);
//         for _ in 0..10 {
//             tester.initialize();
//             for _ in 0..100 {
//                 let command = tester.rng_mut().gen_range(0..6);
//                 match command {
//                     0 => tester.mutate::<ChangeMin<_>>(),
//                     1 => tester.mutate::<ChangeMax<_>>(),
//                     2 => tester.mutate::<RangeAdd<_>>(),
//                     3 => tester.compare::<QueryMin<_>>(),
//                     4 => tester.compare::<QueryMax<_>>(),
//                     5 => tester.compare::<QuerySum<_>>(),
//                     _ => unreachable!(),
//                 }
//             }
//         }
//     }
// }
