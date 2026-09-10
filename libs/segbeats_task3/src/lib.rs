//! 区間 chmin・chmax・区間加算と、min・max・sum 取得を載せた Segment Tree Beats
//!
//! 各ノードに最大値とその個数・2 番目に大きい値、最小値とその個数・2 番目に小さい値、
//! 総和を持たせた完全二分木として実装する。区間 chmin（$x_i \gets \min(x_i, x)$）は、
//! ノードの最大値が $x$ 以下ならなにもせず、2 番目の値 $< x <$ 最大値のときだけ
//! 最大値のみを $x$ に張り替える（区間 chmax も対称に動く）。この操作は
//! ノード内の異なる値の種類数を単調に減らすため、区間加算を挟んでも
//! 償却 $O((n + q) \log^2 n)$ で動作することが保証される
//! （chmin と chmax を同時にサポートする、いわゆる Segment Tree Beats の
//! "Task 3" 相当）。
//!
//! # 仕様
//!
//! - 型: `Segbeats<T>`（`T: Value`。符号付き・符号なし整数型に実装済み）
//! - 構築: [`Segbeats::new`]`(&[T])`
//! - 更新（半開区間 `[l, r)`）
//!     - [`Segbeats::change_min`][]: $x_i \gets \min(x_i, x)$
//!     - [`Segbeats::change_max`][]: $x_i \gets \max(x_i, x)$
//!     - [`Segbeats::range_add`][]: $x_i \gets x_i + x$
//! - 取得（半開区間 `[l, r)`）
//!     - [`Segbeats::query_min`][]: $\min_i x_i$
//!     - [`Segbeats::query_max`][]: $\max_i x_i$
//!     - [`Segbeats::query_sum`][]: $\sum_i x_i$
//!     - [`Segbeats::count_changes`][]: 区間内で値が実際に書き換わった延べ回数
//!
//! # 例
//!
//! ```
//! use segbeats_task3::Segbeats;
//!
//! let mut segbeats = Segbeats::new(&[1, 4, 2, 8, 5]);
//! segbeats.change_min(1..4, 3); // [1, 3, 2, 3, 5]
//! assert_eq!(segbeats.query_max(..), 5);
//! assert_eq!(segbeats.query_sum(..), 1 + 3 + 2 + 3 + 5);
//! assert_eq!(segbeats.count_changes(..), 2); // 4→3, 8→3 の 2 件が書き換わった
//! ```
//!
//! # 計算量
//!
//! - 構築: $O(n)$
//! - 各更新・取得: 償却 $O(\log^2 n)$（chmin・chmax は最悪ではなく償却計算量）

use std::cell::RefCell;
use std::fmt::Debug;
use std::mem::replace;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;
use std::ops::Sub;
use std::ops::SubAssign;

/// `range` を長さ `len` の半開区間 `Range<usize>` に変換する。
///
/// # 例
///
/// ```
/// use segbeats_task3::open;
/// assert_eq!(open(5, ..3), 0..3);
/// assert_eq!(open(5, 2..), 2..5);
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

/// 区間 chmin・chmax・加算・min/max/sum 取得を載せたセグメント木。
///
/// 内部状態は [`RefCell`] に包んであり、取得系メソッド（`query_*`,
/// `count_changes`）も `&self` から遅延評価（push）と統計値の更新を行う。
#[doc(alias = "Segment Tree Beats")]
#[derive(Clone, PartialEq, Eq)]
pub struct Segbeats<T> {
    len: usize,
    lg: u32,
    table: RefCell<Vec<Node<T>>>,
}

impl<T: Value> Debug for Segbeats<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Segbeats")?;
        self.table
            .borrow_mut()
            .iter()
            .try_for_each(|node| writeln!(f, "{:?}", &node))
    }
}

impl<T: Value> Segbeats<T> {
    /// 初期配列から構築する。
    ///
    /// 内部長は `src.len()` 以上最小の 2 冪に拡張し、余った要素は
    /// 演算結果に影響しない値で埋める。
    ///
    /// # 計算量
    ///
    /// $O(n)$
    pub fn new(src: &[T]) -> Self {
        let len = src.len().next_power_of_two();
        let lg = len.trailing_zeros();
        let mut table = vec![Node::new(); 2 * len];
        for (i, &x) in src.iter().enumerate() {
            table[len + i] = Node::single(x);
        }
        (1..len).rev().for_each(|i| {
            let x = table[2 * i];
            let y = table[2 * i + 1];
            Node::merge(&mut table[i], x, y);
        });
        Self {
            len,
            lg,
            table: RefCell::new(table),
        }
    }

    /// 区間 $[l, r)$ を chmin で更新する：$x_i \gets \min(x_i, x)$。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log^2 n)$
    pub fn change_min(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMin<T>>(range, x);
    }

    /// 区間 $[l, r)$ を chmax で更新する：$x_i \gets \max(x_i, x)$。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log^2 n)$
    pub fn change_max(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMax<T>>(range, x);
    }

    /// 区間 $[l, r)$ に $x$ を加算する：$x_i \gets x_i + x$。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log^2 n)$
    pub fn range_add(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<RangeAdd<T>>(range, x);
    }

    /// 区間 $[l, r)$ の最小値 $\min_i x_i$ を返す。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log^2 n)$
    pub fn query_min(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMin<T>>(range, ())
    }

    /// 区間 $[l, r)$ の最大値 $\max_i x_i$ を返す。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log^2 n)$
    pub fn query_max(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMax<T>>(range, ())
    }

    /// 区間 $[l, r)$ の総和 $\sum_i x_i$ を返す。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log^2 n)$
    pub fn query_sum(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QuerySum<T>>(range, ())
    }

    /// 区間 $[l, r)$ 内で、chmin・chmax・非ゼロ加算により値が実際に
    /// 書き換わった延べ回数を返す。
    ///
    /// 各要素について、構築後に値が変化した回数（chmin・chmax は値が
    /// 変わらなければ数えない。加算は $x \neq 0$ のときのみ 1 回と数える）を
    /// 区間内で合計する。
    ///
    /// # 計算量
    ///
    /// 償却 $O(\log^2 n)$
    pub fn count_changes(&self, range: impl RangeBounds<usize>) -> u64 {
        let range = open(self.len, range);
        self.dfs::<CountChanges<T>>(range, ())
    }

    fn push(&self, i: usize) {
        let node = self.table.borrow()[i];
        let max = node.max[0];
        let min = node.min[0];
        let lazy_add = replace(&mut self.table.borrow_mut()[i].lazy_add, T::ZERO);
        let lazy_add_count = replace(&mut self.table.borrow_mut()[i].lazy_add_count, 0);
        let lazy_change_min_count =
            replace(&mut self.table.borrow_mut()[i].lazy_change_min_count, 0);
        let lazy_change_max_count =
            replace(&mut self.table.borrow_mut()[i].lazy_change_max_count, 0);
        for j in 2 * i..2 * i + 2 {
            self.table.borrow_mut()[j].add(lazy_add, lazy_add_count);
        }
        if min == max {
            for j in 2 * i..2 * i + 2 {
                let child = &mut self.table.borrow_mut()[j];
                if child.min[0] == child.max[0] {
                    child.change_singleton(min, lazy_change_min_count + lazy_change_max_count);
                }
            }
        } else {
            for j in 2 * i..2 * i + 2 {
                let child = self.table.borrow()[j];
                assert!(child.max[1] < max);
                if max < child.max[0] {
                    self.table.borrow_mut()[j].change_min(max, lazy_change_min_count);
                }
            }
            for j in 2 * i..2 * i + 2 {
                let child = self.table.borrow()[j];
                assert!(min < child.min[1]);
                if child.min[0] < min {
                    self.table.borrow_mut()[j].change_max(min, lazy_change_max_count);
                }
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
        let x = self.table.borrow()[2 * i];
        let y = self.table.borrow()[2 * i + 1];
        Node::merge(&mut self.table.borrow_mut()[i], x, y);
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
        node.change_min(x, 1);
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
        node.change_max(x, 1);
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
        if x == T::ZERO {
            node.add(x, 0);
        } else {
            node.add(x, 1);
        }
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
struct CountChanges<T>(std::marker::PhantomData<T>);
impl<T: Value> Dfs for CountChanges<T> {
    type Output = u64;
    type Param = ();
    type Value = T;

    fn identity() -> Self::Output {
        0
    }

    fn merge(left: u64, right: u64) -> u64 {
        left + right
    }

    fn extract(node: Node<T>) -> u64 {
        node.change_count
    }
}

#[derive(Debug, Clone, PartialEq, Copy, Eq)]
struct Node<T> {
    max: [T; 2],
    c_max: u32,
    min: [T; 2],
    c_min: u32,
    sum: T,
    len: u32,
    lazy_add: T,
    change_count: u64,
    lazy_add_count: u32,
    lazy_change_min_count: u32,
    lazy_change_max_count: u32,
}
impl<T: Value> Node<T> {
    fn new() -> Self {
        Self {
            max: [T::min_value(); 2],
            c_max: 0,
            min: [T::max_value(); 2],
            c_min: 0,
            sum: T::ZERO,
            len: 0,
            lazy_add: T::ZERO,
            change_count: 0,
            lazy_add_count: 0,
            lazy_change_min_count: 0,
            lazy_change_max_count: 0,
        }
    }

    fn single(x: T) -> Self {
        Self {
            max: [x, T::min_value()],
            c_max: 1,
            min: [x, T::max_value()],
            c_min: 1,
            sum: x,
            len: 1,
            lazy_add: T::ZERO,
            change_count: 0,
            lazy_add_count: 0,
            lazy_change_min_count: 0,
            lazy_change_max_count: 0,
        }
    }

    fn change_min(&mut self, x: T, weight: u32) {
        assert!(self.max[1] < x && x < self.max[0]);
        self.sum += (x - self.max[0]).mul_u32(self.c_max);
        let orig_max = replace(&mut self.max[0], x);
        self.change_count += u64::from(self.c_max) * u64::from(weight);
        if orig_max == self.min[0] {
            self.min[0] = x;
        }
        if orig_max == self.min[1] {
            self.min[1] = x;
        }
        self.lazy_change_min_count += weight;
    }

    fn change_max(&mut self, x: T, weight: u32) {
        assert!(self.min[0] < x && x < self.min[1]);
        self.sum += (x - self.min[0]).mul_u32(self.c_min);
        let orig_min = replace(&mut self.min[0], x);
        self.change_count += u64::from(self.c_min) * u64::from(weight);
        if orig_min == self.max[0] {
            self.max[0] = x;
        }
        if orig_min == self.max[1] {
            self.max[1] = x;
        }
        self.lazy_change_max_count += weight;
    }

    fn add(&mut self, x: T, weight: u32) {
        self.max
            .iter_mut()
            .filter(|y| **y != T::min_value())
            .for_each(|y| *y += x);
        self.min
            .iter_mut()
            .filter(|y| **y != T::max_value())
            .for_each(|y| *y += x);
        self.sum += x.mul_u32(self.len);
        self.change_count += u64::from(self.len) * u64::from(weight);
        self.lazy_add += x;
        self.lazy_add_count += weight;
    }

    fn change_singleton(&mut self, x: T, weight: u32) {
        assert!(self.min[0] == self.max[0]);
        self.min[0] = x;
        self.max[0] = x;
        self.sum = x.mul_u32(self.len);
        self.change_count += u64::from(self.c_min) * u64::from(weight);
        self.lazy_change_min_count += weight; // weigt には和が渡ってきますから、片方に寄せておくと良いです。
    }

    fn merge(node: &mut Self, left: Self, right: Self) {
        use std::cmp::Ordering;
        assert_eq!(node.lazy_change_min_count, 0);
        assert_eq!(node.lazy_change_max_count, 0);
        assert_eq!(node.lazy_add_count, 0);
        assert_eq!(node.lazy_add, T::ZERO);
        let (max, c_max) = {
            let [a, b] = left.max;
            let [c, d] = right.max;
            match a.cmp(&c) {
                Ordering::Equal => ([a, b.max(d)], left.c_max + right.c_max),
                Ordering::Greater => ([a, b.max(c)], left.c_max),
                Ordering::Less => ([c, a.max(d)], right.c_max),
            }
        };
        let (min, c_min) = {
            let [a, b] = left.min;
            let [c, d] = right.min;
            match a.cmp(&c) {
                Ordering::Equal => ([a, b.min(d)], left.c_min + right.c_min),
                Ordering::Less => ([a, b.min(c)], left.c_min),
                Ordering::Greater => ([c, a.min(d)], right.c_min),
            }
        };
        *node = Self {
            max,
            c_max,
            min,
            c_min,
            change_count: left.change_count + right.change_count,
            len: left.len + right.len,
            sum: left.sum + right.sum,
            lazy_add: T::ZERO,
            lazy_add_count: 0,
            lazy_change_min_count: 0,
            lazy_change_max_count: 0,
        };
    }
}

fn contains(i: &Range<usize>, j: &Range<usize>) -> bool {
    i.start <= j.start && j.end <= i.end
}
fn disjoint(i: &Range<usize>, j: &Range<usize>) -> bool {
    i.end <= j.start || j.end <= i.start
}

/// [`Segbeats`] が扱える要素型が実装するトレイト。
///
/// 符号付き・符号なし整数型（`u8`〜`u128`, `usize`, `i8`〜`i128`, `isize`）に実装済み。
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
    /// 最大値。`query_min` の空区間に対する単位元として使う。
    fn max_value() -> Self;
    /// 最小値。`query_max` の空区間に対する単位元として使う。
    fn min_value() -> Self;
    /// 加法の単位元 $0$。
    const ZERO: Self;
    /// $u32$ 倍：$\text{self} \times x$。区間長分をまとめて加算する際に使う。
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
//     use queries::{ChangeMax, ChangeMin, CountChanges, QueryMax, QueryMin, QuerySum, RangeAdd};
//     use query_test::{impl_help, Config};
//     use rand::prelude::*;
//     use vector::{Len, Value, Vector};
//
//     type Tester<T, G> = query_test::Tester<StdRng, Vector<(T, u64)>, Segbeats<T>, G>;
//
//     #[test]
//     fn test_i64() {
//         #[derive(Debug, Clone, PartialEq, Copy, Eq)]
//         struct G {}
//         impl_help! {Len, |rng| rng.gen_range(1..1000); }
//         impl_help! {Value<i64>, |rng| rng.gen_range(-1_000_000, 1_000_000); }
//
//         let mut tester = Tester::<i64, G>::new(StdRng::seed_from_u64(42), Config::Short);
//         for _ in 0..20 {
//             tester.initialize();
//             for _ in 0..1000 {
//                 let command = tester.rng_mut().gen_range(0..7);
//                 match command {
//                     0 => tester.mutate::<ChangeMin<_>>(),
//                     1 => tester.mutate::<ChangeMax<_>>(),
//                     2 => tester.mutate::<RangeAdd<_>>(),
//                     3 => tester.compare::<QueryMin<_>>(),
//                     4 => tester.compare::<QueryMax<_>>(),
//                     5 => tester.compare::<QuerySum<_>>(),
//                     6 => tester.compare::<CountChanges>(),
//                     _ => unreachable!(),
//                 }
//             }
//         }
//     }
// }
