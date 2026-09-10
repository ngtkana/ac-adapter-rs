//! 区間 chmin・chmax と区間 min・max・sum を償却 $O(\log^2 n)$ で処理する Segment Tree Beats。
//!
//! 各ノードは区間内の最大値・最小値をそれぞれ上位 2 段（値とその個数）と総和で持つ。
//! chmin($x$) は「更新後も上位 2 段の関係が崩れない」区間、つまり 2 番目に大きい値が $x$ 未満の
//! 区間にだけタグとしてその場で適用し、それ以外の区間は子に降りて再帰する。区間内の相異なる値の
//! 個数は再帰のたびに単調に減るため、再帰が発生する回数は更新全体を通して償却 $O(\log n)$ 回に
//! 抑えられることが知られている。
//!
//! # 仕様
//!
//! 数列 $a_0, \ldots, a_{n-1}$ を管理する。`Segbeats` が本体で、次の操作を提供する。
//!
//! - `new(&[T])`: 初期化
//! - `change_min(range, x)`: $i \in \text{range}$ に対し $a_i \gets \min(a_i, x)$
//! - `change_max(range, x)`: $i \in \text{range}$ に対し $a_i \gets \max(a_i, x)$
//! - `query_min(range)`, `query_max(range)`: $\min_{i \in \text{range}} a_i$, $\max_{i \in \text{range}} a_i$
//! - `query_sum(range)`: $\sum_{i \in \text{range}} a_i$
//!
//! `range` は `usize` の任意の半開区間（`..`, `a..b`, `a..=b` など）。
//!
//! # 例
//!
//! ```
//! use segbeats::Segbeats;
//!
//! let mut sb = Segbeats::new(&[4, 2, 5, 1, 3]);
//! sb.change_min(1..4, 3); // [4, 2, 3, 1, 3]
//! assert_eq!(sb.query_max(..), 4);
//! assert_eq!(sb.query_sum(..), 4 + 2 + 3 + 1 + 3);
//!
//! sb.change_max(0..2, 3); // [4, 3, 3, 1, 3]
//! assert_eq!(sb.query_min(..), 1);
//! ```
//!
//! # 計算量
//!
//! - 構築（`Segbeats::new`）: $O(n)$
//! - `change_min`, `change_max`: 償却 $O(\log^2 n)$
//! - `query_min`, `query_max`, `query_sum`: $O(\log n)$

use std::cell::RefCell;
use std::fmt::Debug;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Bound;
use std::ops::Range;
use std::ops::RangeBounds;
use std::ops::Sub;
use std::ops::SubAssign;

/// `RangeBounds<usize>` を半開区間 `Range<usize>` に正規化する。境界の非包含側は `len` に丸める。
///
/// # 例
///
/// ```
/// use segbeats::open;
/// assert_eq!(open(10, 2..5), 2..5);
/// assert_eq!(open(10, ..), 0..10);
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

/// 数列に区間 chmin・chmax・区間 min/max/sum を提供するデータ構造。詳細は[クレートの説明](crate)を参照。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Segbeats<T> {
    len: usize,
    lg: u32,
    table: RefCell<Vec<Node<T>>>,
}

impl<T: Value> Segbeats<T> {
    /// 数列 $a_0, \ldots, a_{n-1}$ から構築する。$O(n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use segbeats::Segbeats;
    /// let sb = Segbeats::new(&[3, 1, 4]);
    /// assert_eq!(sb.query_sum(..), 8);
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

    /// $i \in \text{range}$ に対し $a_i \gets \min(a_i, x)$ を適用する。償却 $O(\log^2 n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use segbeats::Segbeats;
    /// let mut sb = Segbeats::new(&[4, 2, 5]);
    /// sb.change_min(.., 3);
    /// assert_eq!(sb.query_max(..), 3); // 4, 5 は 3 に切り下げ、2 はそのまま
    /// ```
    pub fn change_min(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMin<T>>(range, x);
    }

    /// $i \in \text{range}$ に対し $a_i \gets \max(a_i, x)$ を適用する。償却 $O(\log^2 n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use segbeats::Segbeats;
    /// let mut sb = Segbeats::new(&[4, 2, 5]);
    /// sb.change_max(.., 3);
    /// assert_eq!(sb.query_min(..), 3); // 2 は 3 に切り上げ、4, 5 はそのまま
    /// ```
    pub fn change_max(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMax<T>>(range, x);
    }

    /// $\min_{i \in \text{range}} a_i$ を返す。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use segbeats::Segbeats;
    /// let sb = Segbeats::new(&[4, 2, 5]);
    /// assert_eq!(sb.query_min(..), 2);
    /// ```
    pub fn query_min(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMin<T>>(range, ())
    }

    /// $\max_{i \in \text{range}} a_i$ を返す。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use segbeats::Segbeats;
    /// let sb = Segbeats::new(&[4, 2, 5]);
    /// assert_eq!(sb.query_max(..), 5);
    /// ```
    pub fn query_max(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMax<T>>(range, ())
    }

    /// $\sum_{i \in \text{range}} a_i$ を返す。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// use segbeats::Segbeats;
    /// let sb = Segbeats::new(&[4, 2, 5]);
    /// assert_eq!(sb.query_sum(..), 11);
    /// ```
    pub fn query_sum(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QuerySum<T>>(range, ())
    }

    fn push(&self, i: usize) {
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
}
impl<T: Value> Node<T> {
    fn new() -> Self {
        Self {
            max: [T::min_value(), T::min_value()],
            c_max: 0,
            min: [T::max_value(), T::max_value()],
            c_min: 0,
            sum: T::ZERO,
        }
    }

    fn single(x: T) -> Self {
        Self {
            max: [x, T::min_value()],
            c_max: 1,
            min: [x, T::max_value()],
            c_min: 1,
            sum: x,
        }
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
        Self {
            max,
            c_max,
            min,
            c_min,
            sum: left.sum + right.sum,
        }
    }
}

fn contains(i: &Range<usize>, j: &Range<usize>) -> bool {
    i.start <= j.start && j.end <= i.end
}
fn disjoint(i: &Range<usize>, j: &Range<usize>) -> bool {
    i.end <= j.start || j.end <= i.start
}

/// `Segbeats` が扱える要素型が満たすべき性質。整数型に実装済み。
///
/// # 仕様
///
/// - `max_value()`, `min_value()`: 型の最大値・最小値
/// - `ZERO`: 加法の単位元 $0$
/// - `mul_u32(x)`: $\text{self} \times x$（`u32` との積、総和の更新に使用）
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
    /// 型の最大値。
    fn max_value() -> Self;
    /// 型の最小値。
    fn min_value() -> Self;
    /// 加法の単位元 $0$。
    const ZERO: Self;
    /// $\text{self} \times x$ を返す（`u32` との積）。
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
//     use queries::{ChangeMax, ChangeMin, QueryMax, QuerySum};
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
//                 let command = tester.rng_mut().gen_range(0..4);
//                 match command {
//                     0 => tester.mutate::<ChangeMin<_>>(),
//                     1 => tester.mutate::<ChangeMax<_>>(),
//                     2 => tester.compare::<QueryMax<_>>(),
//                     3 => tester.compare::<QuerySum<_>>(),
//                     _ => unreachable!(),
//                 }
//             }
//         }
//     }
// }
