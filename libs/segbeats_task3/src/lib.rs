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

#[derive(Clone, PartialEq, Eq)]
pub struct Segbeats<T> {
    len: usize,
    lg: u32,
    table: RefCell<Vec<Node<T>>>,
}

impl<T: Elm> Debug for Segbeats<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Segbeats")?;
        self.table
            .borrow_mut()
            .iter()
            .try_for_each(|node| writeln!(f, "{:?}", &node))
    }
}

impl<T: Elm> Segbeats<T> {
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

    pub fn change_min(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMin<T>>(range, x);
    }

    pub fn change_max(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMax<T>>(range, x);
    }

    pub fn range_add(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<RangeAdd<T>>(range, x);
    }

    pub fn query_min(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMin<T>>(range, ())
    }

    pub fn query_max(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMax<T>>(range, ())
    }

    pub fn query_sum(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QuerySum<T>>(range, ())
    }

    pub fn count_changes(&self, range: impl RangeBounds<usize>) -> u64 {
        let range = open(self.len, range);
        self.dfs::<CountChanges<T>>(range, ())
    }

    fn push(&self, i: usize) {
        let node = self.table.borrow()[i];
        let max = node.max[0];
        let min = node.min[0];
        let lazy_add = replace(&mut self.table.borrow_mut()[i].lazy_add, T::zero());
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
            let mid = (start + end) / 2;
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
    type Value: Elm;
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
impl<T: Elm> Dfs for ChangeMin<T> {
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
impl<T: Elm> Dfs for ChangeMax<T> {
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
impl<T: Elm> Dfs for RangeAdd<T> {
    type Output = ();
    type Param = T;
    type Value = T;

    fn identity() -> Self::Output {}

    fn tag(node: &mut Node<Self::Value>, x: Self::Param) {
        if x == T::zero() {
            node.add(x, 0);
        } else {
            node.add(x, 1);
        }
    }

    fn merge((): (), (): ()) {}

    fn extract(_node: Node<T>) {}
}
struct QueryMin<T>(std::marker::PhantomData<T>);
impl<T: Elm> Dfs for QueryMin<T> {
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
impl<T: Elm> Dfs for QueryMax<T> {
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
impl<T: Elm> Dfs for QuerySum<T> {
    type Output = T;
    type Param = ();
    type Value = T;

    fn identity() -> Self::Output {
        T::zero()
    }

    fn merge(left: T, right: T) -> T {
        left + right
    }

    fn extract(node: Node<T>) -> T {
        node.sum
    }
}
struct CountChanges<T>(std::marker::PhantomData<T>);
impl<T: Elm> Dfs for CountChanges<T> {
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
impl<T: Elm> Node<T> {
    fn new() -> Self {
        Self {
            max: [T::min_value(); 2],
            c_max: 0,
            min: [T::max_value(); 2],
            c_min: 0,
            sum: T::zero(),
            len: 0,
            lazy_add: T::zero(),
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
            lazy_add: T::zero(),
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
        assert_eq!(node.lazy_add, T::zero());
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
            lazy_add: T::zero(),
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

pub trait Elm:
    Sized
    + std::fmt::Debug
    + Copy
    + Ord
    + Add<Output = Self>
    + AddAssign
    + Sub<Output = Self>
    + SubAssign
{
    fn max_value() -> Self;
    fn min_value() -> Self;
    fn zero() -> Self;
    fn mul_u32(&self, x: u32) -> Self;
}
macro_rules! impl_elm {
    {$($ty:ident;)*} => {
        $(
            impl Elm for $ty {
                fn min_value() -> Self {
                    std::$ty::MIN
                }
                fn max_value() -> Self {
                    std::$ty::MAX
                }
                fn zero() -> Self {
                    0
                }
                fn mul_u32(&self, x: u32) -> Self {
                    self * (x as $ty)
                }
            }
        )*
    }
}
impl_elm! {
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
