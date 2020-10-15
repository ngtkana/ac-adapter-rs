use open::open;
use std::{
    cell::RefCell,
    fmt::Debug,
    ops::{Add, AddAssign, Range, RangeBounds, Sub, SubAssign},
};

#[derive(Debug, Clone, PartialEq)]
pub struct SegbeatsTask1<T> {
    len: usize,
    lg: u32,
    table: RefCell<Vec<Node<T>>>,
}

impl<T: Elm> SegbeatsTask1<T> {
    pub fn new(src: &[T]) -> Self {
        let len = src.len().next_power_of_two();
        let lg = len.trailing_zeros();
        let mut table = vec![Node::foo(); 2 * len];
        for (i, &x) in src.iter().enumerate() {
            table[len + i] = Node::new(x);
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
    pub fn change_min(&mut self, range: impl Clone + RangeBounds<usize>, x: T) {
        let range = open(self.len, range);
        self.dfs::<ChangeMin<T>>(range, x)
    }
    pub fn query_max(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QueryMax<T>>(range, ())
    }
    pub fn query_sum(&self, range: impl RangeBounds<usize>) -> T {
        let range = open(self.len, range);
        self.dfs::<QuerySum<T>>(range, ())
    }
    fn push(&self, i: usize) {
        let x = self.table.borrow()[i].max[0];
        for j in 2 * i..2 * i + 2 {
            let node = self.table.borrow()[j];
            if node.max[0] <= x {
            } else if node.max[1] < x {
                self.table.borrow_mut()[j].change_min(x);
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
        let x = Node::merge(self.table.borrow()[2 * i], self.table.borrow()[2 * i + 1]);
        self.table.borrow_mut()[i] = x;
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
    type Value = T;
    type Param = T;
    type Output = ();
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
    fn merge(_: (), _: ()) {}
    fn extract(_node: Node<T>) {}
}
struct QueryMax<T>(std::marker::PhantomData<T>);
impl<T: Elm> Dfs for QueryMax<T> {
    type Value = T;
    type Param = ();
    type Output = T;
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
    type Value = T;
    type Param = ();
    type Output = T;
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

#[derive(Debug, Clone, PartialEq, Copy, Eq)]
struct Node<T> {
    max: [T; 2],
    c_max: u32,
    sum: T,
}
impl<T: Elm> Node<T> {
    fn foo() -> Self {
        Node {
            max: [T::min_value(), T::min_value()],
            c_max: 0,
            sum: T::zero(),
        }
    }
    fn new(x: T) -> Self {
        Node {
            max: [x, T::min_value()],
            c_max: 1,
            sum: x,
        }
    }
    fn change_min(&mut self, x: T) {
        assert!(self.max[1] < x && x < self.max[0]);
        self.sum += (x - self.max[0]).mul_u32(self.c_max);
        self.max[0] = x;
    }
    fn merge(left: Node<T>, right: Node<T>) -> Self {
        use std::cmp::Ordering;
        let [a, b] = left.max;
        let [c, d] = right.max;
        let sum = left.sum + right.sum;
        match a.cmp(&c) {
            Ordering::Equal => Node {
                max: [a, c.max(d)],
                c_max: left.c_max + right.c_max,
                sum,
            },
            Ordering::Greater => Node {
                max: [a, b.max(c)],
                c_max: left.c_max,
                sum,
            },
            Ordering::Less => Node {
                max: [c, a.max(d)],
                c_max: right.c_max,
                sum,
            },
        }
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

#[cfg(test)]
mod tests {
    mod impl_query;
    mod queries;
    mod vector;

    use super::SegbeatsTask1;
    use queries::{ChangeMin, QueryMax, QuerySum};
    use query_test::{impl_help, Config};
    use rand::prelude::*;
    use vector::{Len, Value, Vector};

    type Tester<T, G> = query_test::Tester<StdRng, Vector<T>, SegbeatsTask1<T>, G>;

    #[test]
    fn test_i64() {
        #[derive(Debug, Clone, PartialEq, Copy, Eq)]
        struct G {}
        impl_help! {Len, |rng| rng.gen_range(1, 100); }
        impl_help! {Value<i64>, |rng| rng.gen_range(-1_000_000_000, 1_000_000_000); }

        let mut tester = Tester::<i64, G>::new(StdRng::seed_from_u64(42), Config::Short);
        for _ in 0..10 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 3);
                match command {
                    0 => tester.mutate::<ChangeMin<_>>(),
                    1 => tester.compare::<QueryMax<_>>(),
                    2 => tester.compare::<QuerySum<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
