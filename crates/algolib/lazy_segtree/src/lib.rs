#![allow(dead_code, unused_variables, unused_imports)]
use alg_traits::{Action, Identity};
use std::{
    cell::RefCell,
    ops::{DerefMut, Range, RangeBounds},
};

#[derive(Debug, Clone, PartialEq)]
pub struct LazySegtree<A: Action, T: Identity> {
    lg: u32,
    len: usize,
    lazy: RefCell<Vec<A::Value>>,
    table: RefCell<Vec<T::Value>>,
}

impl<A, T> LazySegtree<A, T>
where
    A: Action<Point = T::Value> + Identity,
    T: Identity,
{
    fn from_slice(src: &[T::Value]) -> Self {
        let len = src.len();
        let mut table = vec![T::identity(); 2 * len];
        table[len..].clone_from_slice(src);
        for i in (1..len).rev() {
            table[i] = T::op(table[2 * i].clone(), table[2 * i + 1].clone());
        }
        Self {
            lg: len.next_power_of_two().trailing_zeros(),
            len,
            table: RefCell::new(table),
            lazy: RefCell::new(std::iter::repeat(A::identity()).take(len).collect()),
        }
    }

    fn set(&mut self, mut i: usize, x: T::Value) {
        i += self.len;
        for p in (1..=self.lg).rev() {
            self.push(i >> p);
        }
        self.table.borrow_mut()[i] = x;
        for p in 1..=self.lg {
            self.update(i >> p);
        }
    }

    fn fold(&self, range: impl RangeBounds<usize>) -> T::Value {
        let Range { mut start, mut end } = open::open(self.len, range);
        assert!(start <= end, "変な区間");
        assert!(end <= self.len, "範囲外");
        if start == end {
            T::identity()
        } else {
            start += self.len;
            end += self.len;
            for p in (1..=self.lg).rev() {
                if ((start >> p) << p) != start {
                    self.push(start >> p);
                }
                if ((end >> p) << p) != end {
                    self.push(end >> p);
                }
            }

            let mut left = T::identity();
            let mut right = T::identity();
            while start != end {
                if start % 2 == 1 {
                    T::op_left(&mut left, self.table.borrow()[start].clone());
                    start += 1;
                }
                if end % 2 == 1 {
                    end -= 1;
                    T::op_right(self.table.borrow()[end].clone(), &mut right);
                }
                start >>= 1;
                end >>= 1;
            }
            T::op(left, right)
        }
    }

    fn apply(&mut self, range: impl RangeBounds<usize>, a: A::Value) {
        let Range { mut start, mut end } = open::open(self.len, range);
        if start != end {
            start += self.len;
            end += self.len;
            for p in (1..=self.lg).rev() {
                if ((start >> p) << p) != start {
                    self.push(start >> p);
                }
                if ((end >> p) << p) != end {
                    self.push((end - 1) >> p);
                }
            }
            {
                let orig_start = start;
                let orig_end = end;
                while start != end {
                    if start % 2 == 1 {
                        self.apply_subtree(start, a.clone());
                        start += 1;
                    }
                    if end % 2 == 1 {
                        end -= 1;
                        self.apply_subtree(end, a.clone());
                    }
                    start >>= 1;
                    end >>= 1;
                }
                start = orig_start;
                end = orig_end;
            }
            for p in 1..=self.lg {
                if ((start >> p) << p) != start {
                    self.update(start >> p);
                }
                if ((end >> p) << p) != end {
                    self.update((end - 1) >> p);
                }
            }
        }
    }

    fn search_forward<R, F>(&self, range: R, pred: F) -> usize
    where
        R: RangeBounds<usize>,
        F: FnMut(&T::Value) -> bool,
    {
        todo!()
    }

    fn search_backward<R, F>(&self, range: R, pred: F) -> usize
    where
        R: RangeBounds<usize>,
        F: FnMut(&T::Value) -> bool,
    {
        todo!()
    }

    fn peek_one(&self, mut i: usize) -> T::Value {
        i += self.len;
        let mut x = self.table.borrow()[i].clone();
        for p in (1..=self.lg).rev() {
            A::act_assign(self.lazy.borrow()[i >> p].clone(), &mut x);
        }
        x
    }
    fn peek(&self) -> Vec<T::Value> {
        (0..self.len).map(|i| self.peek_one(i)).collect::<Vec<_>>()
    }
    fn update(&self, i: usize) {
        let x = T::op(
            self.table.borrow()[2 * i].clone(),
            self.table.borrow()[2 * i + 1].clone(),
        );
        self.table.borrow_mut()[i] = x;
    }
    fn push(&self, i: usize) {
        let x = std::mem::replace(&mut self.lazy.borrow_mut()[i], A::identity());
        self.apply_subtree(2 * i, x.clone());
        self.apply_subtree(2 * i + 1, x);
    }
    fn apply_subtree(&self, i: usize, a: A::Value) {
        A::act_assign(a.clone(), &mut self.table.borrow_mut()[i]);
        if i < self.len {
            A::op_right(a, &mut self.lazy.borrow_mut()[i]);
        }
    }
}

#[cfg(test)]
mod tests {
    mod impl_query;
    mod range_affine_range_sum;
    use super::LazySegtree;

    use alg_traits::{Action, Assoc, Identity};
    use rand::prelude::*;
    use test_vector2::{queries, Vector};

    type Tester<A, T, G> = query_test::Tester<StdRng, Vector<T>, crate::LazySegtree<A, T>, G>;

    #[test]
    fn test_update_add_u32() {
        #[derive(Debug, Clone, PartialEq, Copy, Eq)]
        struct X {}
        impl Assoc for X {
            type Value = (u32, u32);
            fn op((x0, y0): (u32, u32), (x1, y1): (u32, u32)) -> (u32, u32) {
                (x0 + x1, y0 + y1)
            }
        }
        impl Identity for X {
            fn identity() -> (u32, u32) {
                (0, 0)
            }
        }

        #[derive(Debug, Clone, PartialEq, Copy, Eq)]
        struct A {}
        impl Assoc for A {
            type Value = u32;
            fn op(a: u32, _b: u32) -> u32 {
                a
            }
        }
        impl Action for A {
            type Point = (u32, u32);
            fn act(a: u32, x: (u32, u32)) -> (u32, u32) {
                let len = x.1;
                (a * len, len)
            }
        }

        struct G {}
        impl test_vector2::GenLen for G {
            fn gen_len(rng: &mut impl Rng) -> usize {
                rng.gen_range(1, 20)
            }
        }
        impl test_vector2::GenValue<(u32, u32)> for G {
            fn gen_value(rng: &mut impl Rng) -> (u32, u32) {
                (rng.gen_range(0, 20), 1)
            }
        }
        impl test_vector2::GenKey<u32> for G {
            fn gen_key(rng: &mut impl Rng) -> u32 {
                rng.gen_range(0, 100)
            }
        }
        impl test_vector2::GenActor<Option<A>> for G {
            fn gen_actor(rng: &mut impl Rng) -> Option<u32> {
                Some(rng.gen_range(0, 100))
            }
        }

        struct P {}
        impl queries::Pred<(u32, u32), u32> for P {
            fn pred(&(x, _): &(u32, u32), &y: &u32) -> bool {
                x <= y
            }
        }

        let mut tester = Tester::<Option<A>, X, G>::new(StdRng::seed_from_u64(42));
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 3);
                match command {
                    0 => tester.mutate::<queries::Set<_>>(),
                    1 => tester.compare::<queries::Fold<_>>(),
                    2 => tester.mutate::<queries::RangeApply<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}