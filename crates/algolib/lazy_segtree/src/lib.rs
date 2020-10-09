#![allow(dead_code, unused_variables, unused_imports)]
use alg_traits::{Action, Identity};
use std::ops::{Range, RangeBounds};

#[derive(Debug, Clone, PartialEq)]
pub struct LazySegtree<A: Action, T: Identity> {
    len: usize,
    lazy: std::cell::RefCell<Vec<A::Value>>,
    table: std::cell::RefCell<Vec<T::Value>>,
}

impl<A, T> LazySegtree<A, T>
where
    A: Action<Point = T::Value>,
    T: Identity,
{
    fn from_slice(src: &[T::Value]) -> Self {
        todo!()
    }

    fn set(&mut self, i: usize, x: T::Value) {
        todo!()
    }

    fn fold(&self, range: impl RangeBounds<usize>) -> T::Value {
        todo!()
    }

    fn apply(&mut self, range: impl RangeBounds<usize>, a: A::Value) {
        todo!()
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
}

#[cfg(test)]
mod tests {
    mod impl_query;
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
            fn op(a: u32, b: u32) -> u32 {
                a + b
            }
        }
        impl Identity for A {
            fn identity() -> u32 {
                0
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

        struct P {}
        impl queries::Pred<(u32, u32), u32> for P {
            fn pred(&(x, _): &(u32, u32), &y: &u32) -> bool {
                x <= y
            }
        }

        let mut tester = Tester::<A, X, G>::new(StdRng::seed_from_u64(42));
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 4);
                match command {
                    0 => tester.mutate::<queries::Set<_>>(),
                    1 => tester.compare::<queries::Fold<_>>(),
                    2 => tester.judge::<queries::SearchForward<_, _, P>>(),
                    3 => tester.judge::<queries::SearchBackward<_, _, P>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
