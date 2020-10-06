mod impl_query;
mod queries;
pub mod traits;
mod vector;

use std::ops::{Range, RangeBounds};
use traits::Identity;

#[derive(Debug, Clone, PartialEq)]
pub struct Segtree<T: Identity> {
    len: usize,
    table: Vec<T::Value>,
}
impl<T: Identity> Segtree<T> {
    pub fn from_slice(src: &[T::Value]) -> Self {
        let mut table = src.iter().chain(src.iter()).cloned().collect::<Vec<_>>();
        let len = src.len();
        for i in (1..len).rev() {
            table[i] = T::op(table[2 * i].clone(), table[2 * i + 1].clone())
        }
        Segtree { len, table }
    }
    pub fn set(&mut self, mut i: usize, x: T::Value) {
        i += self.len;
        self.table[i] = x;
        i >>= 1;
        while 0 != i {
            self.update(i);
            i >>= 1;
        }
    }
    pub fn fold(&self, range: impl RangeBounds<usize>) -> T::Value {
        let Range { mut start, mut end } = open(self.len, range);
        start += self.len;
        end += self.len;
        let mut left = T::identity();
        let mut right = T::identity();
        while start != end {
            if start % 2 == 1 {
                T::op_left(&mut left, &self.table[start]);
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                T::op_right(&self.table[end], &mut right);
            }
            start >>= 1;
            end >>= 1;
        }
        T::op(left, right)
    }
    fn update(&mut self, i: usize) {
        self.table[i] = T::op(self.table[2 * i].clone(), self.table[2 * i + 1].clone())
    }
}

fn open(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    use std::ops::Bound::*;
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
    use super::*;
    use rand::prelude::*;
    use traits::{Assoc, Identity};

    type Tester<T, G> = query_test::Tester<StdRng, vector::Vector<T>, crate::Segtree<T>, G>;

    #[derive(Debug, Clone, PartialEq)]
    pub struct InversionValue {
        pub zeros: usize,
        pub ones: usize,
        pub inversion: usize,
    }
    impl InversionValue {
        fn from_bool(src: bool) -> Self {
            match src {
                false => InversionValue {
                    zeros: 1,
                    ones: 0,
                    inversion: 0,
                },
                true => InversionValue {
                    zeros: 0,
                    ones: 1,
                    inversion: 0,
                },
            }
        }
    }

    #[derive(Debug, Clone, PartialEq)]
    pub struct InversionMerge {}
    impl Assoc for InversionMerge {
        type Value = InversionValue;
        fn op(lhs: InversionValue, rhs: InversionValue) -> InversionValue {
            InversionValue {
                zeros: lhs.zeros + rhs.zeros,
                ones: lhs.ones + rhs.ones,
                inversion: lhs.inversion + rhs.inversion + lhs.ones * rhs.zeros,
            }
        }
    }
    impl Identity for InversionMerge {
        fn identity() -> InversionValue {
            InversionValue {
                zeros: 0,
                ones: 0,
                inversion: 0,
            }
        }
    }

    #[test]
    fn test_inversion_value() {
        type Node = InversionValue;
        struct G {}
        impl vector::GenLen for G {
            fn gen_len(rng: &mut impl Rng) -> usize {
                rng.gen_range(1, 20)
            }
        }
        impl vector::GenValue<Node> for G {
            fn gen_value(rng: &mut impl Rng) -> Node {
                InversionValue::from_bool(rng.gen_ratio(1, 2))
            }
        }

        let mut tester = Tester::<InversionMerge, G>::new(StdRng::seed_from_u64(42));
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 2);
                match command {
                    0 => tester.mutate::<queries::Set<_>>(),
                    1 => tester.compare::<queries::Fold<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
