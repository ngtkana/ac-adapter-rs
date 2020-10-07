use alg_traits::Identity;
use std::ops::{Range, RangeBounds};

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
                T::op_left(&mut left, self.table[start].clone());
                start += 1;
            }
            if end % 2 == 1 {
                end -= 1;
                T::op_right(self.table[end].clone(), &mut right);
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
    mod impl_query;
    use alg_inversion_number::{InversionMerge, InversionValue};
    use rand::prelude::*;
    use test_vector2::{queries, Vector};

    type Tester<T, G> = query_test::Tester<StdRng, Vector<T>, crate::Segtree<T>, G>;

    #[test]
    fn test_inversion_value() {
        type Node = InversionValue;
        struct G {}
        impl test_vector2::GenLen for G {
            fn gen_len(rng: &mut impl Rng) -> usize {
                rng.gen_range(1, 20)
            }
        }
        impl test_vector2::GenValue<Node> for G {
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
