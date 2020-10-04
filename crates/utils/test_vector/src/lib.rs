mod impl_gen;
mod impl_query;
use query_test::{gen, query, solve, RandNew};
use rand::prelude::*;
use std::{fmt::Debug, marker::PhantomData, ops::Range};

#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T>(pub Vec<T>);
impl<T: Clone> solve::Solve<query::Get<T>> for Vector<T> {
    fn solve(&self, i: usize) -> T {
        self.0[i].clone()
    }
}
impl<T, G: gen::GenLen + gen::GenValue<T>> RandNew<G> for Vector<T> {
    fn rand_new<R: Rng>(rng: &mut R, _marker: PhantomData<G>) -> Self {
        let len = G::gen_len(rng);
        Vector(
            std::iter::repeat_with(|| G::gen_value(rng))
                .take(len)
                .collect(),
        )
    }
}

impl<T> Vector<T> {
    fn gen_index<R: Rng, G>(&self, rng: &mut R) -> usize {
        rng.gen_range(0, self.0.len())
    }
    fn gen_range<R: Rng, G>(&self, rng: &mut R) -> Range<usize> {
        let mut u = rng.gen_range(0, self.0.len() + 1);
        let mut v = rng.gen_range(0, self.0.len() + 1);
        if v < u {
            std::mem::swap(&mut u, &mut v);
        }
        u..v
    }
}

#[cfg(test)]
mod tests {
    use super::Vector;
    use query_test::{gen, query, solve, utils, FromBrute};
    use rand::prelude::*;
    use std::ops::Range;
    use type_traits::{Action, Identity};

    #[derive(Debug, Clone, PartialEq)]
    struct Segtree<T> {
        lg: u32,
        len: usize,
        table: Vec<T>,
    }
    impl<T: Identity> FromBrute for Segtree<T> {
        type Brute = Vector<T>;
        fn from_brute(brute: &Self::Brute) -> Self {
            let len = brute.0.len();
            let mut table = brute.0.to_vec();
            table.extend_from_slice(&brute.0);
            for i in (1..brute.0.len()).rev() {
                table[i] = table[2 * i].clone().op(table[2 * i + 1].clone());
            }
            let lg = len.next_power_of_two().trailing_zeros();
            Self { lg, len, table }
        }
    }
    impl<T: Identity> Segtree<T> {
        fn update(&mut self, i: usize) {
            self.table[i] = self.table[i * 2].clone().op(self.table[i * 2 + 1].clone());
        }
    }
    impl<T: Identity> solve::Solve<query::Get<T>> for Segtree<T> {
        fn solve(&self, i: usize) -> T {
            self.table[i + self.table.len() / 2].clone()
        }
    }
    impl<T: Identity> solve::Mutate<query::Set<T>> for Segtree<T> {
        fn mutate(&mut self, (mut i, x): (usize, T)) {
            i += self.len;
            self.table[i] = x;
            (1..=self.lg).map(|p| i >> p).for_each(|j| self.update(j));
        }
    }
    impl<T: Identity> solve::Solve<query::Fold<T>> for Segtree<T> {
        fn solve(&self, range: Range<usize>) -> T {
            let Range { mut start, mut end } = range;
            start += self.len;
            end += self.len;
            let mut left = T::identity();
            let mut right = T::identity();
            while start != end {
                if start % 2 == 1 {
                    left.op_from_right(&self.table[start]);
                    start += 1;
                }
                if end % 2 == 1 {
                    end -= 1;
                    right.op_from_left(&self.table[end]);
                }
                start /= 2;
                end /= 2;
            }
            left.op(right)
        }
    }
    impl<T, U, P> solve::Solve<query::ForwardUpperBoundByKey<T, U, P>> for Segtree<T>
    where
        T: Identity,
        U: Ord,
        P: utils::Project<T, U>,
    {
        fn solve(&self, (range, key): (Range<usize>, U)) -> usize {
            let yes = |i: usize| {
                P::project(<Self as solve::Solve<query::Fold<T>>>::solve(
                    self,
                    range.start..i,
                )) <= key
            };
            let Range { mut start, mut end } = range;
            if yes(end) {
                end
            } else {
                while start + 1 < end {
                    let mid = (start + end) / 2;
                    if yes(mid) {
                        start = mid;
                    } else {
                        end = mid;
                    }
                }
                start
            }
        }
    }
    impl<T> solve::Mutate<query::RangeApply<T>> for Segtree<T::Space>
    where
        T: Action,
        T::Space: Identity,
    {
        fn mutate(&mut self, (range, action): (Range<usize>, T)) {
            range.for_each(|i| {
                let x = action
                    .clone()
                    .acted(<Self as solve::Solve<query::Get<T::Space>>>::solve(self, i));
                <Self as solve::Mutate<query::Set<T::Space>>>::mutate(self, (i, x));
            });
        }
    }

    #[test]
    fn test_add_u32() {
        use type_traits::{actions::Adj, binary::Add};

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(0, 8)
            }
        }
        impl gen::GenValue<Add<u32>> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Add<u32> {
                Add(rng.gen_range(0, 256))
            }
        }
        impl gen::GenFoldedKey<u32> for G {
            fn gen_folded_key<R: Rng>(rng: &mut R) -> u32 {
                rng.gen_range(0, 256)
            }
        }
        impl gen::GenAction<Adj<Add<u32>>> for G {
            fn gen_action<R: Rng>(rng: &mut R) -> Adj<Add<u32>> {
                Adj(<G as gen::GenValue<_>>::gen_value(rng))
            }
        }

        struct P {}
        impl utils::Project<Add<u32>, u32> for P {
            fn project(src: Add<u32>) -> u32 {
                src.0
            }
        }

        let mut tester =
            query_test::Tester::<StdRng, crate::Vector<Add<u32>>, Segtree<Add<u32>>, G>::new(
                StdRng::seed_from_u64(42),
                query_test::CONFIG,
            );
        for _ in 0..100 {
            let command = tester.rng_mut().gen_range(0, 5);
            match command {
                0 => tester.compare::<query::Get<_>>(),
                1 => tester.mutate::<query::Set<_>>(),
                2 => tester.compare::<query::Fold<_>>(),
                3 => tester.judge::<query::ForwardUpperBoundByKey<_, u32, P>>(),
                4 => tester.mutate::<query::RangeApply<_>>(),
                _ => unreachable!(),
            }
        }
    }
}
