use crate::{gen, query, solve, Gen, RandNew};
use rand::prelude::*;
use std::{fmt::Debug, marker::PhantomData, ops::Range};
use type_traits::{Assoc, Identity};

#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T>(pub Vec<T>);
impl<T> solve::SolveGet<query::Get<T>> for Vector<T> {
    fn solve_get(&self, i: usize) -> &T {
        &self.0[i]
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
impl<T> solve::SolveMut<query::Set<T>> for Vector<T> {
    fn solve_mut(&mut self, (i, x): (usize, T)) {
        self.0[i] = x;
    }
}
impl<T: Identity> solve::Solve<query::Fold<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range].iter().cloned().fold(T::identity(), T::op)
    }
}
impl<T: Assoc> solve::Solve<query::FoldFirst<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> Option<T> {
        self.0[range]
            .iter()
            .cloned()
            .fold(None, |x, y| Some(x.map(|x| x.op(y.clone())).unwrap_or(y)))
    }
}

impl<T> Vector<T> {
    fn gen_index<R: Rng, G>(&self, rng: &mut R) -> usize {
        rng.gen_range(0, self.0.len())
    }
    fn gen_range<R: Rng, G>(&self, rng: &mut R) -> Range<usize> {
        let mut u = rng.gen_range(0, self.0.len() + 1);
        let mut v = rng.gen_range(0, self.0.len());
        if v < u {
            std::mem::swap(&mut u, &mut v);
            v -= 1;
        }
        u..v
    }
}
impl<T, G> Gen<query::Get<T>, G> for Vector<T> {
    fn gen<R: Rng>(&self, rng: &mut R) -> usize {
        self.gen_index::<R, G>(rng)
    }
}
impl<T, G: gen::GenValue<T>> Gen<query::Set<T>, G> for Vector<T> {
    fn gen<R: Rng>(&self, rng: &mut R) -> (usize, T) {
        (self.gen_index::<R, G>(rng), G::gen_value(rng))
    }
}
impl<T: Identity, G> Gen<query::Fold<T>, G> for Vector<T> {
    fn gen<R: Rng>(&self, rng: &mut R) -> Range<usize> {
        self.gen_range::<R, G>(rng)
    }
}
impl<T: Identity, G> Gen<query::FoldFirst<T>, G> for Vector<T> {
    fn gen<R: Rng>(&self, rng: &mut R) -> Range<usize> {
        <Self as Gen<query::Fold<T>, G>>::gen(self, rng)
    }
}

#[cfg(test)]
mod tests {
    use crate::{gen, query, solve, FromBrute, Vector};
    use rand::prelude::*;
    use std::ops::Range;
    use type_traits::Identity;

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
    impl<T: Identity> solve::SolveGet<query::Get<T>> for Segtree<T> {
        fn solve_get(&self, i: usize) -> &T {
            &self.table[i + self.table.len() / 2]
        }
    }
    impl<T: Identity> solve::SolveMut<query::Set<T>> for Segtree<T> {
        fn solve_mut(&mut self, (mut i, x): (usize, T)) {
            i += self.len;
            self.table[i] = x;
            (1..=self.lg)
                .rev()
                .map(|p| i >> p)
                .for_each(|j| self.update(j));
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

    #[test]
    fn test_add_u32() {
        use type_traits::binary::Add;

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

        let mut tester =
            crate::Tester::<StdRng, crate::Vector<Add<u32>>, Segtree<Add<u32>>, G>::new(
                StdRng::seed_from_u64(42),
                crate::CONFIG,
            );
        for _ in 0..100 {
            let command = tester.rng_mut().gen_range(0, 3);
            match command {
                0 => tester.test_get::<query::Get<_>>(),
                1 => tester.test_mut::<query::Set<_>>(),
                2 => tester.test::<query::Fold<_>>(),
                _ => unreachable!(),
            }
        }
    }
}
