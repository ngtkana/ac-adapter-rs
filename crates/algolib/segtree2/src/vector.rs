use crate::{queries, traits::Identity};
use query_test::{solve, Gen, Init};
use rand::prelude::*;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T: Identity>(pub Vec<T::Value>);

impl<T: Identity> solve::Mutate<queries::Set<T::Value>> for Vector<T> {
    fn mutate(&mut self, (i, x): (usize, T::Value)) {
        self.0[i] = x;
    }
}

impl<T: Identity> solve::Solve<queries::Fold<T::Value>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T::Value {
        self.0[range]
            .iter()
            .fold(T::identity(), |x, y| T::op(x, y.clone()))
    }
}

pub trait GenLen {
    fn gen_len(rng: &mut impl Rng) -> usize;
}

pub trait GenValue<T> {
    fn gen_value(rng: &mut impl Rng) -> T;
}

impl<T: Identity, G: GenLen + GenValue<T::Value>> Init<G> for Vector<T> {
    fn init(rng: &mut impl Rng) -> Self {
        let len = G::gen_len(rng);
        Vector(
            std::iter::repeat_with(|| G::gen_value(rng))
                .take(len)
                .collect(),
        )
    }
}

impl<T: Identity> Vector<T> {
    fn gen_index(&self, rng: &mut impl Rng) -> usize {
        rng.gen_range(0, self.0.len())
    }
    fn gen_range(&self, rng: &mut impl Rng) -> Range<usize> {
        let mut u = rng.gen_range(0, self.0.len() + 1);
        let mut v = rng.gen_range(0, self.0.len() + 1);
        if v < u {
            std::mem::swap(&mut u, &mut v);
        }
        u..v
    }
}

impl<T: Identity, G: GenValue<T::Value>> Gen<queries::Set<T::Value>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> (usize, T::Value) {
        (self.gen_index(rng), G::gen_value(rng))
    }
}

impl<T: Identity, G> Gen<queries::Fold<T::Value>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
