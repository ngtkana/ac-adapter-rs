use super::queries::{ChangeMax, ChangeMin, QueryMax, QueryMin, QuerySum};
use crate::Value;
use query_test::{
    help_material,
    solve::{Mutate, Solve},
    Gen, Help, HelpMaterial, Init,
};
use rand::Rng;
use std::{iter::repeat_with, marker::PhantomData, mem::swap, ops::Range};

#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T>(pub Vec<T>);

// -- solve
impl<T: Value> Mutate<ChangeMin<T>> for Vector<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.0[range].iter_mut().for_each(|y| *y = (*y).min(x));
    }
}
impl<T: Value> Mutate<ChangeMax<T>> for Vector<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.0[range].iter_mut().for_each(|y| *y = (*y).max(x));
    }
}
impl<T: Value> Solve<QueryMin<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range]
            .iter()
            .min()
            .copied()
            .unwrap_or_else(T::max_value)
    }
}
impl<T: Value> Solve<QueryMax<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range]
            .iter()
            .max()
            .copied()
            .unwrap_or_else(T::min_value)
    }
}
impl<T: Value> Solve<QuerySum<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range]
            .iter()
            .copied()
            .fold(T::ZERO, std::ops::Add::add)
    }
}

// -- helpers
#[help_material(usize)]
pub struct Len();
#[help_material(T)]
pub struct Item<T: Value>(PhantomData<T>);
impl<T: Value> Vector<T> {
    fn gen_range(&self, rng: &mut impl Rng) -> Range<usize> {
        let mut u = rng.gen_range(0..self.0.len());
        let mut v = rng.gen_range(0..1 + self.0.len());
        if u > v {
            swap(&mut u, &mut v);
        }
        u..v
    }
}

// -- init
impl<G: Help<Len> + Help<Item<T>>, T: Value> Init<G> for Vector<T> {
    fn init(rng: &mut impl Rng) -> Self {
        let len = <G as Help<Len>>::help(rng);
        Vector(
            repeat_with(|| <G as Help<Item<T>>>::help(rng))
                .take(len)
                .collect(),
        )
    }
}

// -- gen
impl<T: Value, G: Help<Item<T>>> Gen<ChangeMin<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, T) {
        (self.gen_range(rng), G::help(rng))
    }
}
impl<T: Value, G: Help<Item<T>>> Gen<ChangeMax<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, T) {
        (self.gen_range(rng), G::help(rng))
    }
}
impl<T: Value, G> Gen<QueryMin<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
impl<T: Value, G> Gen<QueryMax<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
impl<T: Value, G> Gen<QuerySum<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
