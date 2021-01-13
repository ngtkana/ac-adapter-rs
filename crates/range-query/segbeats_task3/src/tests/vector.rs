use super::queries::{ChangeMax, ChangeMin, CountChanges, QueryMax, QueryMin, QuerySum, RangeAdd};
use crate::Elm;
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
impl<T: Elm> Mutate<ChangeMin<T>> for Vector<(T, u64)> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.0[range].iter_mut().for_each(|y| {
            if x < y.0 {
                y.0 = x;
                y.1 += 1;
            }
        });
    }
}
impl<T: Elm> Mutate<ChangeMax<T>> for Vector<(T, u64)> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.0[range].iter_mut().for_each(|y| {
            if y.0 < x {
                y.0 = x;
                y.1 += 1;
            }
        });
    }
}
impl<T: Elm> Mutate<RangeAdd<T>> for Vector<(T, u64)> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        self.0[range].iter_mut().for_each(|y| {
            if x != T::zero() {
                y.0 += x;
                y.1 += 1;
            }
        });
    }
}
impl<T: Elm> Solve<QueryMin<T>> for Vector<(T, u64)> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range]
            .iter()
            .map(|&(x, _)| x)
            .min()
            .unwrap_or_else(T::max_value)
    }
}
impl<T: Elm> Solve<QueryMax<T>> for Vector<(T, u64)> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range]
            .iter()
            .map(|&(x, _)| x)
            .max()
            .unwrap_or_else(T::min_value)
    }
}
impl<T: Elm> Solve<QuerySum<T>> for Vector<(T, u64)> {
    fn solve(&self, range: Range<usize>) -> T {
        self.0[range]
            .iter()
            .map(|&(x, _)| x)
            .fold(T::zero(), std::ops::Add::add)
    }
}
impl<T: Elm> Solve<CountChanges> for Vector<(T, u64)> {
    fn solve(&self, range: Range<usize>) -> u64 {
        self.0[range].iter().map(|&(_, y)| y).sum()
    }
}

// -- helpers
#[help_material(usize)]
pub struct Len();
#[help_material(T)]
pub struct Value<T: Elm>(PhantomData<T>);
impl<T: Elm> Vector<(T, u64)> {
    fn gen_range(&self, rng: &mut impl Rng) -> Range<usize> {
        let mut u = rng.gen_range(0, self.0.len());
        let mut v = rng.gen_range(0, 1 + self.0.len());
        if u > v {
            swap(&mut u, &mut v);
        }
        u..v
    }
}

// -- init
impl<G: Help<Len> + Help<Value<T>>, T: Elm> Init<G> for Vector<(T, u64)> {
    fn init(rng: &mut impl Rng) -> Self {
        let len = <G as Help<Len>>::help(rng);
        Vector(
            repeat_with(|| (<G as Help<Value<T>>>::help(rng), 0))
                .take(len)
                .collect(),
        )
    }
}

// -- gen
impl<T: Elm, G: Help<Value<T>>> Gen<ChangeMin<T>, G> for Vector<(T, u64)> {
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, T) {
        (self.gen_range(rng), G::help(rng))
    }
}
impl<T: Elm, G: Help<Value<T>>> Gen<ChangeMax<T>, G> for Vector<(T, u64)> {
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, T) {
        (self.gen_range(rng), G::help(rng))
    }
}
impl<T: Elm, G: Help<Value<T>>> Gen<RangeAdd<T>, G> for Vector<(T, u64)> {
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, T) {
        (self.gen_range(rng), G::help(rng))
    }
}
impl<T: Elm, G> Gen<QueryMin<T>, G> for Vector<(T, u64)> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
impl<T: Elm, G> Gen<QueryMax<T>, G> for Vector<(T, u64)> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
impl<T: Elm, G> Gen<QuerySum<T>, G> for Vector<(T, u64)> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
impl<T: Elm, G> Gen<CountChanges, G> for Vector<(T, u64)> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
