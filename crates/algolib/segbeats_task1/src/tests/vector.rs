use super::queries::{ChangeMin, QueryMax, QuerySum};
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
impl<T: Elm> Mutate<ChangeMin<T>> for Vector<T> {
    fn mutate(&mut self, (range, x): (Range<usize>, T)) {
        todo!()
    }
}
impl<T: Elm> Solve<QueryMax<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T {
        todo!()
    }
}
impl<T: Elm> Solve<QuerySum<T>> for Vector<T> {
    fn solve(&self, range: Range<usize>) -> T {
        todo!()
    }
}

// -- helpers
#[help_material(usize)]
pub struct Len();
#[help_material(T)]
pub struct Value<T: Elm>(PhantomData<T>);
impl<T: Elm> Vector<T> {
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
impl<G: Help<Len> + Help<Value<T>>, T: Elm> Init<G> for Vector<T> {
    fn init(rng: &mut impl Rng) -> Self {
        let len = <G as Help<Len>>::help(rng);
        Vector(
            repeat_with(|| <G as Help<Value<T>>>::help(rng))
                .take(len)
                .collect(),
        )
    }
}

// -- gen
impl<T: Elm, G: Help<Value<T>>> Gen<ChangeMin<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, T) {
        (self.gen_range(rng), G::help(rng))
    }
}
impl<T: Elm, G> Gen<QueryMax<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
impl<T: Elm, G> Gen<QuerySum<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}
