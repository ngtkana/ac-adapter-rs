pub use queries2 as queries;

use alg_traits::{Action, Identity};
use query_test::{
    solve::{Judge, Mutate, Solve},
    Gen, Init,
};
use rand::prelude::*;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T>(pub Vec<T>);

// TODO: 参照型への対応を検討しても良いかもです。
impl<T: Clone> Solve<queries::Get<T>> for Vector<T> {
    fn solve(&self, i: usize) -> T {
        self.0[i].clone()
    }
}

impl<T> Mutate<queries::Set<T>> for Vector<T> {
    fn mutate(&mut self, (i, x): (usize, T)) {
        self.0[i] = x;
    }
}

impl<T: Identity> Solve<queries::Fold<T>> for Vector<T::Value> {
    fn solve(&self, range: Range<usize>) -> T::Value {
        self.0[range]
            .iter()
            .fold(T::identity(), |x, y| T::op(x, y.clone()))
    }
}

impl<T, U, P> Judge<queries::SearchForward<T, U, P>> for Vector<T::Value>
where
    T: Identity,
    P: queries::Map<T::Value, U>,
{
    fn judge(&self, (range, key): (Range<usize>, U), output: usize) -> bool {
        let pred = |end| {
            P::map(
                &<Self as Solve<queries::Fold<T>>>::solve(self, range.start..end),
                &key,
            )
        };
        (range.start <= output && output <= range.end && range.start == output || pred(output))
            && (range.end == output || !pred(output + 1))
    }
}

impl<T, U, P> Judge<queries::SearchBackward<T, U, P>> for Vector<T::Value>
where
    T: Identity,
    P: queries::Map<T::Value, U>,
{
    fn judge(&self, (range, key): (Range<usize>, U), output: usize) -> bool {
        let pred = |start: usize| {
            P::map(
                &<Vector<_> as Solve<queries::Fold<T>>>::solve(self, start..range.end),
                &key,
            )
        };
        (range.start <= output
            && output <= range.end
            && (range.start == output || !pred(output - 1)))
            && (range.end == output || pred(output))
    }
}

impl<A: Action> Mutate<queries::RangeApply<A>> for Vector<A::Point> {
    fn mutate(&mut self, (range, a): (Range<usize>, A::Value)) {
        self.0[range]
            .iter_mut()
            .for_each(|x| A::act_assign(a.clone(), x));
    }
}

pub trait GenLen {
    fn gen_len(rng: &mut impl Rng) -> usize;
}

pub trait GenValue<T> {
    fn gen_value(rng: &mut impl Rng) -> T;
}

pub trait GenKey<T> {
    fn gen_key(rng: &mut impl Rng) -> T;
}

pub trait GenActor<A: Action> {
    fn gen_actor(rng: &mut impl Rng) -> A::Value;
}

impl<T, G: GenLen + GenValue<T>> Init<G> for Vector<T> {
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

impl<T: Identity, G: GenValue<T::Value>> Gen<queries::Get<T::Value>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> usize {
        self.gen_index(rng)
    }
}

impl<T: Identity, G: GenValue<T::Value>> Gen<queries::Set<T::Value>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> (usize, T::Value) {
        (self.gen_index(rng), G::gen_value(rng))
    }
}

impl<T: Identity, G> Gen<queries::Fold<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}

impl<T, U, P, G> Gen<queries::SearchForward<T, U, P>, G> for Vector<T>
where
    T: Identity,
    P: queries::Map<T::Value, U>,
    G: GenKey<U>,
{
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, U) {
        (self.gen_range(rng), G::gen_key(rng))
    }
}

impl<T, U, P, G> Gen<queries::SearchBackward<T, U, P>, G> for Vector<T>
where
    T: Identity,
    P: queries::Map<T::Value, U>,
    G: GenKey<U>,
{
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, U) {
        (self.gen_range(rng), G::gen_key(rng))
    }
}

impl<A, T, G> Gen<queries::RangeApply<A>, G> for Vector<T>
where
    A: Action<Point = T::Value>,
    T: Identity,
    G: GenActor<A>,
{
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, A::Value) {
        (self.gen_range(rng), G::gen_actor(rng))
    }
}
