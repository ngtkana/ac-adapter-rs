pub use queries;
use queries::{Fold, Get, Pred, RangeApply, SearchBackward, SearchForward, Set};

use alg_traits::{Action, Identity};
use helpers::{Actor, Key, Len, Value};
use query_test::{
    solve::{Judge, Mutate, Solve},
    Gen, Help, HelpMaterial, Init,
};
use rand::prelude::*;
use std::ops::Range;

#[derive(Debug, Clone, PartialEq)]
pub struct Vector<T>(pub Vec<T>);

// TODO: 参照型への対応を検討しても良いかもです。
impl<T: Clone> Solve<Get<T>> for Vector<T> {
    fn solve(&self, i: usize) -> T {
        self.0[i].clone()
    }
}

impl<T> Mutate<Set<T>> for Vector<T> {
    fn mutate(&mut self, (i, x): (usize, T)) {
        self.0[i] = x;
    }
}

impl<T: Identity> Solve<Fold<T>> for Vector<T::Value> {
    fn solve(&self, range: Range<usize>) -> T::Value {
        self.0[range]
            .iter()
            .fold(T::identity(), |x, y| T::op(x, y.clone()))
    }
}

impl<T, P> Judge<SearchForward<T, P>> for Vector<T::Value>
where
    T: Identity,
    P: Pred<Value = T::Value>,
{
    fn judge(&self, (range, key): (Range<usize>, P::Key), output: usize) -> bool {
        let pred = |end| {
            P::pred(
                &<Self as Solve<Fold<T>>>::solve(self, range.start..end),
                &key,
            )
        };
        (range.start..=range.end).contains(&output)
            && (range.start == output || pred(output))
            && (range.end == output || !pred(output + 1))
    }
}

impl<T, P> Judge<SearchBackward<T, P>> for Vector<T::Value>
where
    T: Identity,
    P: Pred<Value = T::Value>,
{
    fn judge(&self, (range, key): (Range<usize>, P::Key), output: usize) -> bool {
        let pred = |start| {
            P::pred(
                &<Self as Solve<Fold<T>>>::solve(self, start..range.end),
                &key,
            )
        };
        (range.start..=range.end).contains(&output)
            && (range.start == output || !pred(output - 1))
            && (range.end == output || pred(output))
    }
}

impl<A: Action> Mutate<RangeApply<A>> for Vector<A::Point> {
    fn mutate(&mut self, (range, a): (Range<usize>, A::Value)) {
        self.0[range]
            .iter_mut()
            .for_each(|x| A::act_assign(a.clone(), x));
    }
}

impl<T, G: Help<Len> + Help<Value<T>>> Init<G> for Vector<T> {
    fn init(rng: &mut impl Rng) -> Self {
        let len = <G as Help<Len>>::help(rng);
        Vector(
            std::iter::repeat_with(|| <G as Help<Value<_>>>::help(rng))
                .take(len)
                .collect(),
        )
    }
}

impl<T> Vector<T> {
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

impl<T, G: Help<Value<T>>> Gen<Get<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> usize {
        self.gen_index(rng)
    }
}

impl<T, G: Help<Value<T>>> Gen<Set<T>, G> for Vector<T> {
    fn gen(&self, rng: &mut impl Rng) -> (usize, T) {
        (self.gen_index(rng), <G as Help<Value<_>>>::help(rng))
    }
}

impl<T: Identity, G> Gen<Fold<T>, G> for Vector<T::Value> {
    fn gen(&self, rng: &mut impl Rng) -> Range<usize> {
        self.gen_range(rng)
    }
}

impl<T, P, G> Gen<SearchForward<T, P>, G> for Vector<T::Value>
where
    T: Identity,
    P: Pred<Value = T::Value>,
    G: Help<Key<P::Key>>,
{
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, P::Key) {
        (self.gen_range(rng), G::help(rng))
    }
}

impl<T, P, G> Gen<SearchBackward<T, P>, G> for Vector<T::Value>
where
    T: Identity,
    P: Pred<Value = T::Value>,
    G: Help<Key<P::Key>>,
{
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, P::Key) {
        (self.gen_range(rng), G::help(rng))
    }
}

impl<A, G> Gen<RangeApply<A>, G> for Vector<A::Point>
where
    A: Action,
    G: Help<Actor<A>>,
{
    fn gen(&self, rng: &mut impl Rng) -> (Range<usize>, A::Value) {
        (self.gen_range(rng), G::help(rng))
    }
}

pub mod helpers {
    use super::HelpMaterial;
    use alg_traits::Action;
    pub use queries;
    use query_test::help_material;
    use std::marker::PhantomData;

    #[help_material(usize)]
    pub struct Len();

    #[help_material(T)]
    pub struct Value<T>(PhantomData<T>);

    #[help_material(T)]
    pub struct Key<T>(PhantomData<T>);

    #[help_material(A::Value)]
    pub struct Actor<A: Action>(PhantomData<A>);
}
