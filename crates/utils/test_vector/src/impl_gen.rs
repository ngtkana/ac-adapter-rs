use super::Vector;
use query_test::{gen, query, utils, Gen};
use rand::Rng;
use std::ops::Range;
use type_traits::{Action, Identity};

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
impl<T, U, P, G> Gen<query::ForwardUpperBoundByKey<T, U, P>, G> for Vector<T>
where
    T: Identity,
    U: Ord,
    P: utils::Project<T, U>,
    G: gen::GenFoldedKey<U>,
{
    fn gen<R: Rng>(&self, rng: &mut R) -> (Range<usize>, U) {
        (self.gen_range::<R, G>(rng), G::gen_folded_key(rng))
    }
}
impl<T, U, P, G> Gen<query::BackwardUpperBoundByKey<T, U, P>, G> for Vector<T>
where
    T: Identity,
    U: Ord,
    P: utils::Project<T, U>,
    G: gen::GenFoldedKey<U>,
{
    fn gen<R: Rng>(&self, rng: &mut R) -> (Range<usize>, U) {
        (self.gen_range::<R, G>(rng), G::gen_folded_key(rng))
    }
}
impl<T, G> Gen<query::RangeApply<T>, G> for Vector<T::Space>
where
    T: Action,
    G: gen::GenAction<T>,
{
    fn gen<R: Rng>(&self, rng: &mut R) -> (Range<usize>, T) {
        (self.gen_range::<R, G>(rng), G::gen_action(rng))
    }
}
