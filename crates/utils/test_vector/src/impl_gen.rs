use super::Vector;
use queries::{gen, utils};
use query_test::Gen;
use rand::Rng;
use std::ops::Range;
use type_traits::{Action, Identity};

impl<T, G> Gen<queries::Get<T>, G> for Vector<T> {
    fn gen<R: Rng>(&self, rng: &mut R) -> usize {
        self.gen_index::<R, G>(rng)
    }
}
impl<T, G: gen::GenValue<T>> Gen<queries::Set<T>, G> for Vector<T> {
    fn gen<R: Rng>(&self, rng: &mut R) -> (usize, T) {
        (self.gen_index::<R, G>(rng), G::gen_value(rng))
    }
}
impl<T: Identity, G> Gen<queries::Fold<T>, G> for Vector<T> {
    fn gen<R: Rng>(&self, rng: &mut R) -> Range<usize> {
        self.gen_range::<R, G>(rng)
    }
}
impl<T, U, P, G> Gen<queries::ForwardUpperBoundByKey<T, U, P>, G> for Vector<T>
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
impl<T, U, P, G> Gen<queries::BackwardUpperBoundByKey<T, U, P>, G> for Vector<T>
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
impl<T, G> Gen<queries::RangeApply<T>, G> for Vector<T::Space>
where
    T: Action,
    G: gen::GenAction<T>,
{
    fn gen<R: Rng>(&self, rng: &mut R) -> (Range<usize>, T) {
        (self.gen_range::<R, G>(rng), G::gen_action(rng))
    }
}
