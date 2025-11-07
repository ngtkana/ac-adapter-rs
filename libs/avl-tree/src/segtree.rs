use super::core::{AvlTree, NodeMarker};
use std::{fmt::Debug, marker::PhantomData};

pub struct AvlSegtree<O: Op> {
    core: AvlTree<Marker<O>>,
}

impl<O: Op> Default for AvlSegtree<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Op> AvlSegtree<O> {
    pub fn new() -> Self {
        Self {
            core: AvlTree::new(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.core.is_empty()
    }

    pub fn len(&self) -> usize {
        self.core.len()
    }

    pub fn insert(&mut self, index: usize, value: O::Value) {
        self.core.insert(index, value);
    }

    pub fn remove(&mut self, index: usize) -> O::Value {
        self.core.remove(index)
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        Self {
            core: self.core.split_off(index),
        }
    }

    pub fn append(&mut self, other: Self) {
        self.core.append(other.core);
    }

    pub fn reverse(&mut self, start: usize, end: usize) {
        self.core.touch(start, end, |c| c.rev ^= true);
    }

    pub fn product(&mut self, start: usize, end: usize) -> O::Value {
        self.core.product(start, end)
    }
}

impl<O: Op> FromIterator<O::Value> for AvlSegtree<O> {
    fn from_iter<I: IntoIterator<Item = O::Value>>(iter: I) -> Self {
        Self {
            core: iter.into_iter().collect(),
        }
    }
}

pub trait Op {
    type Value: Clone + Debug; // TODO: remove

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    fn identity() -> Self::Value;
}

struct Marker<O> {
    __marker: PhantomData<O>,
}

impl<O: Op> NodeMarker for Marker<O> {
    type Value = O::Value;

    type Prod = O::Value;

    type Operator = ();

    fn singleton(value: &O::Value) -> Self::Prod {
        value.clone()
    }

    fn mul(lhs: &Self::Prod, rhs: &Self::Prod) -> Self::Prod {
        O::mul(lhs, rhs)
    }

    fn identity() -> Self::Prod {
        O::identity()
    }

    fn nop() {}

    fn op_value(&(): &Self::Operator, _: &mut Self::Value) {}

    fn op_prod(&(): &Self::Operator, _: &mut Self::Prod, _len: usize) {}

    fn compose(&(): &(), &mut (): &mut ()) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::debug::{collect, display, validate};
    use fp::fp;
    use rand::Rng;
    use rand::{SeedableRng, rngs::StdRng};

    const P: u64 = 998_244_353;

    type Fp = fp::Fp<P>;

    #[derive(Debug)]
    enum Query {
        Insert { index: usize, value: [Fp; 2] },
        Remove { index: usize },
        Product { start: usize, end: usize },
    }

    enum O {}

    impl Op for O {
        type Value = [Fp; 2];

        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            [lhs[0] * rhs[0], lhs[0] * rhs[1] + lhs[1]]
        }

        fn identity() -> Self::Value {
            [fp!(1), fp!(0)]
        }
    }

    #[test]
    fn test_segtree_noncommutative() {
        let mut rng = StdRng::seed_from_u64(42);
        for tid in 1..=200 {
            let q = 50;
            let value_lim = 10;
            let len_max = rng.gen_range(5..=50);
            let mut n = 0usize;
            let mut seg = AvlSegtree::<O>::new();
            let mut vec = vec![];
            for qid in 1..=q {
                let query = match rng.gen_range(0..3) {
                    0 => {
                        let mut start = rng.gen_range(0..=n + 1);
                        let mut end = rng.gen_range(0..=n);
                        if start > end {
                            (start, end) = (end, start - 1);
                        }
                        Query::Product { start, end }
                    }
                    1..=2 => {
                        if rng.gen_ratio(n as u32, len_max) {
                            let index = rng.gen_range(0..n);
                            Query::Remove { index }
                        } else {
                            let index = rng.gen_range(0..=n);
                            let value = [
                                Fp::new(rng.gen_range(0..value_lim)),
                                Fp::new(rng.gen_range(0..value_lim)),
                            ];
                            Query::Insert { index, value }
                        }
                    }
                    _ => unreachable!(),
                };
                eprintln!("Query #{tid}.{qid}: {query:?}");
                match query {
                    Query::Insert { index, value } => {
                        seg.insert(index, value);
                        vec.insert(index, value);
                        n += 1;
                    }
                    Query::Remove { index } => {
                        let result = seg.remove(index);
                        let expected = vec.remove(index);
                        assert_eq!(result, expected);
                        n -= 1;
                    }
                    Query::Product { start, end } => {
                        let result = seg.product(start, end);
                        let expected = vec[start..end]
                            .iter()
                            .fold(O::identity(), |x, &y| O::mul(&x, &y));
                        assert_eq!(result, expected);
                    }
                }
                eprintln!("{}", display(seg.core.root.as_deref()));
                let result: Vec<_> = collect(seg.core.root.as_deref()).into_iter().collect();
                eprintln!("   vec: {:?}", &vec);
                eprintln!(" rlist: {:?}", &result);
                assert_eq!(&vec, &result);
                validate(seg.core.root.as_deref());
                eprintln!();
            }
        }
    }
}
