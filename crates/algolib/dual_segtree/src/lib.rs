use std::ops::RangeBounds;
use type_traits::{Action, Identity};

#[derive(Debug, Clone, PartialEq)]
pub struct DualSegtreeWith<T: Action> {
    dual: DualSegtree<T>,
    table: Vec<T::Space>,
}
impl<T: Action> DualSegtreeWith<T> {
    pub fn from_slice(_src: &[T], _table: &[T::Space]) -> Self {
        todo!()
    }
    pub fn apply(&mut self, _range: impl RangeBounds<usize>, _x: T) {
        todo!()
    }
    pub fn get(&mut self, _i: usize) -> &T::Space {
        todo!()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct DualSegtree<T> {
    len: usize,
    lg: u32,
    lazy: Vec<T>,
}
impl<T: Identity> DualSegtree<T> {
    pub fn from_slice(_src: &[T]) -> Self {
        todo!()
    }
    pub fn apply(&mut self, _range: impl RangeBounds<usize>, _x: T) {
        todo!()
    }
    pub fn get(&mut self, _i: usize) -> &T {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    mod impl_query;
    use query_test_2::{gen, query, Vector, CONFIG};
    use rand::prelude::*;

    type Fp = fp::F998244353;
    type Tester<T, G> = query_test_2::Tester<StdRng, Vector<T>, crate::DualSegtree<T>, G>;

    #[test]
    fn test_add_fp() {
        use type_traits::{actions::Adj, binary::Add};
        type Node = Add<Fp>;
        type Action = Adj<Node>;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 100)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(rng: &mut R) -> Node {
                Add(Fp::new(rng.gen_range(0, 1)))
            }
        }
        impl gen::GenAction<Action> for G {
            fn gen_action<R: Rng>(rng: &mut R) -> Action {
                Adj(<G as gen::GenValue<Node>>::gen_value(rng))
            }
        }

        let mut tester = Tester::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 5);
                match command {
                    0 => tester.compare_mut::<query::Get<_>>(),
                    1 => tester.mutate::<query::RangeApply<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
