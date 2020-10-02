use std::ops::{self, Range, RangeBounds};
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
    table: Vec<T>,
}
impl<T: Identity> DualSegtree<T> {
    pub fn from_slice(src: &[T]) -> Self {
        Self {
            len: src.len(),
            lg: src.len().next_power_of_two().trailing_zeros(),
            table: std::iter::repeat_with(T::identity)
                .take(src.len())
                .chain(src.to_vec())
                .collect::<Vec<_>>(),
        }
    }
    pub fn apply(&mut self, range: impl RangeBounds<usize>, x: T) {
        let Range { mut start, mut end } = open(self.len, range);
        if start < end {
            start += self.len;
            end += self.len;
            self.thrust(start);
            self.thrust(end - 1);
            while start != end {
                if start % 2 == 1 {
                    self.table[start].op_from_left(&x);
                    start += 1;
                }
                if end % 2 == 1 {
                    end -= 1;
                    self.table[end].op_from_left(&x);
                }
                start >>= 1;
                end >>= 1;
            }
        }
    }
    pub fn get(&mut self, mut i: usize) -> &T {
        i += self.len;
        self.thrust(i);
        &self.table[i]
    }
    fn thrust(&mut self, i: usize) {
        let lg = self.lg;
        (1..=lg)
            .rev()
            .map(|p| i >> p)
            .for_each(|j| self.propagate(j));
    }
    fn propagate(&mut self, i: usize) {
        if self.table[i] != T::identity() {
            let x = std::mem::replace(&mut self.table[i], T::identity());
            self.table[2 * i].op_from_left(&x);
            self.table[2 * i + 1].op_from_left(&x);
        }
    }
}
fn open(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    use ops::Bound::*;
    (match range.start_bound() {
        Unbounded => 0,
        Included(&x) => x,
        Excluded(&x) => x + 1,
    })..(match range.end_bound() {
        Excluded(&x) => x,
        Included(&x) => x + 1,
        Unbounded => len,
    })
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
        use type_traits::{actions::Adj, binary::Add, Constant};
        type Node = Add<Fp>;
        type Action = Adj<Node>;

        struct G {}
        impl gen::GenLen for G {
            fn gen_len<R: Rng>(rng: &mut R) -> usize {
                rng.gen_range(1, 100)
            }
        }
        impl gen::GenValue<Node> for G {
            fn gen_value<R: Rng>(_rng: &mut R) -> Node {
                Add(Fp::new(0))
            }
        }
        impl gen::GenAction<Action> for G {
            fn gen_action<R: Rng>(rng: &mut R) -> Action {
                Adj(Add(Fp::new(rng.gen_range(0, fp::Mod998244353::VALUE))))
            }
        }

        let mut tester = Tester::<Node, G>::new(StdRng::seed_from_u64(42), CONFIG);
        for _ in 0..4 {
            tester.initialize();
            for _ in 0..100 {
                let command = tester.rng_mut().gen_range(0, 2);
                match command {
                    0 => tester.compare_mut::<query::Get<_>>(),
                    1 => tester.mutate::<query::RangeApply<_>>(),
                    _ => unreachable!(),
                }
            }
        }
    }
}
