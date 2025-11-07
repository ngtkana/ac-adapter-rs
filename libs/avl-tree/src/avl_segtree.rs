use super::core::{AvlTree, Node, NodeMarker};
use std::{fmt::Debug, marker::PhantomData};

pub struct AvlSegtree<O: Op> {
    tree: AvlTree<Marker<O>>,
}

impl<O: Op> Default for AvlSegtree<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Op> AvlSegtree<O> {
    pub fn new() -> Self {
        Self {
            tree: AvlTree::new(),
        }
    }
    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }
    pub fn len(&self) -> usize {
        self.tree.len()
    }
    pub fn insert(&mut self, index: usize, value: O::Value) {
        self.tree.insert(index, Data::new(value));
    }
    pub fn remove(&mut self, index: usize) -> O::Value {
        self.tree.remove(index).value
    }
    pub fn split(&mut self, index: usize) -> (Self, Self) {
        let (l, r) = self.tree.split(index);
        (Self { tree: l }, Self { tree: r })
    }
    pub fn merge(lhs: Self, rhs: Self) -> Self {
        Self {
            tree: AvlTree::merge(lhs.tree, rhs.tree),
        }
    }
    pub fn reverse(&mut self, start: usize, end: usize) {
        self.tree.touch(start, end, |c| c.rev ^= true);
    }
    pub fn product(&mut self, start: usize, end: usize) -> O::Value {
        self.tree
            .touch(start, end, |c| c.data.sum.clone())
            .unwrap_or_else(O::identity)
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

struct Data<O: Op> {
    value: O::Value,
    sum: O::Value,
}

impl<O: Op> Data<O> {
    fn new(value: O::Value) -> Self {
        Self {
            sum: value.clone(),
            value,
        }
    }
}

impl<O: Op> Debug for Data<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Data")
            .field("value", &self.value)
            .field("sum", &self.sum)
            .finish()
    }
}

impl<O: Op> Clone for Data<O> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            sum: self.sum.clone(),
        }
    }
}

impl<O: Op> NodeMarker for Marker<O> {
    type Data = Data<O>;

    fn update(node: &mut Node<Self>) {
        let mut sum = node.data.value.clone();
        if let Some(l) = node.left.as_ref() {
            sum = O::mul(&l.data.sum, &sum);
        }
        if let Some(r) = node.right.as_ref() {
            sum = O::mul(&sum, &r.data.sum);
        }
        node.data.sum = sum;
    }

    fn push(_node: &mut Node<Self>) {}
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
        Reverse { start: usize, end: usize },
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
    fn test_segtree() {
        let mut rng = StdRng::seed_from_u64(42);
        for tid in 1..=200 {
            let q = 50;
            let value_lim = 3;
            let len_max = rng.gen_range(5..=50);
            let mut n = 0usize;
            let mut seg = AvlSegtree::<O>::new();
            let mut vec = vec![];
            for qid in 1..=q {
                let query = match rng.gen_range(0..4) {
                    0 => {
                        let mut start = rng.gen_range(0..=n + 1);
                        let mut end = rng.gen_range(0..=n);
                        if start > end {
                            (start, end) = (end, start - 1);
                        }
                        Query::Reverse { start, end }
                    }
                    1 => {
                        let mut start = rng.gen_range(0..=n + 1);
                        let mut end = rng.gen_range(0..=n);
                        if start > end {
                            (start, end) = (end, start - 1);
                        }
                        Query::Product { start, end }
                    }
                    2..=3 => {
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
                    Query::Reverse { start, end } => {
                        seg.reverse(start, end);
                        vec[start..end].reverse();
                    }
                    Query::Product { start, end } => {
                        let result = seg.product(start, end);
                        let expected = vec[start..end]
                            .iter()
                            .fold(O::identity(), |x, &y| O::mul(&x, &y));
                        assert_eq!(result, expected);
                    }
                }
                eprintln!("{}", display(seg.tree.root.as_deref()));
                let result: Vec<_> = collect(seg.tree.root.as_deref())
                    .into_iter()
                    .map(|data| data.value)
                    .collect();
                eprintln!("   vec: {:?}", &vec);
                eprintln!(" rlist: {:?}", &result);
                assert_eq!(&vec, &result);
                validate(seg.tree.root.as_deref());
                eprintln!();
            }
        }
    }
}
