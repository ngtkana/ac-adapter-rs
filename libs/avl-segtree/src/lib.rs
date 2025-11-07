use avl_core::{CoreTree, Node, NodeMarker};
use std::{fmt::Debug, marker::PhantomData};

pub struct AvlSegtree<O: Op> {
    core: CoreTree<Marker<O>>,
}

impl<O: Op> Default for AvlSegtree<O> {
    fn default() -> Self {
        Self {
            core: CoreTree::default(),
        }
    }
}

impl<O: Op> FromIterator<O::Value> for AvlSegtree<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        Self {
            core: iter.into_iter().map(Data::new).collect(),
        }
    }
}

impl<O: Op> AvlSegtree<O> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn is_empty(&self) -> bool {
        self.core.is_empty()
    }
    pub fn len(&self) -> usize {
        self.core.len()
    }
    pub fn insert(&mut self, index: usize, value: O::Value) {
        self.core.insert(index, Data::new(value));
    }
    pub fn remove(&mut self, index: usize) -> O::Value {
        self.core.remove(index).value
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
        self.core.reverse(start, end);
    }
    pub fn product(&mut self, start: usize, end: usize) -> O::Value {
        let r = self.split_off(end);
        let mut c = self.split_off(start);
        let result = c
            .core
            .total()
            .map_or_else(O::identity, |data| data.prod.clone());
        self.append(c);
        self.append(r);
        result
    }
    pub fn to_vec(&mut self) -> Vec<O::Value> {
        self.core.to_vec(|data| data.value.clone())
    }
}

pub trait Op {
    type Value: Clone;

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    fn identity() -> Self::Value;
}

struct Marker<O> {
    __marker: PhantomData<O>,
}

struct Data<O: Op> {
    value: O::Value,
    prod: O::Value,
}

impl<O: Op> Data<O> {
    fn new(value: O::Value) -> Self
    where
        O::Value: Clone,
    {
        Self {
            prod: value.clone(),
            value,
        }
    }
}

// TODO: this is needless
impl<O: Op> Debug for Data<O>
where
    O::Value: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Data")
            .field("value", &self.value)
            .field("prod", &self.prod)
            .finish()
    }
}

impl<O: Op> NodeMarker for Marker<O> {
    type Data = Data<O>;

    fn update(node: &mut Node<Self>) {
        node.data.prod = O::identity();
        if let Some(l) = node.left.as_ref() {
            node.data.prod = O::mul(&node.data.prod, &l.data.prod);
        }
        node.data.prod = O::mul(&node.data.prod, &node.data.value);
        if let Some(r) = node.right.as_ref() {
            node.data.prod = O::mul(&node.data.prod, &r.data.prod);
        }
    }

    fn push(_node: &mut Node<Self>) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use avl_core::display;
    use avl_core::validate;
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
            let len_max = 3;
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
                eprintln!("{}", display(&seg.core));
                let result = seg.to_vec();
                eprintln!("   vec: {:?}", &vec);
                eprintln!(" rlist: {:?}", &result);
                assert_eq!(&vec, &result);
                validate(&seg.core);
                eprintln!();
            }
        }
    }
}
