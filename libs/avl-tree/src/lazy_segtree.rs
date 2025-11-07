use super::core::{Node, NodeMarker};
use crate::core::AvlTree;
use std::fmt::Debug;
use std::marker::PhantomData;

pub struct AvlLazySegtree<O: Op> {
    core: AvlTree<Marker<O>>,
}

impl<O: Op> Default for AvlLazySegtree<O> {
    fn default() -> Self {
        Self::new()
    }
}

impl<O: Op> AvlLazySegtree<O> {
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
        self.core.touch(start, end, |c| c.rev ^= true);
    }

    pub fn product(&mut self, start: usize, end: usize) -> O::Value {
        self.core
            .touch(start, end, |c| c.data.prod.clone())
            .unwrap_or_else(O::identity)
    }

    pub fn apply(&mut self, start: usize, end: usize, op: &O::Operator) {
        self.core.touch(start, end, |c| {
            c.data.value = O::op(op, &c.data.value);
            c.data.prod = O::op(op, &c.data.prod);
            c.data.op = O::compose(op, &c.data.op);
        });
    }
}

impl<O: Op> FromIterator<O::Value> for AvlLazySegtree<O> {
    fn from_iter<I: IntoIterator<Item = O::Value>>(iter: I) -> Self {
        Self {
            core: iter.into_iter().map(Data::new).collect(),
        }
    }
}

pub trait Op {
    type Value: Clone + Debug; // TODO: remove

    type Operator: PartialEq + Eq + Debug; // TODO: remove

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    fn identity() -> Self::Value;

    fn nop() -> Self::Operator;

    fn op(f: &Self::Operator, x: &Self::Value) -> Self::Value;

    fn compose(f: &Self::Operator, g: &Self::Operator) -> Self::Operator;
}

struct Marker<O> {
    __marker: PhantomData<O>,
}

struct Data<O: Op> {
    value: O::Value,
    prod: O::Value,
    op: O::Operator,
}

impl<O: Op> Data<O> {
    fn new(value: O::Value) -> Self
    where
        O::Value: Clone,
    {
        Self {
            prod: value.clone(),
            value,
            op: O::nop(),
        }
    }
}

impl<O: Op> Debug for Data<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Data")
            .field("value", &self.value)
            .field("sum", &self.prod)
            .field("op", &self.op)
            .finish()
    }
}

impl<O: Op> Clone for Data<O>
where
    O::Operator: Clone,
{
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            prod: self.prod.clone(),
            op: self.op.clone(),
        }
    }
}

impl<O: Op> NodeMarker for Marker<O> {
    type Data = Data<O>;

    fn update(node: &mut Node<Self>) {
        let mut sum = node.data.value.clone();
        if let Some(l) = node.left.as_deref() {
            sum = O::mul(&l.data.prod, &sum);
        }
        if let Some(r) = node.right.as_deref() {
            sum = O::mul(&sum, &r.data.prod);
        }
        node.data.prod = sum;
    }

    fn push(node: &mut Node<Self>) {
        if node.data.op != O::nop() {
            let op = std::mem::replace(&mut node.data.op, O::nop());
            if let Some(l) = node.left.as_deref_mut() {
                l.data.prod = O::op(&op, &l.data.prod);
                l.data.value = O::op(&op, &l.data.value);
                l.data.op = O::compose(&op, &l.data.op);
            }
            if let Some(r) = node.right.as_deref_mut() {
                r.data.prod = O::op(&op, &r.data.prod);
                r.data.value = O::op(&op, &r.data.value);
                r.data.op = O::compose(&op, &r.data.op);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::debug::{display, validate};
    use fp::fp;
    use rand::Rng;
    use rand::{SeedableRng, rngs::StdRng};

    const P: u64 = 998_244_353;

    type Fp = fp::Fp<P>;

    #[derive(Debug)]
    enum Query {
        Insert {
            index: usize,
            value: (Fp, usize),
        },
        Remove {
            index: usize,
        },
        Reverse {
            start: usize,
            end: usize,
        },
        Product {
            start: usize,
            end: usize,
        },
        Apply {
            start: usize,
            end: usize,
            op: [Fp; 2],
        },
    }

    enum O {}

    impl Op for O {
        type Value = (Fp, usize);
        type Operator = [Fp; 2];

        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            (lhs.0 + rhs.0, lhs.1 + rhs.1)
        }

        fn identity() -> Self::Value {
            (fp!(0), 0)
        }

        fn nop() -> Self::Operator {
            [fp!(1), fp!(0)]
        }

        fn op(f: &Self::Operator, x: &Self::Value) -> Self::Value {
            (f[0] * x.0 + f[1] * fp!(x.1), x.1)
        }

        fn compose(f: &Self::Operator, g: &Self::Operator) -> Self::Operator {
            [f[0] * g[0], f[0] * g[1] + f[1]]
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
            let mut seg = AvlLazySegtree::<O>::new();
            let mut vec = vec![];
            for qid in 1..=q {
                let query = match rng.gen_range(0..5) {
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
                    2 => {
                        let mut start = rng.gen_range(0..=n + 1);
                        let mut end = rng.gen_range(0..=n);
                        if start > end {
                            (start, end) = (end, start - 1);
                        }
                        let op = [
                            Fp::new(rng.gen_range(0..value_lim)),
                            Fp::new(rng.gen_range(0..value_lim)),
                        ];
                        Query::Apply { start, end, op }
                    }
                    3..=4 => {
                        if rng.gen_ratio(n as u32, len_max) {
                            let index = rng.gen_range(0..n);
                            Query::Remove { index }
                        } else {
                            let index = rng.gen_range(0..=n);
                            let value = (Fp::new(rng.gen_range(0..value_lim)), 1);
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
                    Query::Apply { start, end, op } => {
                        seg.apply(start, end, &op);
                        for x in &mut vec[start..end] {
                            *x = O::op(&op, x);
                        }
                    }
                }
                eprintln!("{}", display(seg.core.root.as_deref()));
                // TODO: fix collect
                // let result: Vec<_> = collect(seg.core.root.as_deref())
                //     .into_iter()
                //     .map(|data| data.value)
                //     .collect();
                // eprintln!("   vec: {:?}", &vec);
                // eprintln!(" rlist: {:?}", &result);
                // assert_eq!(&vec, &result);
                validate(seg.core.root.as_deref());
                eprintln!();
            }
        }
    }
}
