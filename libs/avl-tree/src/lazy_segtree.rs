use super::core::NodeMarker;
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
            O::op(op, &mut c.data.value, 1);
            O::op(op, &mut c.data.prod, c.len);
            O::compose(op, &mut c.op);
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

    type Operator: PartialEq + Debug; // TODO: remove

    fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value;

    fn identity() -> Self::Value;

    fn nop() -> Self::Operator;

    fn op(f: &Self::Operator, x: &mut Self::Value, len: usize);

    fn compose(f: &Self::Operator, g: &mut Self::Operator);
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

impl<O: Op> Debug for Data<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Data")
            .field("value", &self.value)
            .field("sum", &self.prod)
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
        }
    }
}

impl<O: Op> NodeMarker for Marker<O> {
    type Data = Data<O>;

    type Operator = O::Operator;

    fn update(data: &mut Data<O>, left: Option<&Data<O>>, right: Option<&Data<O>>) {
        let mut prod = O::identity();
        if let Some(l) = left {
            prod = O::mul(&prod, &l.prod);
        }
        prod = O::mul(&prod, &data.value);
        if let Some(r) = right {
            prod = O::mul(&prod, &r.prod);
        }
        data.prod = prod;
    }

    fn nop() -> Self::Operator {
        O::nop()
    }

    fn op(f: &Self::Operator, x: &mut Self::Data, len: usize) {
        O::op(f, &mut x.value, 1);
        O::op(f, &mut x.prod, len);
    }

    fn compose(f: &Self::Operator, g: &mut Self::Operator) {
        O::compose(f, g);
    }
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
        Insert {
            index: usize,
            value: Fp,
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
        type Value = Fp;
        type Operator = [Fp; 2];

        fn mul(lhs: &Self::Value, rhs: &Self::Value) -> Self::Value {
            lhs + rhs
        }

        fn identity() -> Self::Value {
            fp!(0)
        }

        fn nop() -> Self::Operator {
            [fp!(1), fp!(0)]
        }

        fn op(f: &Self::Operator, x: &mut Self::Value, len: usize) {
            *x = f[0] * *x + f[1] * fp!(len);
        }

        fn compose(f: &Self::Operator, g: &mut Self::Operator) {
            *g = [f[0] * g[0], f[0] * g[1] + f[1]];
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
                            let value = Fp::new(rng.gen_range(0..value_lim));
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
                            O::op(&op, x, 1);
                        }
                    }
                }
                eprintln!("{}", display(seg.core.root.as_deref()));
                let result: Vec<_> = collect(seg.core.root.as_deref())
                    .into_iter()
                    .map(|data| data.value)
                    .collect();
                eprintln!("   vec: {:?}", &vec);
                eprintln!(" rlist: {:?}", &result);
                assert_eq!(&vec, &result);
                validate(seg.core.root.as_deref());
                eprintln!();
            }
        }
    }
}
