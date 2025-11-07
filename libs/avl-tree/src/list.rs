use super::core::{AvlTree, NodeMarker};
use std::marker::PhantomData;

pub struct AvlList<T> {
    core: AvlTree<Marker<T>>,
}

impl<T> Default for AvlList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> AvlList<T> {
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

    pub fn insert(&mut self, index: usize, value: T) {
        self.core.insert(index, value);
    }

    pub fn remove(&mut self, index: usize) -> T {
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
        self.core.reverse(start, end);
    }
}

impl<T> FromIterator<T> for AvlList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            core: iter.into_iter().collect(),
        }
    }
}

struct Marker<T> {
    __marker: PhantomData<T>,
}
impl<T> NodeMarker for Marker<T> {
    type Value = T;

    type Prod = ();

    type Operator = ();

    fn singleton(_value: &T) -> Self::Prod {}

    fn mul(&(): &Self::Prod, &(): &Self::Prod) -> Self::Prod {}

    fn identity() -> Self::Prod {}

    fn nop() {}

    fn op_value(&(): &Self::Operator, _: &mut T) {}

    fn op_prod(&(): &Self::Operator, (): &mut Self::Prod, _len: usize) {}

    fn compose(&(): &Self::Operator, &mut (): &mut Self::Operator) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::debug::{collect, display, validate};
    use rand::Rng;
    use rand::{SeedableRng, rngs::StdRng};

    #[derive(Debug)]
    enum Query {
        Insert { index: usize, value: i32 },
        Remove { index: usize },
        Reverse { start: usize, end: usize },
    }

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(42);
        for tid in 1..=200 {
            let q = 50;
            let value_lim = 10;
            let len_max = rng.gen_range(5..=50);
            let mut n = 0usize;
            let mut rlist = AvlList::new();
            let mut vec = vec![];
            for qid in 1..=q {
                let query = match rng.gen_range(0..3) {
                    0 => {
                        let mut start = rng.gen_range(0..=n + 1);
                        let mut end = rng.gen_range(0..=n);
                        if start > end {
                            (start, end) = (end, start - 1);
                        }
                        Query::Reverse { start, end }
                    }
                    1..=2 => {
                        if rng.gen_ratio(n as u32, len_max) {
                            let index = rng.gen_range(0..n);
                            Query::Remove { index }
                        } else {
                            let index = rng.gen_range(0..=n);
                            let value = rng.gen_range(0..value_lim);
                            Query::Insert { index, value }
                        }
                    }
                    _ => unreachable!(),
                };
                eprintln!("Query #{tid}.{qid}: {query:?}");
                match query {
                    Query::Insert { index, value } => {
                        rlist.insert(index, value);
                        vec.insert(index, value);
                        n += 1;
                    }
                    Query::Remove { index } => {
                        let result = rlist.remove(index);
                        let expected = vec.remove(index);
                        assert_eq!(result, expected);
                        n -= 1;
                    }
                    Query::Reverse { start, end } => {
                        rlist.reverse(start, end);
                        vec[start..end].reverse();
                    }
                }
                eprintln!("{}", display(rlist.core.root.as_deref()));
                let result = collect(rlist.core.root.as_deref());
                eprintln!("   vec: {:?}", &vec);
                eprintln!(" rlist: {:?}", &result);
                assert_eq!(&vec, &result);
                validate(rlist.core.root.as_deref());
                eprintln!();
            }
        }
    }
}
