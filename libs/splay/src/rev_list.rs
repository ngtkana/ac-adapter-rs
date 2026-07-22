use std::{marker::PhantomData, ops::RangeBounds};

use crate::{Marker, Tree};

pub struct RevList<T> {
    tree: Tree<ListMarker<T>>,
}

struct ListMarker<T> {
    __marker: PhantomData<T>,
}

impl<T> Marker for ListMarker<T> {
    type Value = T;

    type Prod = ();

    type Op = ();

    type Rev = bool;

    fn identity() -> Self::Prod {}

    fn to_prod(_value: &Self::Value) -> Self::Prod {}

    fn mul_assign_from_left(_lhs: &Self::Prod, _rhs: &mut Self::Prod) {}

    fn mul_assign_from_right(_lhs: &mut Self::Prod, _rhs: &Self::Prod) {}

    fn act_on_value(_op: &Self::Op, _value: &mut Self::Value) {}

    fn act_on_prod(_op: &Self::Op, _prod: &mut Self::Prod) {}

    fn act_on_op(_lhs: &Self::Op, _rhs: &mut Self::Op) {}

    fn nop() -> Self::Op {}

    fn is_nop(_op: &Self::Op) -> bool {
        true
    }

    fn rev(rev: &Self::Rev) -> bool {
        *rev
    }

    fn rev_false() -> Self::Rev {
        false
    }

    fn flip_rev(rev: &mut Self::Rev) {
        *rev ^= true;
    }
}

// Public inherent methods for RevList<T>
impl<T> Default for RevList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> RevList<T> {
    pub fn new() -> Self {
        Tree::new().into()
    }

    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    pub fn len(&self) -> usize {
        self.tree.len()
    }

    pub fn insert(&mut self, index: usize, value: T) {
        self.tree.insert(index, value);
    }

    pub fn remove(&mut self, index: usize) -> T {
        self.tree.remove(index)
    }

    pub fn append(&mut self, other: Self) {
        self.tree.append(other.tree);
    }

    pub fn split_off(&mut self, index: usize) -> Self {
        self.tree.split_off(index).into()
    }

    pub fn reverse(&mut self, range: impl RangeBounds<usize>) {
        self.tree.reverse(range);
    }

    pub fn collect_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.tree.collect_vec()
    }
}

impl<T> From<Tree<ListMarker<T>>> for RevList<T> {
    fn from(tree: Tree<ListMarker<T>>) -> Self {
        Self { tree }
    }
}

impl<T> FromIterator<T> for RevList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter().collect::<Tree<_>>().into()
    }
}

#[cfg(test)]
mod tests {
    use rand::{rngs::StdRng, Rng, SeedableRng};

    use crate::test_util::pretty;

    use super::*;

    #[derive(Debug, Clone, Copy)]
    enum Query {
        Insert { index: usize, value: u32 },
        Remove { index: usize },
    }

    #[test]
    fn test_insert_list() {
        let mut rng = StdRng::seed_from_u64(42);
        let value_lim = 100;
        for tid in 1..=200 {
            let len_max = 20usize;
            let queries: Vec<_> = std::iter::repeat_n((), 100)
                .scan(0usize, |n, ()| {
                    Some(if rng.gen_ratio(*n as u32, len_max as u32) {
                        let index = rng.gen_range(0..*n);
                        *n -= 1;
                        Query::Remove { index }
                    } else {
                        let index = rng.gen_range(0..=*n);
                        let value = rng.gen_range(0..value_lim);
                        *n += 1;
                        Query::Insert { index, value }
                    })
                })
                .collect();

            let mut list = RevList::new();
            let mut vec = vec![];
            for (qid, &query) in queries.iter().enumerate() {
                eprintln!("=== Query #{tid}.{qid}: {query:?}");

                match query {
                    Query::Insert { index, value } => {
                        vec.insert(index, value);
                        list.insert(index, value);
                    }
                    Query::Remove { index } => {
                        let expected = vec.remove(index);
                        let result = list.remove(index);
                        assert_eq!(result, expected);
                    }
                }

                eprintln!("vec = {:?}", &vec);
                eprintln!("list =\n{}", pretty(&list.tree));
                assert_eq!(list.collect_vec(), vec);
                eprintln!();
            }
        }
    }
}
