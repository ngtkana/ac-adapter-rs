use std::marker::PhantomData;

use avl_core::{CoreTree, Node, NodeMarker};
pub struct AvlList<T> {
    core: CoreTree<Marker<T>>,
}

impl<T> Default for AvlList<T> {
    fn default() -> Self {
        Self {
            core: CoreTree::default(),
        }
    }
}

impl<T> AvlList<T> {
    pub fn new() -> Self {
        Self::default()
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
    pub fn to_vec(&mut self) -> Vec<T>
    where
        T: Clone,
    {
        self.core.to_vec(Clone::clone)
    }
}

struct Marker<T> {
    __marker: PhantomData<T>,
}
impl<T> NodeMarker for Marker<T> {
    type Data = T;

    fn update(_node: &mut Node<Self>) {}

    fn push(_node: &mut Node<Self>) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use avl_core::{display, validate};
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
            let mut avl = AvlList::new();
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
                        avl.insert(index, value);
                        vec.insert(index, value);
                        n += 1;
                    }
                    Query::Remove { index } => {
                        let result = avl.remove(index);
                        let expected = vec.remove(index);
                        assert_eq!(result, expected);
                        n -= 1;
                    }
                    Query::Reverse { start, end } => {
                        avl.reverse(start, end);
                        vec[start..end].reverse();
                    }
                }
                eprintln!("{}", display(&avl.core));
                let result = avl.to_vec();
                eprintln!("   vec: {:?}", &vec);
                eprintln!(" rlist: {:?}", &result);
                assert_eq!(&vec, &result);
                validate(&avl.core);
                eprintln!();
            }
        }
    }
}
