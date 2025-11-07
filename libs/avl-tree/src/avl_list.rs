use super::core::{Node, NodeMarker};
use crate::core::{merge2, merge3, split2_by_index, split3_by_index};
use std::fmt::Debug;
use std::marker::PhantomData;

#[allow(unused_imports)]
use crate::core::debug::display;

pub struct AvlList<T: Debug> {
    // TODO: remove
    root: Option<Box<Node<Marker<T>>>>,
}

impl<T: Debug> Default for AvlList<T> {
    // TODO: remove
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug> AvlList<T> {
    // TODO: remove
    pub fn new() -> Self {
        Self { root: None }
    }
    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }
    pub fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |x| x.len)
    }
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.len());
        let c = Box::new(Node::new(value));
        let (l, r) = split2_by_index(self.root.take(), index);
        self.root = Some(merge3(l, c, r));
    }
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len());
        let (l, c, r) = split3_by_index(self.root.take().unwrap(), index);
        self.root = merge2(l, r);
        c.data
    }
    pub fn split(&mut self, index: usize) -> (Self, Self) {
        assert!(index <= self.len());
        let (l, r) = split2_by_index(self.root.take(), index);
        (Self { root: l }, Self { root: r })
    }
    pub fn merge(lhs: Self, rhs: Self) -> Self {
        let root = merge2(lhs.root, rhs.root);
        Self { root }
    }
    pub fn reverse(&mut self, start: usize, end: usize) {
        assert!(start <= end && end <= self.len());
        let (lc, r) = split2_by_index(self.root.take(), end);
        let (l, mut c) = split2_by_index(lc, start);
        if let Some(c) = c.as_deref_mut() {
            c.rev ^= true;
        }
        let lc = merge2(l, c);
        self.root = merge2(lc, r);
    }
}

struct Marker<T> {
    __marker: PhantomData<T>,
}
impl<T: std::fmt::Debug> NodeMarker for Marker<T> {
    type Data = T; // remove

    fn update(_node: &mut Node<Self>) {}

    fn push(_node: &mut Node<Self>) {}
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
                eprintln!("{}", display(rlist.root.as_deref()));
                let result = collect(rlist.root.as_deref());
                eprintln!("   vec: {:?}", &vec);
                eprintln!(" rlist: {:?}", &result);
                assert_eq!(&vec, &result);
                validate(rlist.root.as_deref());
                eprintln!();
            }
        }
    }
}
