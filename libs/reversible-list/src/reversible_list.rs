use crate::node::{merge3, split2_by_index};

use super::node::{Node, NodeMarker};
use std::marker::PhantomData;

pub struct ReversibleList<T> {
    root: Option<Box<Node<Marker<T>>>>,
}

impl<T> Default for ReversibleList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> ReversibleList<T> {
    pub fn new() -> Self {
        Self { root: None }
    }
    pub fn insert(&mut self, index: usize, value: T) {
        let c = Box::new(Node::new(value));
        let (l, r) = split2_by_index(self.root.take(), index);
        self.root = Some(merge3(l, c, r));
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
    use crate::node::tests::display;
    use rand::Rng;
    use rand::{SeedableRng, rngs::StdRng};

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(42);
        for tid in 1..=200 {
            let q = 200;
            let value_lim = 10;
            let mut n = 0;
            let mut rlist = ReversibleList::new();
            #[allow(clippy::explicit_counter_loop)]
            for qid in 1..=q {
                let index = rng.gen_range(0..=n);
                let value = rng.gen_range(0..value_lim);
                eprintln!("Query #{tid}.#{qid}: Insert({index}, {value})");
                rlist.insert(index, value);
                eprintln!("{}", display(rlist.root.as_deref()));
                n += 1;
            }
        }
    }
}
