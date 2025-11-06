use super::node::{Node, NodeMarker};
use crate::node::{merge3, split2_by_index};
use procon_lg::lg_recur;
use std::fmt::Debug;
use std::marker::PhantomData;

#[allow(unused_imports)]
use crate::node::debug::display;

pub struct ReversibleList<T: Debug> {
    // TODO: remove
    root: Option<Box<Node<Marker<T>>>>,
}

impl<T: Debug> Default for ReversibleList<T> {
    // TODO: remove
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug> ReversibleList<T> {
    // TODO: remove
    pub fn new() -> Self {
        Self { root: None }
    }
    #[lg_recur]
    pub fn insert(&mut self, index: usize, value: T) {
        let c = Box::new(Node::new(value));
        let (l, r) = split2_by_index(self.root.take(), index);
        self.root = Some(merge3(l, c, r));
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
    use crate::node::debug::{collect, display, validate};
    use rand::Rng;
    use rand::{SeedableRng, rngs::StdRng};

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(42);
        for tid in 1..=200 {
            let q = 20;
            let value_lim = 10;
            let mut n = 0;
            let mut rlist = ReversibleList::new();
            let mut vec = vec![];
            #[allow(clippy::explicit_counter_loop)]
            for qid in 1..=q {
                {
                    let index = rng.gen_range(0..=n);
                    let value = rng.gen_range(0..value_lim);
                    eprintln!("Query #{tid}.{qid}: Insert({index}, {value})");
                    rlist.insert(index, value);
                    vec.insert(index, value);
                    eprintln!("{}", display(rlist.root.as_deref()));
                    n += 1;
                }
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
