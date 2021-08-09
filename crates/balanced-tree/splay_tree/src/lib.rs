mod node;

#[cfg(test)]
mod brute;
#[cfg(test)]
mod test_dynamic_sequence_range_affine_range;

use self::node::{access_index, deep_free, merge, split_at, Node};
use std::{cell::Cell, fmt::Debug, iter::FromIterator, ops::Range, ptr::null_mut};

pub trait LazyOps {
    type Value: Value;
    type Acc: Value;
    type Lazy: Value;
    fn proj(value: &Self::Value) -> Self::Acc;
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value);
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc);
    fn compose(upper: &Self::Lazy, lower: &mut Self::Lazy);
    fn compose_to_option(upper: &Self::Lazy, lower: &mut Option<Self::Lazy>) {
        match lower {
            None => *lower = Some(upper.clone()),
            Some(lower) => Self::compose(upper, lower),
        }
    }
}

pub trait Value: Sized + Debug + Clone {}
impl<T: Sized + Debug + Clone> Value for T {}

pub struct SplayTree<O: LazyOps>(Cell<*mut Node<O>>);
impl<O: LazyOps> SplayTree<O> {
    pub fn new() -> Self {
        Self(Cell::new(null_mut()))
    }
    pub fn len(&self) -> usize {
        unsafe { self.0.get().as_ref() }.map_or(0, |root| root.len)
    }
    pub fn insert(&mut self, at: usize, value: O::Value) {
        let [left, right] = split_at(self.0.get(), at);
        let node = Box::leak(Box::new(Node::new(value)));
        self.0.set(merge(merge(left, node), right));
    }
    pub fn delete(&mut self, at: usize) -> O::Value {
        let [lc, r] = split_at(self.0.get(), at + 1);
        let [l, c] = split_at(lc, at);
        let ans = unsafe { Box::from_raw(c) }.value;
        self.0.set(merge(l, r));
        ans
    }
    pub fn reverse(&mut self, range: Range<usize>) {
        let Range { start, end } = range;
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        if let Some(c) = unsafe { c.as_mut() } {
            c.rev ^= true;
            c.push();
        }
        self.0.set(merge(merge(l, c), r));
    }
    pub fn get(&self, i: usize) -> Option<&O::Value> {
        if self.len() <= i {
            return None;
        }
        let mut root = unsafe { self.0.get().as_mut() }.unwrap();
        root = access_index(root, i);
        self.0.set(root);
        let ans = &root.value;
        Some(ans)
    }
    pub fn split_at(self, at: usize) -> [Self; 2] {
        let [left, right] = split_at(self.0.get(), at);
        [Self(Cell::new(left)), Self(Cell::new(right))]
    }
    pub fn fold(&self, range: Range<usize>) -> Option<O::Acc> {
        let Range { start, end } = range;
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        let ans = unsafe { c.as_mut() }.map(|c| {
            c.update();
            c.acc.clone()
        });
        self.0.set(merge(merge(l, c), r));
        ans
    }
    pub fn act(&mut self, range: Range<usize>, lazy: O::Lazy) {
        let Range { start, end } = range;
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        if let Some(c) = unsafe { c.as_mut() } {
            c.lazy = Some(lazy);
            c.push();
        }
        self.0.set(merge(merge(l, c), r));
    }
    pub fn dump(&self) {
        println!("    === start dump ===    ");
        match unsafe { self.0.get().as_ref() } {
            None => println!("empty"),
            Some(root) => root.dump(),
        }
        println!("    ===  end  dump ===    ");
    }
}

impl<O: LazyOps> FromIterator<O::Value> for SplayTree<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        let mut root = match iter.next() {
            None => return Self::new(),
            Some(value) => Box::leak(Box::new(Node::new(value))),
        };
        for value in iter {
            let node = Box::leak(Box::new(Node::new(value)));
            root.parent = node;
            node.left = root;
            node.update();
            root = node;
        }
        Self(Cell::new(root))
    }
}

impl<O: LazyOps> Drop for SplayTree<O> {
    fn drop(&mut self) {
        deep_free(self.0.get());
    }
}
