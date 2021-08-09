mod node;

#[cfg(test)]
mod brute;
#[cfg(test)]
mod test_dynamic_sequence_range_affine_range;
#[cfg(test)]
mod test_trivial;

use self::node::{access_index, deep_free, merge, split_at, Node};
use std::{
    cell::Cell,
    cmp::Ordering,
    fmt::Debug,
    hash::Hash,
    iter::FromIterator,
    marker::PhantomData,
    ops::{Bound, Deref, DerefMut, Index, Range, RangeBounds},
    ptr::null_mut,
};

pub struct Nop<T: Value>(PhantomData<fn(T) -> T>);
impl<T: Value> LazyOps for Nop<T> {
    type Value = T;
    type Acc = ();
    type Lazy = ();
    fn proj(_value: &Self::Value) -> Self::Acc {}
    fn op(&(): &Self::Acc, &(): &Self::Acc) -> Self::Acc {}
    fn act_value(&(): &Self::Lazy, _value: &mut Self::Value) {}
    fn act_acc(&(): &Self::Lazy, &mut (): &mut Self::Acc) {}
    fn compose(&(): &Self::Lazy, &mut (): &mut Self::Lazy) {}
}

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
    pub fn is_empty(&self) -> bool {
        self.0.get().is_null()
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
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Acc> {
        let Range { start, end } = into_range(self.len(), range);
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        let ans = unsafe { c.as_mut() }.map(|c| {
            c.update();
            c.acc.clone()
        });
        self.0.set(merge(merge(l, c), r));
        ans
    }
    pub fn act(&mut self, range: impl RangeBounds<usize>, lazy: O::Lazy) {
        let Range { start, end } = into_range(self.len(), range);
        let [lc, r] = split_at(self.0.get(), end);
        let [l, c] = split_at(lc, start);
        if let Some(c) = unsafe { c.as_mut() } {
            c.lazy = Some(lazy);
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
    pub fn entry(&mut self, i: usize) -> Option<Entry<'_, O>> {
        if self.len() <= i {
            return None;
        }
        let mut root = unsafe { self.0.get().as_mut() }.unwrap();
        root = access_index(root, i);
        self.0.set(root);
        Some(Entry(self))
    }
    pub fn split_at(self, at: usize) -> [Self; 2] {
        let [left, right] = split_at(self.0.get(), at);
        [Self(Cell::new(left)), Self(Cell::new(right))]
    }
    pub fn iter(&self) -> Iter<'_, O> {
        Iter {
            splay: self,
            start: 0,
            end: self.len(),
        }
    }
    pub fn range(&self, range: impl RangeBounds<usize>) -> Iter<'_, O> {
        let Range { start, end } = into_range(self.len(), range);
        Iter {
            splay: self,
            start,
            end,
        }
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

impl<O: LazyOps> Debug for SplayTree<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
impl<O: LazyOps> Clone for SplayTree<O> {
    fn clone(&self) -> Self {
        self.iter().cloned().collect()
    }
}
impl<O: LazyOps> Default for SplayTree<O> {
    fn default() -> Self {
        Self(Cell::new(null_mut()))
    }
}
impl<O: LazyOps> PartialEq for SplayTree<O>
where
    O::Value: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.len() == other.len() && self.iter().zip(other.iter()).all(|(x, y)| x == y)
    }
}
impl<O: LazyOps> Eq for SplayTree<O> where O::Value: Eq {}
impl<O: LazyOps> PartialOrd for SplayTree<O>
where
    O::Value: PartialOrd,
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        for (x, y) in self.iter().zip(other.iter()) {
            match x.partial_cmp(y) {
                Some(Ordering::Equal) => (),
                non_eq => return non_eq,
            }
        }
        self.len().partial_cmp(&other.len())
    }
}
impl<O: LazyOps> Ord for SplayTree<O>
where
    O::Value: Ord,
{
    fn cmp(&self, other: &Self) -> Ordering {
        for (x, y) in self.iter().zip(other.iter()) {
            match x.cmp(y) {
                Ordering::Equal => (),
                non_eq => return non_eq,
            }
        }
        self.len().cmp(&other.len())
    }
}
impl<O: LazyOps> Hash for SplayTree<O>
where
    O::Value: Hash,
{
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.iter().for_each(|x| x.hash(state))
    }
}

impl<O: LazyOps> Index<usize> for SplayTree<O> {
    type Output = O::Value;
    fn index(&self, index: usize) -> &Self::Output {
        if self.len() <= index {
            splay_tree_index_out_of_range_fail(index, self.len());
        }
        self.get(index).unwrap()
    }
}

pub struct Iter<'a, O: LazyOps> {
    splay: &'a SplayTree<O>,
    start: usize,
    end: usize,
}
impl<'a, O: LazyOps> Iterator for Iter<'a, O> {
    type Item = &'a O::Value;
    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            let ans = self.splay.get(self.start).unwrap();
            self.start += 1;
            Some(ans)
        }
    }
}
impl<'a, O: LazyOps> DoubleEndedIterator for Iter<'a, O> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            self.end -= 1;
            let ans = self.splay.get(self.end).unwrap();
            Some(ans)
        }
    }
}

pub struct Entry<'a, O: LazyOps>(&'a mut SplayTree<O>);
impl<O: LazyOps> Deref for Entry<'_, O> {
    type Target = O::Value;
    fn deref(&self) -> &Self::Target {
        &unsafe { &*self.0 .0.get() }.value
    }
}
impl<O: LazyOps> DerefMut for Entry<'_, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut unsafe { &mut *self.0 .0.get() }.value
    }
}

impl<O: LazyOps> Drop for SplayTree<O> {
    fn drop(&mut self) {
        deep_free(self.0.get());
    }
}
fn into_range(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(&start) => start,
        Bound::Excluded(&start) => start - 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound() {
        Bound::Included(&end) => end + 1,
        Bound::Excluded(&end) => end,
        Bound::Unbounded => len,
    };
    if len < start {
        splay_tree_start_index_len_fail(start, len);
    }
    if len < end {
        splay_tree_end_index_len_fail(end, len);
    }
    if start > end {
        splay_tree_index_order_fail(start, end)
    }
    start..end
}
fn splay_tree_index_out_of_range_fail(index: usize, len: usize) -> ! {
    panic!(
        "range index {} out of range for splay tree of length {}",
        index, len
    );
}
fn splay_tree_start_index_len_fail(index: usize, len: usize) -> ! {
    panic!(
        "range start index {} out of range for splay tree of length {}",
        index, len
    );
}
fn splay_tree_end_index_len_fail(index: usize, len: usize) -> ! {
    panic!(
        "range end index {} out of range for splay tree of length {}",
        index, len
    );
}
fn splay_tree_index_order_fail(index: usize, end: usize) -> ! {
    panic!("splay tree index starts at {} but ends at {}", index, end);
}
