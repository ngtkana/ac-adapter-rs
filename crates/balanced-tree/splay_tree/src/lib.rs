mod node;

use {
    node::{get, merge, split, Node},
    std::{
        cell::Cell,
        fmt::Debug,
        iter::FromIterator,
        marker::PhantomData,
        ops::{Bound, Range, RangeBounds},
        ptr::null_mut,
    },
};

/// [`Acc`](Ops::Acc), [`Lazy`](Ops::Lazy) をユニット型にして、演算を回避する型です。
pub struct Nop<T>(PhantomData<fn(T) -> T>);
impl<T: Value> Ops for Nop<T> {
    type Value = T;
    type Acc = ();
    type Lazy = ();
    fn proj(_: &Self::Value) -> Self::Acc {}
    fn op(&(): &Self::Acc, &(): &Self::Acc) -> Self::Acc {}
    fn act_value(&(): &Self::Lazy, _value: &mut Self::Value) {}
    fn act_acc(&(): &Self::Lazy, &mut (): &mut Self::Acc) {}
    fn lazy_propagate(&(): &Self::Lazy, &mut (): &mut Self::Lazy) {}
}

/// [`Sized`], [`Debug`], [`Clone`] 取りまとめ役です。
pub trait Value: Sized + Debug + Clone {}
impl<T: Sized + Debug + Clone> Value for T {}

/// 演算
pub trait Ops {
    /// 値型
    type Value: Value;
    /// 集約値型
    type Acc: Value;
    /// 遅延値型
    type Lazy: Value;
    /// 集約化
    fn proj(value: &Self::Value) -> Self::Acc;
    /// 演算
    fn op(lhs: &Self::Acc, rhs: &Self::Acc) -> Self::Acc;
    /// 値への作用
    fn act_value(lazy: &Self::Lazy, value: &mut Self::Value);
    /// 集約値への作用
    fn act_acc(lazy: &Self::Lazy, acc: &mut Self::Acc);
    /// 遅延値の伝播
    fn lazy_propagate(upper: &Self::Lazy, lower: &mut Self::Lazy);
}

pub struct SplayTree<O: Ops> {
    root: Cell<*mut Node<O>>,
}
impl<O: Ops> FromIterator<O::Value> for SplayTree<O> {
    fn from_iter<T: IntoIterator<Item = O::Value>>(iter: T) -> Self {
        let mut root = null_mut();
        for value in iter {
            let node = Box::into_raw(Box::new(Node::new(value)));
            root = unsafe { merge(root, node) };
        }
        let root = Cell::new(root);
        Self { root }
    }
}
impl<O: Ops> SplayTree<O> {
    pub fn len(&self) -> usize {
        let root = self.root.get();
        unsafe { root.as_ref() }.map_or(0, |root| root.len)
    }
    pub fn get(&mut self, index: usize) -> &O::Value {
        let root = self.root.get();
        let root = unsafe { get(root, index).as_mut() }.unwrap();
        self.root.set(root);
        &root.value
    }
    pub fn get_mut(&mut self, index: usize) -> &mut O::Value {
        let root = self.root.get();
        let root = unsafe { get(root, index).as_mut() }.unwrap();
        self.root.set(root);
        unsafe { root.update() };
        &mut root.value
    }
    pub fn act(&mut self, start: usize, end: usize, lazy: O::Lazy) {
        let root = self.root.get();
        let [lc, r] = unsafe { split(root, end) };
        let [l, c] = unsafe { split(lc, start) };
        unsafe {
            if let Some(c) = c.as_mut() {
                c.lazy = Some(lazy);
                c.push();
            }
        }
        self.root.set(unsafe { merge(merge(l, c), r) });
    }
    pub fn fold(&self, range: impl RangeBounds<usize>) -> Option<O::Acc> {
        let Range { start, end } = into_range(self.len(), range);
        let root = self.root.get();
        let [lc, r] = unsafe { split(root, end) };
        let [l, c] = unsafe { split(lc, start) };
        let ans = unsafe { c.as_ref() }.map(|c| c.acc.clone());
        self.root.set(unsafe { merge(merge(l, c), r) });
        ans
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
