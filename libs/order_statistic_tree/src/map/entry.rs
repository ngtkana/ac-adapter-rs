use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use super::node::Node;
use super::Op;

/// A guard type that automatically recomputes aggregation when dropped.
/// Returned by `get_mut()` and `entry().or_insert*()`.
pub struct ValueMut<'a, K, V, O: Op<Key = K, Value = V>> {
    node: NonNull<Node<K, V, O>>,
    _marker: PhantomData<&'a mut K>,
}

impl<K, V, O: Op<Key = K, Value = V>> ValueMut<'_, K, V, O> {
    pub(super) fn new(node: NonNull<Node<K, V, O>>) -> Self {
        ValueMut {
            node,
            _marker: PhantomData,
        }
    }
}

impl<K, V, O: Op<Key = K, Value = V>> Deref for ValueMut<'_, K, V, O> {
    type Target = V;

    fn deref(&self) -> &V {
        unsafe { &(*self.node.as_ptr()).value }
    }
}

impl<K, V, O: Op<Key = K, Value = V>> DerefMut for ValueMut<'_, K, V, O> {
    fn deref_mut(&mut self) -> &mut V {
        unsafe { &mut (*self.node.as_ptr()).value }
    }
}

impl<K, V, O: Op<Key = K, Value = V>> Drop for ValueMut<'_, K, V, O> {
    fn drop(&mut self) {
        unsafe {
            (*self.node.as_ptr()).update();
        }
    }
}
