use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

use super::node::Node;
use super::{Op, OrderStatisticMap};
use super::node::find_and_splay;

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

/// An entry in the map, either occupied or vacant.
pub enum Entry<'a, K, V, O: Op<Key = K, Value = V>> {
    Occupied(OccupiedEntry<'a, K, V, O>),
    Vacant(VacantEntry<'a, K, V, O>),
}

impl<'a, K: Ord, V, O: Op<Key = K, Value = V>> Entry<'a, K, V, O> {
    /// Returns a reference to the key.
    pub fn key(&self) -> &K {
        match self {
            Entry::Occupied(oe) => unsafe { &(*oe.node.as_ptr()).key },
            Entry::Vacant(ve) => &ve.key,
        }
    }

    /// Ensures a value is in the entry by inserting the default if empty,
    /// and returns a mutable reference to the value.
    pub fn or_insert(self, default: V) -> ValueMut<'a, K, V, O>
    where
        K: Clone,
    {
        self.or_insert_with(move || default)
    }

    /// Ensures a value is in the entry by inserting the result of the default function
    /// if empty, and returns a mutable reference to the value.
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> ValueMut<'a, K, V, O>
    where
        K: Clone,
    {
        match self {
            Entry::Occupied(oe) => oe.into_mut(),
            Entry::Vacant(ve) => ve.insert(default()),
        }
    }

    /// Ensures a value is in the entry by inserting the default value of `V` if empty,
    /// and returns a mutable reference to the value.
    pub fn or_default(self) -> ValueMut<'a, K, V, O>
    where
        K: Clone,
        V: Default,
    {
        self.or_insert_with(V::default)
    }

    /// Provides in-place mutable access to an occupied entry before any potential inserts
    /// into the map.
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut oe) => {
                f(&mut *oe.get_mut());
                Entry::Occupied(oe)
            }
            Entry::Vacant(ve) => Entry::Vacant(ve),
        }
    }
}

/// An occupied entry in the map.
pub struct OccupiedEntry<'a, K, V, O: Op<Key = K, Value = V>> {
    pub(super) node: NonNull<Node<K, V, O>>,
    pub(super) _map: PhantomData<&'a mut OrderStatisticMap<K, V, O>>,
}

impl<'a, K, V, O: Op<Key = K, Value = V>> OccupiedEntry<'a, K, V, O> {
    pub(super) fn new(node: NonNull<Node<K, V, O>>) -> Self {
        OccupiedEntry {
            node,
            _map: PhantomData,
        }
    }

    /// Gets a reference to the value in the entry.
    pub fn get(&self) -> &V {
        unsafe { &(*self.node.as_ptr()).value }
    }

    /// Gets a mutable reference to the value in the entry.
    pub fn get_mut(&mut self) -> &mut V {
        unsafe { &mut (*self.node.as_ptr()).value }
    }

    /// Consumes the entry and returns a mutable reference to the value.
    pub fn into_mut(self) -> ValueMut<'a, K, V, O> {
        ValueMut::new(self.node)
    }
}

/// A vacant entry in the map.
pub struct VacantEntry<'a, K, V, O: Op<Key = K, Value = V>> {
    pub(super) map: &'a mut OrderStatisticMap<K, V, O>,
    pub(super) key: K,
}

impl<'a, K: Ord + Clone, V, O: Op<Key = K, Value = V>> VacantEntry<'a, K, V, O> {
    /// Inserts the value and returns a mutable reference to it.
    pub fn insert(self, value: V) -> ValueMut<'a, K, V, O> {
        let key_ref = self.key.clone();
        self.map.insert(self.key, value);
        let node = find_and_splay(self.map, &key_ref).unwrap();
        ValueMut::new(node)
    }
}
