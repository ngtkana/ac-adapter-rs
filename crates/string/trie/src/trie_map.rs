use {
    super::DEGREE,
    std::fmt::{self, Debug, Formatter},
};

/// A map base on a trie.
#[derive(Clone, PartialEq)]
pub struct TrieMap<V>(Option<Box<Node<V>>>);

impl<V: Debug> Debug for TrieMap<V> {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        let mut f = w.debug_map();
        self.for_each_kv(|k, v| {
            f.key(&k.to_vec()).value(v);
        });
        f.finish()
    }
}

impl<V> Default for TrieMap<V> {
    fn default() -> Self {
        Self(None)
    }
}

impl<V> TrieMap<V> {
    /// Makes a new empty TrieMap.
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    ///
    /// // entries can now be inserted into the empty map
    /// map.insert(once(1), "a");
    /// ```
    pub fn new() -> Self {
        Self(None)
    }

    /// Inserts a key-value pair into the map.
    ///
    /// If the map did not have this key present, `None` is returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. The key is not updated, though.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// assert_eq!(map.insert(once(17), "a"), None);
    /// // assert_eq!(map.is_empty(), false); TODO: unimplemented
    ///
    /// map.insert(once(17), "b");
    /// assert_eq!(map.insert(once(17), "c"), Some("b"));
    /// // assert_eq!(map[&37], "c"); TODO: unimplemented
    /// ```
    pub fn insert(&mut self, key: impl IntoIterator<Item = usize>, value: V) -> Option<V> {
        let mut key = key.into_iter();
        let me = self.0.get_or_insert_with(|| Box::new(Node::new()));
        let next = key.next();
        if let Some(next) = next {
            me.child[next].insert(key, value)
        } else {
            me.value.replace(value)
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    /// assert_eq!(map.get(once(1)), Some(&"a"));
    /// assert_eq!(map.get(once(2)), None);
    /// ```
    pub fn get(&self, key: impl IntoIterator<Item = usize>) -> Option<&V> {
        let mut key = key.into_iter();
        let me = self.0.as_deref()?;
        let next = key.next();
        if let Some(next) = next {
            me.child[next].get(key)
        } else {
            me.value.as_ref()
        }
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    /// if let Some(x) = map.get_mut(once(1)) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map.get(once(1)), Some(&"b"));
    /// // assert_eq!(map[&1], "b"); TODO: unimplemented
    /// ```
    pub fn get_mut(&mut self, key: impl IntoIterator<Item = usize>) -> Option<&mut V> {
        let mut key = key.into_iter();
        let me = self.0.as_deref_mut()?;
        let next = key.next();
        if let Some(next) = next {
            me.child[next].get_mut(key)
        } else {
            me.value.as_mut()
        }
    }

    /// Inserts a `value` at `key` if it is [`None`], then returns a mutable reference
    /// to the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    ///
    /// // Existing
    /// map.get_or_insert(once(1), "b");
    /// assert_eq!(map.get(once(1)), Some(&"a"));
    ///
    /// // New
    /// map.get_or_insert(once(2), "c");
    /// assert_eq!(map.get(once(2)), Some(&"c"));
    ///
    /// // assert_eq!(map[&1], "b"); TODO: unimplemented
    pub fn get_or_insert(&mut self, key: impl IntoIterator<Item = usize>, value: V) -> &mut V {
        let mut key = key.into_iter();
        let me = self.0.get_or_insert_with(|| Box::new(Node::new()));
        let next = key.next();
        if let Some(next) = next {
            me.child[next].get_or_insert(key, value)
        } else {
            me.value.get_or_insert(value)
        }
    }

    /// Inserts a value computed from `f` at `key` if it is [`None`],
    /// then returns a mutable reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    ///
    /// // Existing
    /// map.get_or_insert_with(once(1), || "b");
    /// assert_eq!(map.get(once(1)), Some(&"a"));
    ///
    /// // New
    /// map.get_or_insert_with(once(2), || "c");
    /// assert_eq!(map.get(once(2)), Some(&"c"));
    ///
    /// // assert_eq!(map[&1], "b"); TODO: unimplemented
    pub fn get_or_insert_with(
        &mut self,
        key: impl IntoIterator<Item = usize>,
        f: impl FnOnce() -> V,
    ) -> &mut V {
        let mut key = key.into_iter();
        let me = self.0.get_or_insert_with(|| Box::new(Node::new()));
        let next = key.next();
        if let Some(next) = next {
            me.child[next].get_or_insert_with(key, f)
        } else {
            me.value.get_or_insert_with(f)
        }
    }

    /// Visits all the "existing" nodes corresponding to the preficies of the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(vec![1], "a");
    /// map.insert(vec![1, 1, 1], "c");
    ///
    /// // Corresponding an existing key.
    /// let mut expected = [None, Some("a"), None, Some("c")].iter();
    /// map.for_each_prefix(vec![1, 1, 1].into_iter(), |trie| {
    ///     let expected = expected.next().unwrap().as_ref();
    ///     assert_eq!(trie.get(None.into_iter()), expected);
    /// });
    ///
    /// // No, but falls within the trie.
    /// let mut expected = [None, Some("a"), None].iter();
    /// map.for_each_prefix(vec![1, 1].into_iter(), |trie| {
    ///     let expected = expected.next().unwrap().as_ref();
    ///     assert_eq!(trie.get(None.into_iter()), expected);
    /// });
    ///
    /// // Runs off thte trie.
    /// let mut expected = [None, Some("a"), None, Some("c")].iter();
    /// map.for_each_prefix(vec![1, 1, 1, 1].into_iter(), |trie| {
    ///     let expected = expected.next().unwrap().as_ref();
    ///     assert_eq!(trie.get(None.into_iter()), expected);
    /// });
    /// ```
    pub fn for_each_prefix(
        &self,
        key: impl IntoIterator<Item = usize>,
        mut visit: impl FnMut(&TrieMap<V>),
    ) {
        let mut key = key.into_iter();
        if let Some(me) = self.0.as_deref() {
            visit(self);
            let next = key.next();
            if let Some(next) = next {
                me.child[next].for_each_prefix(key, visit);
            }
        }
    }

    /// Visits all the pairs of a key of a values in the trie, in lexicographic order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(vec![1, 2, 2], "a");
    /// map.insert(vec![2], "b");
    /// map.insert(vec![1], "c");
    /// map.insert(vec![1, 1, 1], "d");
    ///
    /// let mut expected = vec![
    ///     (vec![1], "c"),
    ///     (vec![1, 1, 1], "d"),
    ///     (vec![1, 2, 2], "a"),
    ///     (vec![2], "b")
    /// ].into_iter();
    /// map.for_each_kv(|k, &v| {
    ///     let (ek, ev) = expected.next().unwrap();
    ///     assert_eq!(k, ek);
    ///     assert_eq!(v, ev);
    /// });
    ///
    ///
    /// ```
    pub fn for_each_kv(&self, mut visit: impl FnMut(&[usize], &V)) {
        let mut prefix = Vec::new();
        self.for_each_kv_impl(&mut prefix, &mut visit);
        assert!(prefix.is_empty());
    }
    fn for_each_kv_impl(&self, prefix: &mut Vec<usize>, visit: &mut impl FnMut(&[usize], &V)) {
        if let Some(me) = self.0.as_deref() {
            if let Some(value) = me.value.as_ref() {
                visit(prefix, value);
            }
            for (i, child) in me.child.iter().enumerate() {
                prefix.push(i);
                child.for_each_kv_impl(prefix, visit);
                prefix.pop();
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct Node<V> {
    pub(super) value: Option<V>,
    pub(super) child: [TrieMap<V>; DEGREE],
}
impl<V> Node<V> {
    pub fn new() -> Self {
        Self {
            value: None,
            child: <[TrieMap<V>; DEGREE]>::default(),
        }
    }
}
impl<V> Default for Node<V> {
    fn default() -> Self {
        Self::new()
    }
}
