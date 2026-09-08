use super::DEGREE;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::{self};

/// トライ木で実装したキー→値の辞書。
#[derive(Clone, PartialEq)]
pub struct TrieMap<V>(Option<Box<Node<V>>>);

impl<V: Debug> Debug for TrieMap<V> {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        let mut f = w.debug_map();
        self.for_each_kv(|k, v| {
            f.key(&k).value(v);
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
    /// 空の辞書を構築する。何もアロケートしない。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieMap;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    /// assert_eq!(map.get(once(1)), Some(&"a"));
    /// ```
    pub fn new() -> Self {
        Self(None)
    }

    /// キーと値の組を挿入する。キーが存在しなければ `None` を、既に存在すれば値を
    /// 上書きして古い値を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieMap;
    ///
    /// let mut map = TrieMap::new();
    /// assert_eq!(map.insert(once(17), "a"), None);
    /// assert_eq!(map.insert(once(17), "b"), Some("a"));
    /// ```
    pub fn insert(&mut self, key: impl IntoIterator<Item = usize>, value: V) -> Option<V> {
        let mut key = key.into_iter();
        let me = self.0.get_or_insert_with(|| Box::new(Node::new()));
        match key.next() {
            Some(next) => me.child[next].insert(key, value),
            None => me.value.replace(value),
        }
    }

    /// キーを削除し、そのキーに対応する値があれば返す。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieMap;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    /// assert_eq!(map.remove(once(1)), Some("a"));
    /// assert_eq!(map.remove(once(1)), None);
    /// ```
    pub fn remove(&mut self, key: impl IntoIterator<Item = usize>) -> Option<V> {
        let mut key = key.into_iter();
        let me = self.0.as_deref_mut()?;
        let removed = match key.next() {
            Some(next) => me.child[next].remove(key),
            None => me.value.take(),
        };
        if removed.is_some() {
            let me = self.0.as_deref().unwrap();
            if me.value.is_none() && me.child.iter().all(|child| child.0.is_none()) {
                self.0 = None;
            }
        }
        removed
    }

    /// キーに対応する値への参照を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieMap;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    /// assert_eq!(map.get(once(1)), Some(&"a"));
    /// assert_eq!(map.get(once(2)), None);
    /// ```
    pub fn get(&self, key: impl IntoIterator<Item = usize>) -> Option<&V> {
        let mut key = key.into_iter();
        let me = self.0.as_deref()?;
        match key.next() {
            Some(next) => me.child[next].get(key),
            None => me.value.as_ref(),
        }
    }

    /// キーに対応する値への可変参照を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieMap;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    /// if let Some(x) = map.get_mut(once(1)) {
    ///     *x = "b";
    /// }
    /// assert_eq!(map.get(once(1)), Some(&"b"));
    /// ```
    pub fn get_mut(&mut self, key: impl IntoIterator<Item = usize>) -> Option<&mut V> {
        let mut key = key.into_iter();
        let me = self.0.as_deref_mut()?;
        match key.next() {
            Some(next) => me.child[next].get_mut(key),
            None => me.value.as_mut(),
        }
    }

    /// キーに値が存在しなければ `value` を挿入し、その値への可変参照を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    ///
    /// map.get_or_insert(once(1), "b"); // 既存キーなので "a" のまま
    /// assert_eq!(map.get(once(1)), Some(&"a"));
    ///
    /// map.get_or_insert(once(2), "c"); // 新規キーなので "c" を挿入
    /// assert_eq!(map.get(once(2)), Some(&"c"));
    /// ```
    pub fn get_or_insert(&mut self, key: impl IntoIterator<Item = usize>, value: V) -> &mut V {
        let mut key = key.into_iter();
        let me = self.0.get_or_insert_with(|| Box::new(Node::new()));
        match key.next() {
            Some(next) => me.child[next].get_or_insert(key, value),
            None => me.value.get_or_insert(value),
        }
    }

    /// キーに値が存在しなければ `f()` を挿入し、その値への可変参照を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use trie::TrieMap;
    /// use std::iter::once;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(once(1), "a");
    ///
    /// map.get_or_insert_with(once(1), || "b"); // 既存キーなので "a" のまま
    /// assert_eq!(map.get(once(1)), Some(&"a"));
    ///
    /// map.get_or_insert_with(once(2), || "c"); // 新規キーなので "c" を挿入
    /// assert_eq!(map.get(once(2)), Some(&"c"));
    /// ```
    pub fn get_or_insert_with(
        &mut self,
        key: impl IntoIterator<Item = usize>,
        f: impl FnOnce() -> V,
    ) -> &mut V {
        let mut key = key.into_iter();
        let me = self.0.get_or_insert_with(|| Box::new(Node::new()));
        match key.next() {
            Some(next) => me.child[next].get_or_insert_with(key, f),
            None => me.value.get_or_insert_with(f),
        }
    }

    /// `key` の各接頭辞（空列を含む）に対応するノードを、根から葉へ向かって訪問する。
    /// トライ上に存在しない接頭辞まで達すると打ち切る。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieMap;
    ///
    /// let mut map = TrieMap::new();
    /// map.insert(vec![1], "a");
    /// map.insert(vec![1, 1, 1], "c");
    ///
    /// // 接頭辞 [], [1], [1, 1], [1, 1, 1] の順に訪問する
    /// let mut expected = [None, Some("a"), None, Some("c")].iter();
    /// map.for_each_prefix(vec![1, 1, 1].into_iter(), |trie| {
    ///     let expected = expected.next().unwrap().as_ref();
    ///     assert_eq!(trie.get(None.into_iter()), expected);
    /// });
    /// ```
    pub fn for_each_prefix(
        &self,
        key: impl IntoIterator<Item = usize>,
        mut visit: impl FnMut(&Self),
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

    /// キーの辞書式順序で、すべてのキーと値の組を訪問する。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieMap;
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
    ///     (vec![2], "b"),
    /// ]
    /// .into_iter();
    /// map.for_each_kv(|k, &v| {
    ///     let (ek, ev) = expected.next().unwrap();
    ///     assert_eq!(k, ek.as_slice());
    ///     assert_eq!(v, ev);
    /// });
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

/// [`TrieMap`] の 1 ノード。空でないキーを表す値と、次の要素ごとの子を持つ。
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

#[cfg(test)]
mod tests {
    use super::TrieMap;
    use rand::prelude::*;
    use std::collections::BTreeMap;
    use test_case::test_case;

    #[allow(clippy::unused_unit)]
    #[test_case(200, 2; "short")]
    #[test_case(200, 10; "mid")]
    #[test_case(200, 100; "long")]
    fn test_trie_map_rand(iter: usize, len_max: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        let mut trie = TrieMap::new();
        let mut btree_map = BTreeMap::new();
        for _ in 0..iter {
            let n = rng.gen_range(1..=len_max);
            let s = rand::distributions::Uniform::new(0, 26)
                .sample_iter(&mut rng)
                .take(n)
                .collect::<Vec<_>>();

            match rng.gen_range(0..4) {
                // insert
                0 => {
                    let init_value = 0;
                    let trie_exist = trie.insert(s.iter().copied(), init_value);
                    let btree_map_exist = btree_map.insert(s.clone(), init_value);
                    assert_eq!(trie_exist, btree_map_exist);
                }
                // remove
                1 => {
                    let trie_exist = trie.remove(s.iter().copied());
                    let btree_map_exist = btree_map.remove(&s);
                    assert_eq!(trie_exist, btree_map_exist);
                }
                // get
                2 => {
                    let trie_exist = trie.get(s.iter().copied());
                    let btree_map_exist = btree_map.get(&s);
                    assert_eq!(trie_exist, btree_map_exist);
                }
                // get_mut
                3 => {
                    let trie_value = trie.get_mut(s.iter().copied());
                    let btree_map_value = btree_map.get_mut(&s);
                    assert_eq!(trie_value, btree_map_value);
                    if let Some(trie_value) = trie_value {
                        *trie_value += 1;
                    }
                    if let Some(btree_map_value) = btree_map_value {
                        *btree_map_value += 1;
                    }
                }
                _ => unreachable!(),
            }

            println!("trie = {trie:?}");
            println!("btree_map = {btree_map:?}");
            println!();
        }
    }
}
