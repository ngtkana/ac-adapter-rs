use {
    super::TrieMap,
    std::fmt::{self, Debug, Formatter},
};

/// A set base on a trie.
#[derive(Clone, PartialEq)]
pub struct TrieSet {
    map: TrieMap<()>,
}

impl Debug for TrieSet {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        let mut f = w.debug_set();
        self.for_each_keys(|k| {
            f.entry(&k.to_vec());
        });
        f.finish()
    }
}

impl TrieSet {
    /// Makes a new empty TrieMap.
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieSet;
    /// use std::iter::once;
    ///
    /// let mut set = TrieSet::new();
    ///
    /// // entries can now be inserted into the empty set
    /// set.insert(once(1));
    /// ```
    pub fn new() -> Self {
        Self {
            map: TrieMap::new(),
        }
    }
    /// Adds a value to the set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned, and the
    /// entry is not updated.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    ///
    /// assert_eq!(set.insert(once(2)), true);
    /// assert_eq!(set.insert(once(2)), false);
    /// // assert_eq!(set.len(), 1); not implemented
    /// ```
    pub fn insert(&mut self, iter: impl IntoIterator<Item = usize>) -> bool {
        self.map.insert(iter, ()).is_none()
    }

    /// Visits all the "existing" nodes corresponding to the preficies of the key.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieSet;
    /// use std::iter::once;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(vec![1]);
    /// set.insert(vec![1, 1, 1]);
    ///
    /// // Corresponding an existing key.
    /// let mut expected = [false, true, false, true].iter();
    /// set.for_each_prefix(vec![1, 1, 1].into_iter(), |trie| {
    ///     let expected = *expected.next().unwrap();
    ///     assert_eq!(trie.get(None.into_iter()).is_some(), expected);
    /// });
    ///
    /// // No, but falls within the trie.
    /// let mut expected = [false, true, false].iter();
    /// set.for_each_prefix(vec![1, 1].into_iter(), |trie| {
    ///     let expected = *expected.next().unwrap();
    ///     assert_eq!(trie.get(None.into_iter()).is_some(), expected);
    /// });
    ///
    /// // Runs off thte trie.
    /// let mut expected = [false, true, false, true].iter();
    /// set.for_each_prefix(vec![1, 1, 1, 1].into_iter(), |trie| {
    ///     let expected = *expected.next().unwrap();
    ///     assert_eq!(trie.get(None.into_iter()).is_some(), expected);
    /// });
    /// ```
    pub fn for_each_prefix(
        &self,
        key: impl IntoIterator<Item = usize>,
        visit: impl FnMut(&TrieMap<()>), // TODO: なんとかしたいですね。
    ) {
        self.map.for_each_prefix(key, visit);
    }

    /// Visits all the keys of a values in the trie, in lexicographic order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use trie::TrieSet;
    /// use std::iter::once;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(vec![1, 2, 2]);
    /// set.insert(vec![2]);
    /// set.insert(vec![1]);
    /// set.insert(vec![1, 1, 1]);
    ///
    /// let mut expected = vec![
    ///     vec![1],
    ///     vec![1, 1, 1],
    ///     vec![1, 2, 2],
    ///     vec![2],
    /// ].into_iter();
    /// set.for_each_keys(|k| {
    ///     let ek = expected.next().unwrap();
    ///     assert_eq!(k, ek);
    /// });
    /// ```
    pub fn for_each_keys(&self, mut visit: impl FnMut(&[usize])) {
        self.map.for_each_kv(|k, ()| visit(k));
    }
}

#[cfg(test)]
mod tests {
    use {super::TrieSet, rand::prelude::*, std::collections::BTreeSet, test_case::test_case};

    #[test_case(200, 2; "short")]
    #[test_case(200, 10; "mid")]
    #[test_case(200, 100; "long")]
    fn test_trie_set_rand_insert(iter: usize, len_max: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        let mut trie = TrieSet::new();
        let mut btree_set = BTreeSet::new();
        for _ in 0..iter {
            let n = rng.gen_range(1..=len_max);
            let s = rand::distributions::Uniform::new(0, 26)
                .sample_iter(&mut rng)
                .take(n)
                .collect::<Vec<_>>();

            let trie_exist = trie.insert(s.iter().copied());
            let btree_set_exist = btree_set.insert(s.clone());
            assert_eq!(trie_exist, btree_set_exist);

            println!("trie = {:?}", trie);
            println!("btree_set = {:?}", btree_set);
            println!();
        }
    }
}
