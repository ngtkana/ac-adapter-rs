use super::TrieMap;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::{self};

/// A set base on a trie.
#[derive(Clone, PartialEq)]
pub struct TrieSet {
    map: TrieMap<()>,
}

impl Debug for TrieSet {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        let mut f = w.debug_set();
        self.for_each(|k| {
            f.entry(&k.to_vec());
        });
        f.finish()
    }
}

impl Default for TrieSet {
    fn default() -> Self {
        Self::new()
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
    /// use std::iter::once;
    /// use trie::TrieSet;
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

    /// Returns `true` if the set contains a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(once(1));
    /// set.insert(once(2));
    /// set.insert(once(3));
    ///
    /// // let set: TrieSet<_> = [1, 2, 3].iter().cloned().collect(); TODO: unimplemented
    /// assert_eq!(set.contains(once(1)), true);
    /// assert_eq!(set.contains(once(4)), false);
    /// ```
    pub fn contains(&self, value: impl IntoIterator<Item = usize>) -> bool {
        self.map.get(value).is_some()
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

    /// Removes a value from the set. Returns whether the value was
    /// present in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    ///
    /// set.insert(once(2));
    /// assert_eq!(set.remove(once(2)), true);
    /// assert_eq!(set.remove(once(2)), false);
    /// ```
    pub fn remove(&mut self, value: impl IntoIterator<Item = usize>) -> bool {
        self.map.remove(value).is_some()
    }

    /// Visits all the "existing" nodes corresponding to the preficies of the value.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(vec![1]);
    /// set.insert(vec![1, 1, 1]);
    ///
    /// // Corresponding an existing value.
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
        value: impl IntoIterator<Item = usize>,
        visit: impl FnMut(&TrieMap<()>), // TODO: なんとかしたいですね。
    ) {
        self.map.for_each_prefix(value, visit);
    }

    /// Visits all the values of a values in the trie, in lexicographic order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(vec![1, 2, 2]);
    /// set.insert(vec![2]);
    /// set.insert(vec![1]);
    /// set.insert(vec![1, 1, 1]);
    ///
    /// let mut expected = vec![vec![1], vec![1, 1, 1], vec![1, 2, 2], vec![2]].into_iter();
    /// set.for_each(|k| {
    ///     let ek = expected.next().unwrap();
    ///     assert_eq!(k, ek.as_slice());
    /// });
    /// ```
    pub fn for_each(&self, mut visit: impl FnMut(&[usize])) {
        self.map.for_each_kv(|k, ()| visit(k));
    }
}

#[cfg(test)]
mod tests {
    use super::TrieSet;
    use rand::prelude::*;
    use std::collections::BTreeSet;
    use test_case::test_case;

    #[allow(clippy::unused_unit)]
    #[test_case(200, 2; "short")]
    #[test_case(200, 10; "mid")]
    #[test_case(200, 100; "long")]
    fn test_trie_set_rand(iter: usize, len_max: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        let mut trie = TrieSet::new();
        let mut btree_set = BTreeSet::new();
        for _ in 0..iter {
            let n = rng.gen_range(1..=len_max);
            let s = rand::distributions::Uniform::new(0, 26)
                .sample_iter(&mut rng)
                .take(n)
                .collect::<Vec<_>>();

            match rng.gen_range(0..3) {
                // insert
                0 => {
                    let trie_exist = trie.insert(s.iter().copied());
                    let btree_set_exist = btree_set.insert(s.clone());
                    assert_eq!(trie_exist, btree_set_exist);
                }
                // remove
                1 => {
                    let trie_exist = trie.remove(s.iter().copied());
                    let btree_set_exist = btree_set.remove(&s);
                    assert_eq!(trie_exist, btree_set_exist);
                }
                // contians
                2 => {
                    let trie_exist = trie.contains(s.iter().copied());
                    let btree_set_exist = btree_set.contains(&s);
                    assert_eq!(trie_exist, btree_set_exist);
                }
                _ => unreachable!(),
            }

            println!("trie = {:?}", trie);
            println!("btree_set = {:?}", btree_set);
            println!();
        }
    }
}
