use super::TrieMap;
use std::fmt::Debug;
use std::fmt::Formatter;
use std::fmt::{self};

/// トライ木で実装したキー列の集合。内部的に `TrieMap<()>` をラップして実装する。
#[derive(Clone, PartialEq)]
pub struct TrieSet {
    map: TrieMap<()>,
}

impl Debug for TrieSet {
    fn fmt(&self, w: &mut Formatter<'_>) -> fmt::Result {
        let mut f = w.debug_set();
        self.for_each(|k| {
            f.entry(&k);
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
    /// 空の集合を構築する。何もアロケートしない。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(once(1));
    /// assert!(set.contains(once(1)));
    /// ```
    pub fn new() -> Self {
        Self {
            map: TrieMap::new(),
        }
    }

    /// 値が集合に含まれるかを返す。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(once(1));
    /// assert_eq!(set.contains(once(1)), true);
    /// assert_eq!(set.contains(once(4)), false);
    /// ```
    pub fn contains(&self, value: impl IntoIterator<Item = usize>) -> bool {
        self.map.get(value).is_some()
    }

    /// 値を集合に追加する。既に存在しなければ `true`、既に存在すれば `false` を返す
    /// （このとき集合は変化しない）。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    /// assert_eq!(set.insert(once(2)), true);
    /// assert_eq!(set.insert(once(2)), false);
    /// ```
    pub fn insert(&mut self, iter: impl IntoIterator<Item = usize>) -> bool {
        self.map.insert(iter, ()).is_none()
    }

    /// 値を集合から削除する。削除前に集合に含まれていたかを返す。
    ///
    /// # 例
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

    /// `value` の各接頭辞（空列を含む）に対応するノードを、根から葉へ向かって訪問する。
    /// トライ上に存在しない接頭辞まで達すると打ち切る。
    ///
    /// # 例
    ///
    /// ```
    /// use std::iter::once;
    /// use trie::TrieSet;
    ///
    /// let mut set = TrieSet::new();
    /// set.insert(vec![1]);
    /// set.insert(vec![1, 1, 1]);
    ///
    /// // 接頭辞 [], [1], [1, 1], [1, 1, 1] の順に訪問する
    /// let mut expected = [false, true, false, true].iter();
    /// set.for_each_prefix(vec![1, 1, 1].into_iter(), |trie| {
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

    /// 辞書式順序で、すべての値を訪問する。
    ///
    /// # 例
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

            println!("trie = {trie:?}");
            println!("btree_set = {btree_set:?}");
            println!();
        }
    }
}
