use {super::avltree::Avltree, std::fmt::Debug};

/// マップを管理する AVL 木です。
///
/// # Examples
///
/// ```
/// # use avl_tree::AvlMap;
/// let mut a = AvlMap::new();
///
/// // 挿入します。
/// // 成功すると、インデックスが返ります。
/// // すでにある値は上書きされません。
/// assert_eq!(a.insert(5, 105), Some(0));
/// assert_eq!(a.insert(15, 115), Some(1));
/// assert_eq!(a.insert(10, 110), Some(1));
/// assert_eq!(a.insert(15, 215), None);
///
/// // `Vec` に変換できます。
/// assert_eq!(a.collect_vec(), vec![(5, 105), (10, 110), (15, 115)]);
///
/// // 二分探索ができます。
/// // 要素への参照や可変参照もとれます。
/// assert_eq!(a.nth(2), Some((&15, &115)));
/// assert_eq!(a.contains_key(&5), true);
/// assert_eq!(a.lower_bound(&7), 1);
/// assert_eq!(a.position_get(&15), Some((2, &115)));
/// *a.get_mut(&15).unwrap() += 100;
/// assert_eq!(a.collect_vec(), vec![(5, 105), (10, 110), (15, 215)]);
///
/// // 削除します。
/// // 成功すると、インデックスと要素が返ります。
/// assert_eq!(a.delete(&5), Some((0, 5, 105)));
///
/// // インデックスで削除することもできます。
/// // 成功すると、要素が返ります。
/// assert_eq!(a.delete_nth(0), (10, 110));
/// ```
#[derive(Clone, Default)]
pub struct AvlMap<K, V>(Avltree<K, V>);
impl<K: Ord, V> AvlMap<K, V> {
    /// 空の [`AvlMap`] を構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let a = AvlMap::<(), ()>::new();
    /// assert_eq!(a.collect_vec(), Vec::new());
    /// ```
    pub fn new() -> Self {
        Self(Avltree::new())
    }
    /// 管理する要素の個数を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert((), ());
    /// assert_eq!(a.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.0.len()
    }
    /// 空ならば `true` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// assert_eq!(a.is_empty(), true);
    /// a.insert((), ());
    /// assert_eq!(a.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// `x` に等しい要素がない場合新しく挿入します。さもなくば挿入されません。
    ///
    /// # Returns
    ///
    /// 挿入された場合はそのインデックスを返します。さもなくば `None` を返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// assert_eq!(a.insert(2, ()), Some(0));
    /// assert_eq!(a.insert(8, ()), Some(1));
    /// assert_eq!(a.insert(5, ()), Some(1));
    /// assert_eq!(a.insert(8, ()), None);
    /// assert_eq!(a.collect_keys_vec(), vec![2, 5, 8]);
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<usize> {
        self.0.insert_by(k, v, Ord::cmp)
    }
    /// `x` に等しい要素がある場合は削除されます。さもなくば削除されません
    ///
    /// # Returns
    ///
    /// 削除された場合はそのインデックスを返します。さもなくば `None` を返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.delete(&2), Some((0, 2, ())));
    /// assert_eq!(a.delete(&8), Some((1, 8, ())));
    /// assert_eq!(a.delete(&5), Some((0, 5, ())));
    /// assert_eq!(a.delete(&8), None);
    /// assert_eq!(a.collect_keys_vec(), Vec::new());
    /// ```
    pub fn delete(&mut self, k: &K) -> Option<(usize, K, V)> {
        self.0.delete_by(0, |_, l| k.cmp(l))
    }
    /// `n` 番目の要素を削除します。
    ///
    /// # Panics
    ///
    /// 範囲外
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.delete_nth(0), (2, ()));
    /// assert_eq!(a.delete_nth(1), (8, ()));
    /// assert_eq!(a.delete_nth(0), (5, ()));
    /// assert_eq!(a.collect_vec(), Vec::new());
    /// ```
    pub fn delete_nth(&mut self, n: usize) -> (K, V) {
        assert!(n < self.len());
        self.0
            .delete_by(0, |i, _| n.cmp(&i))
            .map(|(_, k, v)| (k, v))
            .unwrap()
    }
    /// 先頭の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.front(), Some((&2, &())));
    /// ```
    pub fn front(&self) -> Option<(&K, &V)> {
        self.0.get_extremum(0)
    }
    /// 末尾の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.back(), Some((&8, &())));
    /// ```
    pub fn back(&self) -> Option<(&K, &V)> {
        self.0.get_extremum(1)
    }
    /// 先頭の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, 0);
    /// }
    /// *a.front_mut().unwrap().1 += 10;
    /// assert_eq!(a.collect_vec(), vec![(2, 10), (5, 0), (8, 0)]);
    /// ```
    pub fn front_mut(&mut self) -> Option<(&K, &mut V)> {
        self.0.get_mut_extremum(0).map(|(k, v)| (k, v))
    }
    /// 末尾の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, 0);
    /// }
    /// *a.back_mut().unwrap().1 += 10;
    /// assert_eq!(a.collect_vec(), vec![(2, 0), (5, 0), (8, 10)]);
    /// ```
    pub fn back_mut(&mut self) -> Option<(&K, &mut V)> {
        self.0.get_mut_extremum(1).map(|(k, v)| (k, v))
    }
    /// `n` 番目の要素を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.nth(0), Some((&2, &())));
    /// assert_eq!(a.nth(1), Some((&5, &())));
    /// assert_eq!(a.nth(2), Some((&8, &())));
    /// assert_eq!(a.nth(3), None);
    /// ```
    pub fn nth(&self, n: usize) -> Option<(&K, &V)> {
        self.0.get_by(0, |i, _| n.cmp(&i)).map(|(_, k, v)| (k, v))
    }
    /// `x` に等しい要素があれば、`true` を返します。
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.contains_key(&2), true);
    /// assert_eq!(a.contains_key(&3), false);
    /// assert_eq!(a.contains_key(&4), false);
    /// assert_eq!(a.contains_key(&5), true);
    /// ```
    pub fn contains_key(&self, k: &K) -> bool {
        self.get(k).is_some()
    }
    /// `x` に等しい要素があれば、そのインデックスを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.position(&2), Some(0));
    /// assert_eq!(a.position(&3), None);
    /// assert_eq!(a.position(&4), None);
    /// assert_eq!(a.position(&5), Some(1));
    /// ```
    pub fn position(&self, k: &K) -> Option<usize> {
        self.0.get_by(0, |_, l| k.cmp(l)).map(|(i, _, _)| i)
    }
    /// `x` に等しい要素があれば、その値への参照を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for (k, v) in vec![(2, 12), (5, 15), (8, 18)] {
    ///     a.insert(k, v);
    /// }
    /// assert_eq!(a.get(&2), Some(&12));
    /// assert_eq!(a.get(&3), None);
    /// assert_eq!(a.get(&4), None);
    /// assert_eq!(a.get(&5), Some(&15));
    /// ```
    pub fn get(&self, k: &K) -> Option<&V> {
        self.position_get(k).map(|(_, v)| v)
    }
    /// `x` に等しい要素があれば、その値への可変参照を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for (k, v) in vec![(2, 12), (5, 15), (8, 18)] {
    ///     a.insert(k, v);
    /// }
    /// *a.get_mut(&2).unwrap() = 22;
    /// assert_eq!(a.collect_vec(), vec![(2, 22), (5, 15), (8, 18)]);
    /// ```
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        self.position_get_mut(k).map(|(_, v)| v)
    }
    /// `x` に等しい要素があれば、そのインデックスと値への参照を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for (k, v) in vec![(2, 12), (5, 15), (8, 18)] {
    ///     a.insert(k, v);
    /// }
    /// assert_eq!(a.position_get(&2), Some((0, &12)));
    /// assert_eq!(a.position_get(&3), None);
    /// assert_eq!(a.position_get(&4), None);
    /// assert_eq!(a.position_get(&5), Some((1, &15)));
    /// ```
    pub fn position_get(&self, k: &K) -> Option<(usize, &V)> {
        self.0.get_by(0, |_, l| k.cmp(l)).map(|(i, _, v)| (i, v))
    }
    /// `x` に等しい要素があれば、そのインデックスと値への可変参照を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for (k, v) in vec![(2, 12), (5, 15), (8, 18)] {
    ///     a.insert(k, v);
    /// }
    /// *a.position_get_mut(&2).unwrap().1 = 22;
    /// assert_eq!(a.collect_vec(), vec![(2, 22), (5, 15), (8, 18)]);
    /// ```
    pub fn position_get_mut(&mut self, k: &K) -> Option<(usize, &mut V)> {
        self.0
            .get_mut_by(0, |_, l| k.cmp(l))
            .map(|(i, _, v)| (i, v))
    }
    /// そこより左は `x` 未満、そこより右は `x`
    /// 以上になるようなインデックス境界がただ一つ存在するのでそれを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.lower_bound(&4), 1);
    /// assert_eq!(a.lower_bound(&5), 1);
    /// assert_eq!(a.lower_bound(&6), 2);
    /// ```
    pub fn lower_bound(&self, k: &K) -> usize {
        self.0.partition_point(|l| l < k)
    }
    /// そこより左はすべて `x` 以下、そこより右はすべて `x`
    /// より大きくなるようなインデックス境界がただ一つ存在するのでそれを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.upper_bound(&4), 1);
    /// assert_eq!(a.upper_bound(&5), 2);
    /// assert_eq!(a.upper_bound(&6), 2);
    /// ```
    pub fn upper_bound(&self, k: &K) -> usize {
        self.0.partition_point(|l| l <= k)
    }
    /// すぐ左は `false`、すぐ右は `true` になるようなインデックス境界が
    /// 一つ以上存在するので、そのうちひとつを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9] {
    ///     a.insert(x, ());
    /// }
    /// for r in 0..5 {
    ///     let result = a.partition_point(|&x| x % 5 != r);
    ///     assert!(result % 5 == r || result == 10);
    /// }
    /// ```
    pub fn partition_point<F: Fn(&K) -> bool>(&self, f: F) -> usize {
        self.0.partition_point(f)
    }
    /// 要素を昇順にすべて clone して、[`Vec`] に変換します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 8, 5] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.collect_vec(), vec![(2, ()), (5, ()), (8, ())]);
    /// ```
    pub fn collect_vec(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        self.0.collect_vec()
    }
    /// 要素を昇順にすべて clone して、[`Vec`] に変換します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// for x in vec![2, 8, 5] {
    ///     a.insert(x, ());
    /// }
    /// assert_eq!(a.collect_keys_vec(), vec![2, 5, 8]);
    /// ```
    pub fn collect_keys_vec(&self) -> Vec<K>
    where
        K: Clone,
    {
        self.0.collect_keys_vec()
    }
    /// 要素を昇順に訪問します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// let mut s = String::new();
    /// for x in vec![2, 8, 5] {
    ///     a.insert(x, ());
    /// }
    /// a.for_each(|&k, _| s.push_str(&format!("{}", k)));
    /// assert_eq!(s.as_str(), "258");
    /// ```
    pub fn for_each<F: FnMut(&K, &V)>(&self, mut f: F) {
        self.0.for_each(&mut f)
    }
    /// 要素を昇順に訪問します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_tree::AvlMap;
    /// let mut a = AvlMap::new();
    /// let mut s = String::new();
    /// for x in vec![2, 8, 5] {
    ///     a.insert(x, ());
    /// }
    /// a.rfor_each(|&k, _| s.push_str(&format!("{}", k)));
    /// assert_eq!(s.as_str(), "852");
    /// ```
    pub fn rfor_each<F: FnMut(&K, &V)>(&self, mut f: F) {
        self.0.rfor_each(&mut f)
    }
}
impl<K: Debug, V: Debug> Debug for AvlMap<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use {
        super::AvlMap,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::fmt::Debug,
        superslice::Ext,
    };

    #[test]
    fn test_rand() {
        #[derive(Clone, Debug, Default, Hash, PartialEq)]
        struct Brute(Vec<(i32, u8)>);
        impl Brute {
            fn new() -> Self {
                Self(Vec::new())
            }
            fn len(&self) -> usize {
                self.0.len()
            }
            fn insert(&mut self, k: i32, v: u8) -> Option<usize> {
                if self.0.binary_search_by_key(&k, |&(k, _)| k).is_err() {
                    let i = self.0.lower_bound_by_key(&k, |&(k, _)| k);
                    self.0.insert(i, (k, v));
                    Some(i)
                } else {
                    None
                }
            }
            fn delete(&mut self, &k: &i32) -> Option<(usize, i32, u8)> {
                if self.0.binary_search_by_key(&k, |&(k, _)| k).is_ok() {
                    let i = self.0.lower_bound_by_key(&k, |&(k, _)| k);
                    let (k, v) = self.0.remove(i);
                    Some((i, k, v))
                } else {
                    None
                }
            }
            fn delete_nth(&mut self, n: usize) -> (i32, u8) {
                self.0[n..].rotate_left(1);
                self.0.pop().unwrap()
            }
            fn nth(&mut self, n: usize) -> Option<(&i32, &u8)> {
                self.0.get(n).map(|(k, v)| (k, v))
            }
            fn position_get(&self, &k: &i32) -> Option<(usize, &u8)> {
                self.0
                    .binary_search_by_key(&k, |&(k, _)| k)
                    .ok()
                    .map(|i| (i, &self.0[i].1))
            }
            fn position_get_mut(&mut self, &k: &i32) -> Option<(usize, &mut u8)> {
                match self.0.binary_search_by_key(&k, |&(k, _)| k) {
                    Err(_) => None,
                    Ok(i) => Some((i, &mut self.0[i].1)),
                }
            }
            fn lower_bound(&self, k: &i32) -> usize {
                self.0.lower_bound_by_key(k, |&(k, _)| k)
            }
            fn upper_bound(&self, k: &i32) -> usize {
                self.0.upper_bound_by_key(k, |&(k, _)| k)
            }
            fn collect_vec(&self) -> Vec<(i32, u8)> {
                self.0.clone()
            }
        }

        let mut len_lim = vec![1, 2];
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            const A: i32 = 20;
            const B: u8 = 3;
            const Q: usize = 200;
            let mut fast = AvlMap::new();
            let mut brute = Brute::new();
            for _ in 0..Q {
                match rng.gen_range(0..10) {
                    // len
                    0 => {
                        let result = fast.len();
                        let expected = brute.len();
                        assert_eq!(result, expected);
                    }
                    // insert
                    1 => {
                        let k = rng.gen_range(0..A);
                        let v = rng.gen_range(0..B);
                        let result = fast.insert(k, v);
                        let expected = brute.insert(k, v);
                        assert_eq!(result, expected);
                    }
                    // delete
                    2 => {
                        let x = rng.gen_range(0..A);
                        let result = fast.delete(&x);
                        let expected = brute.delete(&x);
                        assert_eq!(result, expected);
                    }
                    // delete_nth
                    3 => {
                        if !fast.is_empty() {
                            let n = rng.gen_range(0..fast.len());
                            let result = fast.delete_nth(n);
                            let expected = brute.delete_nth(n);
                            assert_eq!(result, expected);
                        }
                    }
                    // nth
                    4 => {
                        if !fast.is_empty() {
                            let n = rng.gen_range(0..fast.len());
                            let result = fast.nth(n);
                            let expected = brute.nth(n);
                            assert_eq!(result, expected);
                        }
                    }
                    // position_get
                    5 => {
                        let x = rng.gen_range(0..A);
                        let result = fast.position_get(&x);
                        let expected = brute.position_get(&x);
                        assert_eq!(result, expected);
                    }
                    // position_get_mut
                    6 => {
                        let k = rng.gen_range(0..A);
                        let v = rng.gen_range(0..B);
                        match [fast.position_get_mut(&k), brute.position_get_mut(&k)] {
                            [None, None] => continue,
                            [Some((result, fast_ref)), Some((expected, brute_ref))] => {
                                *fast_ref = v;
                                *brute_ref = v;
                                assert_eq!(result, expected);
                            }
                            _ => panic!(),
                        };
                    }
                    // lower_bound
                    7 => {
                        let x = rng.gen_range(0..=A);
                        let result = fast.lower_bound(&x);
                        let expected = brute.lower_bound(&x);
                        assert_eq!(result, expected);
                    }
                    // upper_bound
                    8 => {
                        let x = rng.gen_range(0..=A);
                        let result = fast.upper_bound(&x);
                        let expected = brute.upper_bound(&x);
                        assert_eq!(result, expected);
                    }
                    // collect_vec
                    9 => {
                        let result = fast.collect_vec();
                        let expected = brute.collect_vec();
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
                println!("{:?}", &fast);
                let ht = fast.0.ht();
                while len_lim.len() <= ht {
                    let value = len_lim[len_lim.len() - 2] + len_lim[len_lim.len() - 1] - 1;
                    len_lim.push(value);
                }
                assert!(ht <= len_lim[ht]);
            }
        }
    }

    #[test]
    fn test_avltree_fmt() {
        let mut map = AvlMap::<u32, u32>::new();
        for (k, v) in vec![(0, 10), (1, 11), (2, 12)] {
            map.insert(k, v);
        }
        assert_eq!("{0: 10, 1: 11, 2: 12}", format!("{:?}", &map).as_str());
    }
}
