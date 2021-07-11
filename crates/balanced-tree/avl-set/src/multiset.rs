use {
    std::cmp::Ordering,
    {super::avltree::Avltree, std::fmt::Debug},
};

/// 多重集合を管理する AVL 木です。
///
/// # Examples
///
/// ```
/// # use avl_set::AvlMultiset;
/// let mut a = AvlMultiset::new();
///
/// // 挿入します。
/// // 成功すると、インデックスが返ります。
/// assert_eq!(a.insert(5), 0);
/// assert_eq!(a.insert(15), 1);
/// assert_eq!(a.insert(10), 1);
/// assert_eq!(a.insert(15), 2);
///
/// // `Vec` に変換できます。
/// assert_eq!(a.collect_vec(), vec![5, 10, 15, 15]);
///
/// // 二分探索ができます。
/// assert_eq!(a.contains(&5), true);
/// assert_eq!(a.lower_bound(&7), 1);
///
/// // 削除します。
/// // 成功すると、インデックスと要素が返ります。
/// assert_eq!(a.delete(&5), Some((0, 5)));
///
/// // インデックスで削除することもできます。
/// // 成功すると、要素が返ります。
/// assert_eq!(a.delete_nth(0), 10);
/// ```
#[derive(Clone, Default)]
pub struct AvlMultiset<K>(Avltree<K, ()>);
impl<K: Ord> AvlMultiset<K> {
    /// 空の [`AvlMultiset`] を構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlMultiset;
    /// let a = AvlMultiset::<()>::new();
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(());
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// assert_eq!(a.is_empty(), true);
    /// a.insert(());
    /// assert_eq!(a.is_empty(), false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
    /// 何がなんでも挿入します。
    ///
    /// # Returns
    ///
    /// 挿入されたインデックスを返します。
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// assert_eq!(a.insert(2), 0);
    /// assert_eq!(a.insert(8), 1);
    /// assert_eq!(a.insert(5), 1);
    /// assert_eq!(a.insert(8), 2);
    /// assert_eq!(a.collect_vec(), vec![2, 5, 8, 8]);
    /// ```
    pub fn insert(&mut self, k: K) -> usize {
        self.0
            .insert_by(k, (), |x, y| match x.cmp(y) {
                Ordering::Less | Ordering::Equal => Ordering::Less,
                Ordering::Greater => Ordering::Greater,
            })
            .unwrap()
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x);
    /// }
    /// assert_eq!(a.delete(&2), Some((0, 2)));
    /// assert_eq!(a.delete(&8), Some((1, 8)));
    /// assert_eq!(a.delete(&5), Some((0, 5)));
    /// assert_eq!(a.delete(&8), None);
    /// assert_eq!(a.collect_vec(), Vec::new());
    /// ```
    pub fn delete(&mut self, k: &K) -> Option<(usize, K)> {
        self.0
            .delete_by(0, |_, l| k.cmp(l))
            .map(|(i, k, ())| (i, k))
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x);
    /// }
    /// assert_eq!(a.delete_nth(0), 2);
    /// assert_eq!(a.delete_nth(1), 8);
    /// assert_eq!(a.delete_nth(0), 5);
    /// assert_eq!(a.collect_vec(), Vec::new());
    /// ```
    pub fn delete_nth(&mut self, n: usize) -> K {
        assert!(n < self.len());
        self.0
            .delete_by(0, |i, _| n.cmp(&i))
            .map(|(_, k, ())| k)
            .unwrap()
    }
    /// `x` に等しい要素があれば、`true` を返します。
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x);
    /// }
    /// assert_eq!(a.contains(&2), true);
    /// assert_eq!(a.contains(&3), false);
    /// assert_eq!(a.contains(&4), false);
    /// assert_eq!(a.contains(&5), true);
    /// ```
    pub fn contains(&self, k: &K) -> bool {
        self.0.get_by(|l| k.cmp(l)).is_some()
    }
    /// そこより左は `x` 未満、そこより右は `x`
    /// 以上になるようなインデックス境界がただ一つ存在するのでそれを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x);
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x);
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// for x in vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9] {
    ///     a.insert(x);
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// for x in vec![2, 8, 5] {
    ///     a.insert(x);
    /// }
    /// assert_eq!(a.collect_vec(), vec![2, 5, 8]);
    /// ```
    pub fn collect_vec(&self) -> Vec<K>
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
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// let mut s = String::new();
    /// for x in vec![2, 8, 5] {
    ///     a.insert(x);
    /// }
    /// a.for_each(|&x| s.push_str(&format!("{}", x)));
    /// assert_eq!(s.as_str(), "258");
    /// ```
    pub fn for_each<F: FnMut(&K)>(&self, mut f: F) {
        self.0.for_each(&mut |k, ()| f(k))
    }
    /// 要素を昇順に訪問します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlMultiset;
    /// let mut a = AvlMultiset::new();
    /// let mut s = String::new();
    /// for x in vec![2, 8, 5] {
    ///     a.insert(x);
    /// }
    /// a.rfor_each(|&x| s.push_str(&format!("{}", x)));
    /// assert_eq!(s.as_str(), "852");
    /// ```
    pub fn rfor_each<F: FnMut(&K)>(&self, mut f: F) {
        self.0.rfor_each(&mut |k, ()| f(k))
    }
}
impl<T: Debug> Debug for AvlMultiset<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_set = f.debug_set();
        self.0.fmt_keys_impl(&mut debug_set);
        debug_set.finish()
    }
}

#[cfg(test)]
mod tests {
    use {
        super::AvlMultiset,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::fmt::Debug,
        superslice::Ext,
    };

    #[test]
    fn test_rand() {
        #[derive(Clone, Debug, Default, Hash, PartialEq)]
        struct Brute(Vec<i32>);
        impl Brute {
            fn new() -> Self {
                Self(Vec::new())
            }
            fn len(&self) -> usize {
                self.0.len()
            }
            fn insert(&mut self, x: i32) -> usize {
                let i = self.0.lower_bound(&x);
                self.0.insert(i, x);
                i
            }
            fn delete_validate(&mut self, &x: &i32, result: Option<(usize, i32)>) {
                match result {
                    None => {
                        assert!(self.0.binary_search(&x).is_err());
                    }
                    Some((i, y)) => {
                        assert_eq!(x, y);
                        assert_eq!(x, self.0[i]);
                        self.0.remove(i);
                    }
                }
            }
            fn delete_nth(&mut self, n: usize) -> i32 {
                self.0[n..].rotate_left(1);
                self.0.pop().unwrap()
            }
            fn lower_bound(&self, x: &i32) -> usize {
                self.0.lower_bound(x)
            }
            fn upper_bound(&self, x: &i32) -> usize {
                self.0.upper_bound(x)
            }
            fn collect_vec(&self) -> Vec<i32> {
                self.0.clone()
            }
        }

        let mut len_lim = vec![1, 2];
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            const A: i32 = 40;
            const Q: usize = 200;
            let mut fast = AvlMultiset::new();
            let mut brute = Brute::new();
            for _ in 0..Q {
                match rng.gen_range(0..7) {
                    // len
                    0 => {
                        let result = fast.len();
                        let expected = brute.len();
                        assert_eq!(result, expected);
                    }
                    // insert
                    1 => {
                        let x = rng.gen_range(0..A);
                        let result = fast.insert(x);
                        let expected = brute.insert(x);
                        assert_eq!(result, expected);
                    }
                    // delete
                    2 => {
                        let x = rng.gen_range(0..A);
                        let result = fast.delete(&x);
                        brute.delete_validate(&x, result);
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
                    // lower_bound
                    4 => {
                        let x = rng.gen_range(0..=A);
                        let result = fast.lower_bound(&x);
                        let expected = brute.lower_bound(&x);
                        assert_eq!(result, expected);
                    }
                    // upper_bound
                    5 => {
                        let x = rng.gen_range(0..=A);
                        let result = fast.upper_bound(&x);
                        let expected = brute.upper_bound(&x);
                        assert_eq!(result, expected);
                    }
                    // collect_vec
                    6 => {
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
}
