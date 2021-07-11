use {super::avltree::Avltree, std::fmt::Debug};

/// 集合を管理する AVL 木です。
#[derive(Clone, Default)]
pub struct AvlSet<K>(Avltree<K, ()>);
impl<K: Ord> AvlSet<K> {
    /// 空の [`AvlSet`] を構築します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlSet;
    /// let a = AvlSet::<()>::new();
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
    /// assert_eq!(a.is_empty(), true);
    /// a.insert(());
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
    /// assert_eq!(a.insert(2), Some(0));
    /// assert_eq!(a.insert(8), Some(1));
    /// assert_eq!(a.insert(5), Some(1));
    /// assert_eq!(a.insert(8), None);
    /// assert_eq!(a.collect_vec(), vec![2, 5, 8]);
    /// ```
    pub fn insert(&mut self, k: K) -> Option<usize> {
        self.0.insert_by(k, (), Ord::cmp)
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
        self.0.delete_by(|l| k.cmp(l)).map(|(i, k, ())| (i, k))
    }
    /// `x` に等しい要素があれば、`true` を返します。
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
    /// `x` に等しい要素があれば、そのインデックスを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
    /// for x in vec![2, 5, 8] {
    ///     a.insert(x);
    /// }
    /// assert_eq!(a.position(&2), Some(0));
    /// assert_eq!(a.position(&3), None);
    /// assert_eq!(a.position(&4), None);
    /// assert_eq!(a.position(&5), Some(1));
    /// ```
    pub fn position(&self, k: &K) -> Option<usize> {
        self.0.get_by(|l| k.cmp(l)).map(|(i, ())| i)
    }
    /// そこより左は `x` 未満、そこより右は `x`
    /// 以上になるようなインデックス境界がただ一つ存在するのでそれを返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
    /// # use avl_set::AvlSet;
    /// let mut a = AvlSet::new();
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
impl<T: Debug> Debug for AvlSet<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_set = f.debug_set();
        self.0.fmt_keys_impl(&mut debug_set);
        debug_set.finish()
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{super::avltree::utils::describe_set, AvlSet},
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::fmt::Debug,
        superslice::Ext,
    };

    fn describe<T: Debug>(avl: &AvlSet<T>) -> String {
        describe_set(&avl.0)
    }

    #[test]
    fn test_structure_biased_ascending() {
        let mut avl = AvlSet::<u32>::new();
        assert_eq!(describe(&avl).as_str(), "");
        avl.insert(0);
        assert_eq!(describe(&avl).as_str(), "(0)");
        avl.insert(1);
        assert_eq!(describe(&avl).as_str(), "(0(1))");
        avl.insert(2);
        assert_eq!(describe(&avl).as_str(), "((0)1(2))");
        avl.insert(3);
        assert_eq!(describe(&avl).as_str(), "((0)1(2(3)))");
        avl.insert(4);
        assert_eq!(describe(&avl).as_str(), "((0)1((2)3(4)))");
        avl.insert(5);
        assert_eq!(describe(&avl).as_str(), "(((0)1(2))3(4(5)))");
        avl.insert(6);
        assert_eq!(describe(&avl).as_str(), "(((0)1(2))3((4)5(6)))");
        avl.insert(7);
        assert_eq!(describe(&avl).as_str(), "(((0)1(2))3((4)5(6(7))))");
        avl.insert(8);
        assert_eq!(describe(&avl).as_str(), "(((0)1(2))3((4)5((6)7(8))))");
        avl.insert(9);
        assert_eq!(describe(&avl).as_str(), "(((0)1(2))3(((4)5(6))7(8(9))))");
        avl.insert(10);
        assert_eq!(
            describe(&avl).as_str(),
            "(((0)1(2))3(((4)5(6))7((8)9(10))))"
        );
        avl.insert(11);
        assert_eq!(
            describe(&avl).as_str(),
            "((((0)1(2))3((4)5(6)))7((8)9(10(11))))"
        );
    }

    #[test]
    fn test_structure_biased_descending() {
        struct Reverse(u32);
        impl PartialEq for Reverse {
            fn eq(&self, other: &Self) -> bool {
                self.0 == other.0
            }
        }
        impl Eq for Reverse {}
        impl PartialOrd for Reverse {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                Some(self.cmp(&other))
            }
        }
        impl Ord for Reverse {
            fn cmp(&self, other: &Self) -> std::cmp::Ordering {
                self.0.cmp(&other.0).reverse()
            }
        }
        impl Debug for Reverse {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                self.0.fmt(f)
            }
        }
        let mut avl = AvlSet::<Reverse>::new();
        assert_eq!(describe(&avl).as_str(), "");
        avl.insert(Reverse(0));
        assert_eq!(describe(&avl).as_str(), "(0)");
        avl.insert(Reverse(1));
        assert_eq!(describe(&avl).as_str(), "((1)0)");
        avl.insert(Reverse(2));
        assert_eq!(describe(&avl).as_str(), "((2)1(0))");
        avl.insert(Reverse(3));
        assert_eq!(describe(&avl).as_str(), "(((3)2)1(0))");
        avl.insert(Reverse(4));
        assert_eq!(describe(&avl).as_str(), "(((4)3(2))1(0))");
        avl.insert(Reverse(5));
        assert_eq!(describe(&avl).as_str(), "(((5)4)3((2)1(0)))");
        avl.insert(Reverse(6));
        assert_eq!(describe(&avl).as_str(), "(((6)5(4))3((2)1(0)))");
        avl.insert(Reverse(7));
        assert_eq!(describe(&avl).as_str(), "((((7)6)5(4))3((2)1(0)))");
        avl.insert(Reverse(8));
        assert_eq!(describe(&avl).as_str(), "((((8)7(6))5(4))3((2)1(0)))");
        avl.insert(Reverse(9));
        assert_eq!(describe(&avl).as_str(), "((((9)8)7((6)5(4)))3((2)1(0)))");
        avl.insert(Reverse(10));
        assert_eq!(
            describe(&avl).as_str(),
            "((((10)9(8))7((6)5(4)))3((2)1(0)))"
        );
        avl.insert(Reverse(11));
        assert_eq!(
            describe(&avl).as_str(),
            "((((11)10)9(8))7(((6)5(4))3((2)1(0))))"
        );
    }

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
            fn insert(&mut self, x: i32) -> Option<usize> {
                if self.0.binary_search(&x).is_err() {
                    let i = self.0.lower_bound(&x);
                    self.0.insert(i, x);
                    Some(i)
                } else {
                    None
                }
            }
            fn delete(&mut self, x: &i32) -> Option<(usize, i32)> {
                if self.0.binary_search(&x).is_ok() {
                    let i = self.0.lower_bound(&x);
                    self.0.remove(i);
                    Some((i, *x))
                } else {
                    None
                }
            }
            fn position(&mut self, x: &i32) -> Option<usize> {
                self.0.binary_search(&x).ok()
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
            let mut fast = AvlSet::new();
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
                        let expected = brute.delete(&x);
                        assert_eq!(result, expected);
                    }
                    // position
                    3 => {
                        let x = rng.gen_range(0..A);
                        let result = fast.position(&x);
                        let expected = brute.position(&x);
                        assert_eq!(result, expected);
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

    #[test]
    fn test_avltree_fmt() {
        let mut set = AvlSet::<u32>::new();
        assert_eq!("{}", format!("{:?}", &set).as_str());
        set.insert(10);
        assert_eq!("{10}", format!("{:?}", &set).as_str());
        set.insert(15);
        assert_eq!("{10, 15}", format!("{:?}", &set).as_str());
        set.insert(5);
        assert_eq!("{5, 10, 15}", format!("{:?}", &set).as_str());
    }
}
