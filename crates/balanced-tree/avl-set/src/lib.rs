use std::{
    cmp::Ordering,
    fmt::{Debug, DebugSet},
    mem::{replace, swap, take},
};

#[derive(Clone, Hash, PartialEq)]
pub struct Avltree<T>(Option<Box<Node<T>>>);
impl<T> Avltree<T> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.len)
    }
    pub fn is_empty(&self) -> bool {
        self.0.is_none()
    }
    /// `Ordering` で二分探索して、一致するものがなければ挿入してインデックスを変えします。
    pub fn insert_by<F: Fn(&T, &T) -> Ordering>(&mut self, x: T, cmp: F) -> Option<usize> {
        let res = match &mut self.0 {
            None => {
                self.0 = Some(Box::new(Node::new(x)));
                Some(0)
            }
            Some(node) => match cmp(&x, &node.value) {
                Ordering::Less => node.child[0].insert_by(x, cmp),
                Ordering::Equal => None,
                Ordering::Greater => node.child[1]
                    .insert_by(x, cmp)
                    .map(|s| node.child[0].len() + 1 + s),
            },
        };
        self.update();
        res
    }
    /// `Ordering` で二分探索して、一致するものがあれば削除して要素とインデックスを変えます。
    pub fn delete_by<F: Fn(&T, &T) -> Ordering>(&mut self, x: &T, cmp: F) -> Option<(usize, T)> {
        fn delete_extremum<T>(root: &mut Box<Avltree<T>>, e: usize) -> T {
            let res = if root.0.as_ref().unwrap().child[1 - e].is_empty() {
                let swp = take(&mut root.0.as_mut().unwrap().child[e]);
                replace(&mut *root, swp).0.unwrap().value
            } else {
                delete_extremum(&mut root.0.as_mut().unwrap().child[1 - e], e)
            };
            root.update();
            res
        }
        let res = match &mut self.0 {
            None => None,
            Some(node) => match cmp(&x, &node.value) {
                Ordering::Less => node.child[0].delete_by(x, cmp),
                Ordering::Equal => Some(
                    match node.child.iter().position(|child| !child.is_empty()) {
                        None => (0, take(&mut self.0).unwrap().value),
                        Some(e) => {
                            let i = node.child[0].len();
                            let ext = delete_extremum(&mut node.child[e], e);
                            (i, replace(&mut node.value, ext))
                        }
                    },
                ),
                Ordering::Greater => node.child[1]
                    .delete_by(x, cmp)
                    .map(|(i, x)| (node.child[0].len() + 1 + i, x)),
            },
        };
        self.update();
        res
    }
    /// `bool` 値で二分探索して、一致するものがあればそのインデックスを返します。
    pub fn partition_point<F: Fn(&T, &T) -> bool>(&self, x: &T, f: F) -> usize {
        match &self.0 {
            None => 0,
            Some(node) => {
                if f(&x, &node.value) {
                    node.child[0].len() + 1 + node.child[1].partition_point(x, f)
                } else {
                    node.child[0].partition_point(x, f)
                }
            }
        }
    }
    /// 頂点を順番に訪問してクローンをくりかえして、`Vec<T>` に集めます。
    pub fn collect_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        let mut vec = Vec::new();
        self.for_each(&mut |x| vec.push(x.clone()));
        vec
    }
    /// 要素を順番に訪問します。
    pub fn for_each<F: FnMut(&T)>(&self, f: &mut F) {
        if let Some(node) = &self.0 {
            node.child[0].for_each(f);
            f(&node.value);
            node.child[1].for_each(f);
        }
    }
    fn update(&mut self) {
        if let Some(node) = &mut self.0 {
            let d = node.child[0].ht() as isize - node.child[1].ht() as isize;
            if 1 < d {
                let [a, b] = take(&mut node.child[0].0.as_mut().unwrap().child);
                let c = take(&mut node.child[1]);
                node.child.swap(0, 1);
                swap(
                    &mut node.value,
                    &mut node.child[1].0.as_mut().unwrap().value,
                );
                node.child[0] = a;
                node.child[1].0.as_mut().unwrap().child = [b, c];
                node.child[1].update();
            } else if d < -1 {
                let a = take(&mut node.child[0]);
                let [b, c] = take(&mut node.child[1].0.as_mut().unwrap().child);
                node.child.swap(0, 1);
                swap(
                    &mut node.value,
                    &mut node.child[0].0.as_mut().unwrap().value,
                );
                node.child[0].0.as_mut().unwrap().child = [a, b];
                node.child[1] = c;
                node.child[0].update();
            }
            node.update();
        }
    }
    fn ht(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.ht)
    }
    fn fmt_impl(&self, debug_set: &mut DebugSet<'_, '_>)
    where
        T: Debug,
    {
        if let Some(node) = self.0.as_ref() {
            node.child[0].fmt_impl(debug_set);
            debug_set.entry(&node.value);
            node.child[1].fmt_impl(debug_set);
        }
    }
}
impl<T: Ord> Avltree<T> {
    pub fn insert(&mut self, x: T) -> Option<usize> {
        self.insert_by(x, Ord::cmp)
    }
    pub fn delete(&mut self, x: &T) -> Option<(usize, T)> {
        self.delete_by(x, Ord::cmp)
    }
    pub fn lower_bound(&mut self, x: &T) -> usize {
        self.partition_point(x, PartialOrd::gt)
    }
    pub fn upper_bound(&mut self, x: &T) -> usize {
        self.partition_point(x, PartialOrd::ge)
    }
}
impl<T> Default for Avltree<T> {
    fn default() -> Self {
        Self(None)
    }
}
impl<T: Debug> Debug for Avltree<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_set = f.debug_set();
        self.fmt_impl(&mut debug_set);
        debug_set.finish()
    }
}

#[derive(Clone, Hash, PartialEq)]
pub struct Node<T> {
    ht: usize,
    len: usize,
    value: T,
    child: [Box<Avltree<T>>; 2],
}
impl<T> Node<T> {
    fn new(value: T) -> Self {
        Self {
            ht: 1,
            len: 1,
            value,
            child: [Box::new(Avltree::new()), Box::new(Avltree::new())],
        }
    }
    fn update(&mut self) {
        self.ht = self.child.iter().map(|child| child.ht()).max().unwrap() + 1;
        self.len = self.child.iter().map(|child| child.len()).sum::<usize>() + 1;
    }
}

#[cfg(test)]
mod tests {
    use {
        super::Avltree,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::fmt::Debug,
        superslice::Ext,
    };

    fn describe<T: Debug>(avl: &Avltree<T>) -> String {
        fn dfs<T: Debug>(avl: &Avltree<T>, s: &mut String) {
            if let Some(node) = avl.0.as_ref() {
                s.push('(');
                dfs(&node.child[0], s);
                s.push_str(&format!("{:?}", &node.value));
                dfs(&node.child[1], s);
                s.push(')');
            }
        }
        let mut s = String::new();
        dfs(avl, &mut s);
        s
    }

    #[test]
    fn test_structure_biased_ascending() {
        let mut avl = Avltree::<u32>::new();
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
        let mut avl = Avltree::<Reverse>::new();
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

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            const A: i32 = 40;
            const Q: usize = 200;
            let mut fast = Avltree::new();
            let mut brute = Brute::new();
            for _ in 0..Q {
                match rng.gen_range(0..6) {
                    // insert
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
                    // lower_bound
                    3 => {
                        let x = rng.gen_range(0..=A);
                        let result = fast.lower_bound(&x);
                        let expected = brute.lower_bound(&x);
                        assert_eq!(result, expected);
                    }
                    // upper_bound
                    4 => {
                        let x = rng.gen_range(0..=A);
                        let result = fast.upper_bound(&x);
                        let expected = brute.upper_bound(&x);
                        assert_eq!(result, expected);
                    }
                    // collect_vec
                    5 => {
                        let result = fast.collect_vec();
                        let expected = brute.collect_vec();
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
                println!("{:?}", &fast);
                let ht = fast.ht();
                let ht_lim = fast.len().next_power_of_two().trailing_zeros() as usize * 2 + 1;
                assert!(ht <= ht_lim);
            }
        }
    }

    #[test]
    fn test_avltree_fmt() {
        let mut set = Avltree::<u32>::new();
        assert_eq!("{}", format!("{:?}", &set).as_str());
        set.insert(10);
        assert_eq!("{10}", format!("{:?}", &set).as_str());
        set.insert(15);
        assert_eq!("{10, 15}", format!("{:?}", &set).as_str());
        set.insert(5);
        assert_eq!("{5, 10, 15}", format!("{:?}", &set).as_str());
    }
}
