use std::{
    cmp::Ordering,
    fmt::{Debug, DebugSet},
    mem::{replace, swap, take},
};

#[derive(Clone)]
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
    /// `Ordering` で二分探索して、一致するものがなければ挿入してインデックスを返します。
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
    /// `Ordering` で二分探索して、一致するものがあれば削除して要素とインデックスを返します。
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
    pub fn partition_point<F: Fn(&T) -> bool>(&self, f: F) -> usize {
        match &self.0 {
            None => 0,
            Some(node) => {
                if f(&node.value) {
                    node.child[0].len() + 1 + node.child[1].partition_point(f)
                } else {
                    node.child[0].partition_point(f)
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
    /// 要素を昇順に訪問します。
    pub fn for_each<F: FnMut(&T)>(&self, f: &mut F) {
        if let Some(node) = &self.0 {
            node.child[0].for_each(f);
            f(&node.value);
            node.child[1].for_each(f);
        }
    }
    /// 要素を降順に訪問します。
    pub fn rfor_each<F: FnMut(&T)>(&self, f: &mut F) {
        if let Some(node) = &self.0 {
            node.child[1].rfor_each(f);
            f(&node.value);
            node.child[0].rfor_each(f);
        }
    }
    pub fn ht(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.ht)
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

#[derive(Clone)]
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
pub mod utils {
    use {super::Avltree, std::fmt::Debug};

    pub fn describe<T: Debug>(avl: &Avltree<T>) -> String {
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
}
