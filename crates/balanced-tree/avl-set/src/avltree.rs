use std::{
    cmp::Ordering,
    fmt::{Debug, DebugMap, DebugSet},
    mem::{replace, swap, take},
};

#[derive(Clone)]
pub struct Avltree<K, V>(Option<Box<Node<K, V>>>);
impl<K, V> Avltree<K, V> {
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
    pub fn insert_by<F: Fn(&K, &K) -> Ordering>(&mut self, k: K, v: V, cmp: F) -> Option<usize> {
        let res = match &mut self.0 {
            None => {
                self.0 = Some(Box::new(Node::new(k, v)));
                Some(0)
            }
            Some(node) => match cmp(&k, &node.key) {
                Ordering::Less => node.child[0].insert_by(k, v, cmp),
                Ordering::Equal => None,
                Ordering::Greater => node.child[1]
                    .insert_by(k, v, cmp)
                    .map(|s| node.child[0].len() + 1 + s),
            },
        };
        self.rotate_update();
        res
    }
    /// `Ordering` で二分探索して、一致するものがあれば削除して要素とインデックスを返します。
    pub fn delete_by<F: Fn(&K) -> Ordering>(&mut self, cmp: F) -> Option<(usize, K, V)> {
        fn delete_extremum<K, V>(root: &mut Box<Avltree<K, V>>, e: usize) -> (K, V) {
            let res = if root.0.as_ref().unwrap().child[1 - e].is_empty() {
                let swp = take(&mut root.0.as_mut().unwrap().child[e]);
                replace(&mut *root, swp).0.unwrap().into_kv()
            } else {
                delete_extremum(&mut root.0.as_mut().unwrap().child[1 - e], e)
            };
            root.rotate_update();
            res
        }
        let res = match &mut self.0 {
            None => None,
            Some(node) => match cmp(&node.key) {
                Ordering::Less => node.child[0].delete_by(cmp),
                Ordering::Equal => Some(
                    match node.child.iter().position(|child| !child.is_empty()) {
                        None => {
                            let old = take(&mut self.0).unwrap();
                            (0, old.key, old.value)
                        }
                        Some(e) => {
                            let i = node.child[0].len();
                            let (ext_k, ext_v) = delete_extremum(&mut node.child[e], e);
                            (
                                i,
                                replace(&mut node.key, ext_k),
                                replace(&mut node.value, ext_v),
                            )
                        }
                    },
                ),
                Ordering::Greater => node.child[1]
                    .delete_by(cmp)
                    .map(|(i, k, v)| (node.child[0].len() + 1 + i, k, v)),
            },
        };
        self.rotate_update();
        res
    }
    /// `bool` 値で二分探索して、一致するものがあればそのインデックスを返します。
    pub fn partition_point<F: Fn(&K) -> bool>(&self, f: F) -> usize {
        match &self.0 {
            None => 0,
            Some(node) => {
                if f(&node.key) {
                    node.child[0].len() + 1 + node.child[1].partition_point(f)
                } else {
                    node.child[0].partition_point(f)
                }
            }
        }
    }
    /// 頂点を順番に訪問してクローンをくりかえして、`Vec<T>` に集めます。
    pub fn collect_vec(&self) -> Vec<(K, V)>
    where
        K: Clone,
        V: Clone,
    {
        let mut vec = Vec::new();
        self.for_each(&mut |k, v| vec.push((k.clone(), v.clone())));
        vec
    }
    /// 頂点を順番に訪問してクローンをくりかえして、`Vec<T>` に集めます。
    pub fn collect_keys_vec(&self) -> Vec<K>
    where
        K: Clone,
    {
        let mut vec = Vec::new();
        self.for_each(&mut |k, _| vec.push(k.clone()));
        vec
    }
    /// 要素を昇順に訪問します。
    pub fn for_each<F: FnMut(&K, &V)>(&self, f: &mut F) {
        if let Some(node) = &self.0 {
            node.child[0].for_each(f);
            f(&node.key, &node.value);
            node.child[1].for_each(f);
        }
    }
    /// 要素を降順に訪問します。
    pub fn rfor_each<F: FnMut(&K, &V)>(&self, f: &mut F) {
        if let Some(node) = &self.0 {
            node.child[1].rfor_each(f);
            f(&node.key, &node.value);
            node.child[0].rfor_each(f);
        }
    }
    pub fn ht(&self) -> usize {
        self.0.as_ref().map_or(0, |node| node.ht)
    }
    fn rotate(&mut self) {
        if let Some(node) = &mut self.0 {
            let d = node.child[0].ht() as isize - node.child[1].ht() as isize;
            if 1 < d {
                let [a, b] = take(&mut node.child[0].0.as_mut().unwrap().child);
                let c = take(&mut node.child[1]);
                node.child.swap(0, 1);
                swap(&mut node.key, &mut node.child[1].0.as_mut().unwrap().key);
                swap(
                    &mut node.value,
                    &mut node.child[1].0.as_mut().unwrap().value,
                );
                node.child[0] = a;
                node.child[1].0.as_mut().unwrap().child = [b, c];
                node.child[1].0.as_mut().unwrap().update();
            } else if d < -1 {
                let a = take(&mut node.child[0]);
                let [b, c] = take(&mut node.child[1].0.as_mut().unwrap().child);
                node.child.swap(0, 1);
                swap(&mut node.key, &mut node.child[0].0.as_mut().unwrap().key);
                swap(
                    &mut node.value,
                    &mut node.child[0].0.as_mut().unwrap().value,
                );
                node.child[0].0.as_mut().unwrap().child = [a, b];
                node.child[1] = c;
                node.child[0].0.as_mut().unwrap().update();
            }
        }
    }
    fn rotate_update(&mut self) {
        self.rotate();
        if let Some(node) = &mut self.0 {
            node.update();
        }
    }
    pub fn fmt_keys_impl(&self, debug_map: &mut DebugSet<'_, '_>)
    where
        K: Debug,
    {
        if let Some(node) = self.0.as_ref() {
            node.child[0].fmt_keys_impl(debug_map);
            debug_map.entry(&node.key);
            node.child[1].fmt_keys_impl(debug_map);
        }
    }
    fn fmt_impl(&self, debug_map: &mut DebugMap<'_, '_>)
    where
        K: Debug,
        V: Debug,
    {
        if let Some(node) = self.0.as_ref() {
            node.child[0].fmt_impl(debug_map);
            debug_map.entry(&node.key, &node.value);
            node.child[1].fmt_impl(debug_map);
        }
    }
}
impl<K, V> Default for Avltree<K, V> {
    fn default() -> Self {
        Self(None)
    }
}
impl<K: Debug, V: Debug> Debug for Avltree<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_map = f.debug_map();
        self.fmt_impl(&mut debug_map);
        debug_map.finish()
    }
}

#[derive(Clone)]
pub struct Node<K, V> {
    ht: usize,
    len: usize,
    key: K,
    value: V,
    child: [Box<Avltree<K, V>>; 2],
}
impl<K, V> Node<K, V> {
    fn new(k: K, v: V) -> Self {
        Self {
            ht: 1,
            len: 1,
            key: k,
            value: v,
            child: [Box::new(Avltree::new()), Box::new(Avltree::new())],
        }
    }
    fn update(&mut self) {
        self.ht = self.child.iter().map(|child| child.ht()).max().unwrap() + 1;
        self.len = self.child.iter().map(|child| child.len()).sum::<usize>() + 1;
    }
    fn into_kv(self) -> (K, V) {
        (self.key, self.value)
    }
}

#[cfg(test)]
pub mod utils {
    use {super::Avltree, std::fmt::Debug};

    pub fn describe_set<K: Debug, V>(avl: &Avltree<K, V>) -> String {
        fn dfs<K: Debug, V>(avl: &Avltree<K, V>, s: &mut String) {
            if let Some(node) = avl.0.as_ref() {
                s.push('(');
                dfs(&node.child[0], s);
                s.push_str(&format!("{:?}", &node.key));
                dfs(&node.child[1], s);
                s.push(')');
            }
        }
        let mut s = String::new();
        dfs(avl, &mut s);
        s
    }
}
