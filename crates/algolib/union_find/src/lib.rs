//! Union Find のアルゴリズムで Disjoint Set Datastructure をします。
use std::cell::Cell;

#[derive(Clone, Debug)]
pub struct UnionFind(Vec<Cell<ParentOrSize>>);
impl UnionFind {
    /// 構築です。
    pub fn new(len: usize) -> Self {
        Self(vec![Cell::new(ParentOrSize::Size(1)); len])
    }
    /// 親を探します。
    pub fn find(&self, i: usize) -> usize {
        self.find_and_size(i).root
    }
    /// 属する成分のサイズです。
    pub fn size(&self, i: usize) -> usize {
        self.find_and_size(i).size
    }
    /// くっつけます。
    pub fn unite(&mut self, u: usize, v: usize) {
        let RootAndSize {
            root: mut u,
            size: su,
        } = self.find_and_size(u);
        let RootAndSize {
            root: mut v,
            size: sv,
        } = self.find_and_size(v);
        if u == v {
            return;
        }
        if su > sv {
            std::mem::swap(&mut u, &mut v);
            std::mem::swap(&mut v, &mut u);
        }
        self.0[v].set(ParentOrSize::Size(su + sv));
        self.0[u].set(ParentOrSize::Parent(v));
    }
    /// 同じ連結成分に入っていれば `true` です。
    pub fn same(&self, u: usize, v: usize) -> bool {
        self.find(u) == self.find(v)
    }
    /// 根ならば `true` です。
    pub fn is_root(&self, u: usize) -> bool {
        self.find(u) == u
    }
    fn find_and_size(&self, i: usize) -> RootAndSize {
        assert!(i < self.0.len());
        match self.0[i].get() {
            ParentOrSize::Parent(p) => {
                let ret = self.find_and_size(p);
                self.0[i].set(ParentOrSize::Parent(ret.root));
                ret
            }
            ParentOrSize::Size(size) => RootAndSize { root: i, size },
        }
    }
}
#[derive(Clone, Copy, Debug)]
enum ParentOrSize {
    Parent(usize),
    Size(usize),
}
#[derive(Clone, Copy, Debug)]
struct RootAndSize {
    root: usize,
    size: usize,
}

#[cfg(test)]
mod tests {
    use super::UnionFind;

    #[test]
    fn test_hand() {
        let mut uf = UnionFind::new(5);
        assert!((0..5).all(|i| uf.is_root(i) && uf.size(i) == 1));
        assert!((0..5).all(|i| (0..5).all(|j| i == j || !uf.same(i, j))));

        uf.unite(0, 2);
        assert!(uf.size(0) == 2);
        assert!(uf.size(1) == 1);
        assert!(uf.size(2) == 2);
        assert!(uf.size(3) == 1);
        assert!(uf.size(4) == 1);
        assert!((0..5)
            .all(|i| (0..5).all(|j| i == j || uf.same(i, j) == matches!((i, j), (0, 2) | (2, 0)))));
    }
}
