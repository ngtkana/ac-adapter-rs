#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! union-find です。

#[derive(Clone, Copy, Debug)]
enum ParentOrSize {
    Parent(usize),
    Size(usize),
}

/// union-find です。
#[derive(Clone, Debug)]
pub struct UnionFind(Vec<ParentOrSize>);

impl UnionFind {
    /// 構築です。
    ///
    /// # Example
    ///
    /// ```
    /// let uf = union_find::UnionFind::new(3);
    /// ```
    pub fn new(len: usize) -> Self {
        Self(vec![ParentOrSize::Size(1); len])
    }

    /// 空かどうかです。
    ///
    /// # Example
    ///
    /// ```
    /// assert!(!union_find::UnionFind::new(3).is_empty());
    /// assert!(union_find::UnionFind::new(0).is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// 長さです。
    ///
    /// # Example
    ///
    /// ```
    /// assert_eq!(union_find::UnionFind::new(3).len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// 親を探します。
    ///
    /// # Example
    ///
    /// ```
    /// let mut uf = union_find::UnionFind::new(3);
    /// assert_ne!(uf.find(0), uf.find(1));
    /// uf.unite(0, 1);
    /// assert_eq!(uf.find(0), uf.find(1));
    /// ```
    pub fn find(&mut self, i: usize) -> usize {
        self.find_and_size(i).0
    }

    /// 属する成分のサイズです。
    ///
    /// # Example
    ///
    /// ```
    /// let mut uf = union_find::UnionFind::new(3);
    /// assert_eq!(uf.size(0), 1);
    /// uf.unite(0, 1);
    /// assert_eq!(uf.size(0), 2);
    /// ```
    pub fn size(&mut self, i: usize) -> usize {
        self.find_and_size(i).1
    }

    fn find_and_size(&mut self, i: usize) -> (usize, usize) {
        assert!(i < self.len());
        match self.0[i] {
            ParentOrSize::Parent(p) => {
                let ret = self.find_and_size(p);
                self.0[i] = ParentOrSize::Parent(ret.0);
                ret
            }
            ParentOrSize::Size(si) => (i, si),
        }
    }

    /// くっつけます。
    ///
    /// # Example
    ///
    /// ```
    /// let mut uf = union_find::UnionFind::new(3);
    /// uf.unite(0, 1);
    /// ```
    pub fn unite(&mut self, u: usize, v: usize) {
        let (mut u, su) = self.find_and_size(u);
        let (mut v, sv) = self.find_and_size(v);
        if u == v {
            return;
        }
        if su > sv {
            std::mem::swap(&mut u, &mut v);
            std::mem::swap(&mut v, &mut u);
        }
        self.0[v] = ParentOrSize::Size(su + sv);
        self.0[u] = ParentOrSize::Parent(v);
    }

    /// 同じ連結成分に入っているかどうかです。
    ///
    /// # Example
    ///
    /// ```
    /// let mut uf = union_find::UnionFind::new(3);
    /// assert!(!uf.same(0, 1));
    /// uf.unite(0, 1);
    /// assert!(uf.same(0, 1));
    /// ```
    pub fn same(&mut self, u: usize, v: usize) -> bool {
        self.find(u) == self.find(v)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
