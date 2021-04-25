//! Union Find のアルゴリズムで Disjoint Set Datastructure をします。
use std::{
    cell::RefCell,
    fmt::{Debug, Formatter, Result},
};

#[derive(Clone)]
pub struct UnionFind(RefCell<Vec<isize>>);
impl UnionFind {
    /// 構築です。
    pub fn new(len: usize) -> Self {
        Self(RefCell::new(vec![-1; len]))
    }
    /// 頂点がなければ `ture`、さもなくば `false` です。
    pub fn is_empty(&self) -> bool {
        self.0.borrow().is_empty()
    }
    /// 頂点数です。
    pub fn len(&self) -> usize {
        self.0.borrow().len()
    }
    /// 孤立頂点を増やします。
    pub fn push(&mut self) {
        self.0.borrow_mut().push(-1);
    }
    /// 親を探します。
    pub fn find(&self, i: usize) -> usize {
        self.find_and_size(i)[0]
    }
    /// 属する成分のサイズです。
    pub fn size(&self, i: usize) -> usize {
        self.find_and_size(i)[1]
    }
    /// くっつけます。
    pub fn union(&mut self, u: usize, v: usize) {
        let [mut u, su] = self.find_and_size(u);
        let [mut v, sv] = self.find_and_size(v);
        if u == v {
            return;
        }
        if su > sv {
            std::mem::swap(&mut u, &mut v);
            std::mem::swap(&mut v, &mut u);
        }
        let mut ref_mut = self.0.borrow_mut();
        ref_mut[v] = -((su + sv) as isize);
        ref_mut[u] = v as isize;
    }
    /// 同じ連結成分に入っていれば `true` です。
    pub fn same(&self, u: usize, v: usize) -> bool {
        self.find(u) == self.find(v)
    }
    /// 根ならば `true` です。
    pub fn is_root(&self, u: usize) -> bool {
        self.find(u) == u
    }
    fn find_and_size(&self, mut i: usize) -> [usize; 2] {
        assert!(i < self.0.borrow().len());
        loop {
            i = match self.0.borrow()[i] {
                x if 0 <= x => x as usize,
                x => return [i, (-x) as usize],
            };
        }
    }
}
impl Debug for UnionFind {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        use std::collections::HashMap;
        let mut map = HashMap::new();
        for i in 0..self.len() {
            map.entry(self.find(i)).or_insert_with(Vec::new).push(i);
        }
        f.debug_list().entries(map.values()).finish()
    }
}

#[cfg(test)]
mod tests {
    use {
        super::UnionFind,
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::DistinctTwo,
    };

    #[test]
    fn test_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for iter in 0..20 {
            println!("Testcase #{}", iter);
            let n = rng.gen_range(2..20);
            let q = 4 * n;
            let mut parent = (0..n).collect_vec();
            let mut uf = UnionFind::new(n);
            for _ in 0..q {
                match rng.gen_range(0..3) {
                    // union
                    0 => {
                        let (u, v) = rng.sample(DistinctTwo(0..n));
                        let orig_u = u;
                        let orig_v = v;
                        uf.union(u, v);
                        let u = parent[u];
                        let v = parent[v];
                        for i in 0..n {
                            if parent[i] == u || parent[i] == v {
                                parent[i] = u;
                            }
                        }
                        println!("union({}, {}): {:?}", orig_u, orig_v, &uf);
                    }
                    // same
                    1 => {
                        let (u, v) = rng.sample(DistinctTwo(0..n));
                        let result = uf.same(u, v);
                        let expected = parent[u] == parent[v];
                        println!("same({}, {}) = {}", u, v, result);
                        assert_eq!(result, expected);
                    }
                    // insert
                    2 => {
                        uf.push();
                        let new_vertex = parent.len();
                        parent.push(new_vertex);
                        println!("insert: {:?}", &uf);
                    }
                    _ => unreachable!(),
                }
            }
            println!();
        }
    }
}
