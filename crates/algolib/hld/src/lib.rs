use std::iter::Iterator;

#[derive(Debug, Clone, PartialEq)]
pub struct HLD {
    root: usize,
    g: Vec<Vec<usize>>,
    head: Vec<usize>,
    parent: Vec<usize>,
    pub ord: Vec<usize>,
    pub vid: Vec<usize>,
}
impl HLD {
    pub fn new(mut g: Vec<Vec<usize>>, root: usize) -> Self {
        let n = g.len();

        fn dfs(x: usize, p: usize, parent: &mut [usize], size: &mut [u32], g: &mut [Vec<usize>]) {
            let mut child = g[x].iter().copied().filter(|&y| y != p).collect::<Vec<_>>();
            for &c in &child {
                dfs(c, x, parent, size, g);
                size[x] += size[c];
                parent[c] = x;
            }
            for i in 0..child.len() {
                if size[child[0]] < size[child[i]] {
                    child.swap(0, i);
                }
            }
            g[x] = child
        }
        let mut size = vec![1; n];
        let mut parent = vec![std::usize::MAX; n];
        parent[root] = root;
        dfs(root, root, &mut parent, &mut size, &mut g);

        fn efs(
            x: usize,
            head: &mut [usize],
            ord: &mut Vec<usize>,
            vid: &mut [usize],
            g: &[Vec<usize>],
        ) {
            vid[x] = ord.len();
            ord.push(x);
            if !g[x].is_empty() {
                head[g[x][0]] = head[x];
            }
            g[x].iter().for_each(|&y| efs(y, head, ord, vid, g));
        }
        let mut head = (0..n).collect::<Vec<_>>();
        let mut ord = Vec::new();
        let mut vid = vec![std::usize::MAX; n];
        efs(root, &mut head, &mut ord, &mut vid, &g);
        Self {
            root,
            g,
            head,
            ord,
            vid,
            parent,
        }
    }
    pub fn lca(&self, u: usize, v: usize) -> usize {
        self.ord[self.iter_vtx(u, v).last().unwrap().0]
    }
    pub fn iter_vtx<'a>(&'a self, u: usize, v: usize) -> Iter<'a> {
        Iter {
            hld: self,
            u,
            v,
            include_lca: IncludeLca::Yes,
            finished: false,
        }
    }
    pub fn iter_edge<'a>(&'a self, u: usize, v: usize) -> Iter<'a> {
        Iter {
            hld: self,
            u,
            v,
            include_lca: IncludeLca::No,
            finished: false,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Iter<'a> {
    hld: &'a HLD,
    u: usize,
    v: usize,
    include_lca: IncludeLca,
    finished: bool,
}
impl<'a> Iterator for Iter<'a> {
    type Item = (usize, usize);
    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            None
        } else {
            if self.hld.vid[self.u] > self.hld.vid[self.v] {
                std::mem::swap(&mut self.u, &mut self.v);
            }
            let res = if self.hld.head[self.u] != self.hld.head[self.v] {
                let res = (self.hld.vid[self.hld.head[self.v]], self.hld.vid[self.v]);
                self.v = self.hld.parent[self.hld.head[self.v]];
                res
            } else {
                self.finished = true;
                match self.include_lca {
                    IncludeLca::Yes => (self.hld.vid[self.u], self.hld.vid[self.v]),
                    IncludeLca::No => (self.hld.vid[self.u] + 1, self.hld.vid[self.v]),
                }
            };
            Some(res)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Copy, Eq)]
enum IncludeLca {
    Yes,
    No,
}

#[cfg(test)]
mod tests {
    use super::HLD;
    use rand::prelude::*;
    use randtools::{LogUniform, Open, Tree};

    #[test]
    fn test_singleton() {
        let g = vec![Vec::new()];
        let _ = HLD::new(g, 0);
    }

    #[test]
    fn test_rand_small() {
        test_rand(20);
    }

    #[test]
    fn test_rand_large() {
        test_rand(1_000);
    }

    fn test_rand(size_lim: usize) {
        let mut rng = StdRng::seed_from_u64(42);

        for test_id in 0..100 {
            let n = rng.sample(LogUniform(2, size_lim));
            println!("Test {}, n = {}", test_id, n);
            let root = rng.gen_range(0, n);
            let g = rng.sample(Tree(n));
            let hld = HLD::new(g.clone(), root);
            for _ in 0..20 {
                let (s, t) = rng.sample(Open(0, n));

                // lca
                let lca = hld.lca(s, t);
                let lca_expected = lca_brute(&g, s, t, root);
                assert_eq!(lca, lca_expected);

                // vtx vs edge
                let mut path_v = psp_path_unsorted(&hld, s, t);
                let mut path_e = psp_path_unsorted_without_lca(&hld, s, t);
                path_e.push(lca);
                path_v.sort();
                path_e.sort();
                assert_eq!(&path_v, &path_e);

                // vs bfs
                let mut expected = bfs::psp_path(&g, s, t).unwrap();
                expected.sort();
                assert_eq!(&path_v, &expected);

                // call count
                let cnt = count_call_count(&hld, s, t);
                assert!(cnt < expected_call_count_max(n));
            }
        }
    }

    fn psp_path_unsorted(hld: &HLD, s: usize, t: usize) -> Vec<usize> {
        hld.iter_vtx(s, t)
            .map(|(l, r)| (l..=r).map(|i| hld.ord[i]))
            .flatten()
            .collect()
    }

    fn psp_path_unsorted_without_lca(hld: &HLD, s: usize, t: usize) -> Vec<usize> {
        hld.iter_edge(s, t)
            .map(|(l, r)| (l..=r).map(|i| hld.ord[i]))
            .flatten()
            .collect()
    }

    fn expected_call_count_max(n: usize) -> u32 {
        let lg = n.next_power_of_two().trailing_zeros();
        2 * lg + 1
    }

    fn count_call_count(hld: &HLD, s: usize, t: usize) -> u32 {
        hld.iter_vtx(s, t).count() as u32
    }

    fn lca_brute(g: &[Vec<usize>], u: usize, v: usize, root: usize) -> usize {
        let a = bfs::psp_path(&g, root, u).unwrap();
        let b = bfs::psp_path(&g, root, v).unwrap();
        a.into_iter()
            .zip(b.into_iter())
            .take_while(|(x, y)| x == y)
            .last()
            .unwrap()
            .0
    }
}
