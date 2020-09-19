use rand::prelude::*;

#[derive(Debug, Clone, PartialEq)]
pub struct UnionFind {
    table: Vec<isize>,
}
impl UnionFind {
    pub fn new(len: usize) -> Self {
        Self {
            table: vec![-1; len],
        }
    }
    pub fn size(&mut self, mut i: usize) -> usize {
        i = self.root(i);
        (-self.table[i]) as usize
    }
    pub fn root(&mut self, i: usize) -> usize {
        if self.table[i] < 0 {
            i
        } else {
            let p = self.table[i] as usize;
            let root = self.root(p);
            self.table[i] = root as isize;
            root
        }
    }
    pub fn unite(&mut self, mut i: usize, mut j: usize) -> bool {
        i = self.root(i);
        j = self.root(j);
        if i == j {
            false
        } else {
            if self.size(i) < self.size(j) {
                std::mem::swap(&mut i, &mut j);
            }
            self.table[i] += self.table[j];
            self.table[j] = i as isize;
            true
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Brute(Vec<Vec<usize>>);
impl Brute {
    pub fn new(len: usize) -> Self {
        Self((0..len).map(|i| vec![i]).collect())
    }
    pub fn find(&self, i: usize) -> usize {
        self.0
            .iter()
            .position(|v| v.iter().any(|&x| x == i))
            .unwrap()
    }
    pub fn unite(&mut self, x: usize, y: usize) -> bool {
        let i = self.find(x);
        let j = self.find(y);
        if i == j {
            false
        } else {
            let v = self.0.remove(i.max(j));
            self.0[i.min(j)].extend(v);
            true
        }
    }
}

pub struct Query<'a> {
    pub len: usize,
    pub rng: &'a mut StdRng,
}
impl<'a> Query<'a> {
    pub fn unite(&mut self) -> (usize, usize) {
        (
            self.rng.gen_range(0, self.len),
            self.rng.gen_range(0, self.len),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use query_test::query;

    #[test]
    pub fn test_uf_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..3 {
            let len = rng.gen_range(1, 20);
            let mut instance = query_test::Instance {
                query: Query {
                    len: len,
                    rng: &mut rng,
                },
                brute: Brute::new(len),
                fast: UnionFind::new(len),
            };
            for _ in 0..10 {
                match instance.query.rng.gen_range(0, 100) {
                    0..=99 => instance.apply(query!(unite, u, v)),
                    _ => unreachable!(),
                }
            }
        }
    }
}
