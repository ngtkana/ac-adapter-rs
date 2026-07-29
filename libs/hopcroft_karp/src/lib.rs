use std::{collections::VecDeque, slice::Iter};

pub fn hopcroft_karp(g: &[Vec<usize>]) -> Vec<usize> {
    let n = g.len();
    let mut queue = VecDeque::new();
    let mut f = vec![usize::MAX; n];
    let mut label = vec![usize::MAX; n];
    for x in (0..n).filter(|&i| !g[i].is_empty()) {
        queue.push_back(x);
        label[x] = 0;
    }
    let mut iter = g.iter().map(|g| g.iter()).collect::<Vec<_>>();
    loop {
        let orig_count = queue.len();
        while let Some(x) = queue.pop_front() {
            for &y in &g[x] {
                if label[y] == usize::MAX {
                    label[y] = label[x] + 1;
                    let z = f[y];
                    if z != usize::MAX && label[z] == usize::MAX {
                        label[z] = label[x] + 2;
                        queue.push_back(z);
                    }
                }
            }
        }
        for (g, iter) in g.iter().zip(&mut iter) {
            *iter = g.iter();
        }
        for x in 0..n {
            if label[x] == 0 && !primal(x, &mut label, &mut iter, &mut f) {
                queue.push_back(x);
            }
        }
        if orig_count == queue.len() || queue.is_empty() {
            return f;
        }
        label.fill(usize::MAX);
        for &x in &queue {
            label[x] = 0;
        }
    }
}

fn primal(x: usize, label: &mut [usize], iter: &mut [Iter<'_, usize>], f: &mut [usize]) -> bool {
    while let Some(&y) = iter[x].next() {
        if label[x] + 1 == label[y] {
            let z = f[y];
            if z == usize::MAX || (label[x] + 2 == label[z] && primal(z, label, iter, f)) {
                f[y] = x;
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{Rng, SeedableRng, rngs::StdRng, seq::SliceRandom};

    fn naive(g: &[Vec<usize>]) -> Vec<usize> {
        let n = g.len();
        let Some(i) = (0..n).find(|&i| !g[i].is_empty()) else {
            return vec![usize::MAX; n];
        };
        let mut g = g.to_vec();
        let gi = std::mem::take(&mut g[i]);
        let mut cands = vec![];
        cands.push(naive(&g));
        for j in gi {
            let mut g = g.clone();
            for g in &mut g {
                g.retain(|&x| x != j);
            }
            let mut result = naive(&g);
            result[j] = i;
            cands.push(result);
        }
        cands
            .into_iter()
            .max_by_key(|result| result.iter().filter(|&&x| x != usize::MAX).count())
            .unwrap()
    }

    #[test]
    fn test() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(0..=16);
            let l = rng.gen_range(0..=n);
            let r = n - l;
            let m = rng.gen_range(0..=l * r);

            let mut is_left = vec![false; n];
            is_left[..l].fill(true);
            is_left.shuffle(&mut rng);

            let mut g = vec![vec![]; n];
            for _ in 0..m {
                loop {
                    let i = rng.gen_range(0..n);
                    let j = rng.gen_range(0..n);
                    if !is_left[i] || is_left[j] || g[i].contains(&j) {
                        continue;
                    }
                    g[i].push(j);
                    break;
                }
            }

            let result = hopcroft_karp(&g);
            let expected = naive(&g);
            assert_eq!(
                result.iter().filter(|&&x| x != usize::MAX).count(),
                expected.iter().filter(|&&x| x != usize::MAX).count(),
                "result = {result:?}, expected = {expected:?}, is_left = {is_left:?}, g = {g:?}",
            );
        }
    }
}
