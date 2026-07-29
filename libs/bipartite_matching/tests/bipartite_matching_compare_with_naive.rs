use bipartite_matching::bipartite_matching;
use rand::{rngs::StdRng, seq::SliceRandom, Rng, SeedableRng};

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

        let result = bipartite_matching(&g);
        let expected = naive(&g);
        assert_eq!(
            result.iter().filter(|&&x| x != usize::MAX).count(),
            expected.iter().filter(|&&x| x != usize::MAX).count(),
            "result = {result:?}, expected = {expected:?}, is_left = {is_left:?}, g = {g:?}",
        );
    }
}
