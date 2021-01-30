pub fn hungarian(cost_matrix: &[Vec<i64>]) -> HungarianResult {
    let h = cost_matrix.len();
    let w = cost_matrix[0].len();
    let mut m = vec![std::usize::MAX; w + 1];
    let all_min = *cost_matrix.iter().flatten().min().unwrap();
    let mut left = cost_matrix
        .iter()
        .map(|v| *v.iter().min().unwrap() - all_min)
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let mut right = vec![0; w].into_boxed_slice();

    for s in 0..h {
        // dijkstra
        let (pi, mut y) = {
            let mut used_l = vec![false; h];
            let mut used_r = vec![false; w + 1];
            let mut pi = vec![w; w];
            let mut dist = vec![std::i64::MAX; w];
            m[w] = s;
            let mut x0 = s;
            let mut y0 = w;
            while x0 != std::usize::MAX {
                // find y0
                let (swap, delta) = {
                    let mut swap = w;
                    used_r[y0] = true;
                    used_l[x0] = true;
                    let mut delta = std::i64::MAX;
                    for y in (0..w).filter(|&y| !used_r[y]) {
                        let cost = cost_matrix[x0][y] - (right[y] - left[x0]);
                        if cost < dist[y] {
                            pi[y] = y0;
                            dist[y] = cost;
                        }
                        if dist[y] < delta {
                            swap = y;
                            delta = dist[y];
                        }
                    }
                    (swap, delta)
                };

                // update x0, y0
                y0 = swap;
                x0 = m[y0];

                // update potential
                for i in (0..h).filter(|&i| !used_l[i]) {
                    left[i] += delta;
                }
                for j in (0..w).filter(|&i| !used_r[i]) {
                    right[j] += delta;
                    dist[j] -= delta;
                }
            }
            (pi, y0)
        };
        // augmentation
        while y != w {
            m[y] = m[pi[y]];
            y = pi[y];
        }
    }
    m.pop();

    let backward = m;
    let mut forward = vec![std::usize::MAX; h].into_boxed_slice();
    let mut value = 0;
    for (y, &x) in backward.iter().enumerate() {
        if x != std::usize::MAX {
            forward[x] = y;
            value += cost_matrix[x][y];
        }
    }
    let backward = backward
        .into_iter()
        .map(|x| if x == std::usize::MAX { None } else { Some(x) })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    HungarianResult {
        forward,
        backward,
        left,
        right,
        value,
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct HungarianResult {
    pub forward: Box<[usize]>,
    pub backward: Box<[Option<usize>]>,
    pub left: Box<[i64]>,
    pub right: Box<[i64]>,
    pub value: i64,
}

#[cfg(test)]
mod tests {
    use std::{assert_eq, mem::swap};

    use {
        super::{hungarian, HungarianResult},
        dbg::{lg, tabular},
        itertools::Itertools,
        next_permutation::permutations_map,
        rand::{
            prelude::{Rng, StdRng},
            SeedableRng,
        },
        std::iter::repeat_with,
        test_case::test_case,
    };

    #[test_case(vec![vec![4, 3, 5], vec![3, 5, 9], vec![4, 1, 4]] => (vec![2, 0, 1], 9); "yosupo sample")]
    #[test_case(vec![vec![4, 3, 5], vec![3, 5, 0], vec![4, 1, 4]] => (vec![0, 2, 1], 5); "handmade")]
    fn test_hand(cost_matrix: Vec<Vec<i64>>) -> (Vec<usize>, i64) {
        let HungarianResult { forward, value, .. } = hungarian(&cost_matrix);
        (forward.into_vec(), value)
    }

    #[test_case(5, 5, 100, true)]
    #[test_case(5, 5, 1000, false)]
    #[test_case(30, 500, 30, false)]
    fn test_rand(h: usize, w: usize, iter: usize, brute: bool) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iter {
            let mut h = rng.gen_range(1..=h);
            let mut w = rng.gen_range(1..=w);
            if h > w {
                swap(&mut h, &mut w);
            }
            let cost_matrix =
                repeat_with(|| repeat_with(|| rng.gen_range(0..=1)).take(w).collect_vec())
                    .take(h)
                    .collect_vec();
            tabular!(&cost_matrix);
            let result = hungarian(&cost_matrix);
            if brute {
                compare_with_brute(&cost_matrix, &result);
            }
            validate(&cost_matrix, &result);
        }
    }

    fn validate(cost_matrix: &[Vec<i64>], result: &HungarianResult) {
        let h = cost_matrix.len();
        let w = cost_matrix[0].len();
        let HungarianResult {
            left,
            right,
            forward,
            backward,
            value,
        } = result;
        lg!(&left);
        lg!(&right);

        // partial 1 on 1 correspondence
        assert_eq!(backward.iter().filter(|&x| x.is_some()).count(), h);
        for i in 0..h {
            assert_eq!(i, backward[forward[i]].unwrap());
        }
        for j in 0..w {
            if let Some(i) = backward[j] {
                assert_eq!(j, forward[i]);
            }
        }

        // feasibility
        for (i, j, x) in cost_matrix
            .iter()
            .enumerate()
            .map(|(i, v)| v.iter().enumerate().map(move |(j, &x)| (i, j, x)))
            .flatten()
        {
            assert!(
                right[j] - left[i] <= x,
                "left[{i}] = {left}, right[{j}] = {right}, cost_matrix[{i}][{j}] = {cost}",
                i = i,
                left = left[i],
                j = j,
                right = right[j],
                cost = x,
            );
        }

        // saturation
        for (i, &j) in forward.iter().enumerate() {
            assert_eq!(cost_matrix[i][j], right[j] - left[i]);
        }

        // value is correct
        assert_eq!(
            *value,
            forward
                .iter()
                .enumerate()
                .map(|(i, &j)| cost_matrix[i][j])
                .sum::<i64>()
        );
    }

    fn compare_with_brute(cost_matrix: &[Vec<i64>], result: &HungarianResult) {
        let h = cost_matrix.len();
        let w = cost_matrix[0].len();
        let brute_value = permutations_map((0..w).collect_vec(), |v| {
            calculate_score(cost_matrix, v[..h].iter().copied())
        })
        .min()
        .unwrap();
        assert_eq!(brute_value, result.value);
    }

    fn calculate_score(cost_matrix: &[Vec<i64>], perm: impl IntoIterator<Item = usize>) -> i64 {
        perm.into_iter()
            .enumerate()
            .map(|(i, j)| cost_matrix[i][j])
            .sum::<i64>()
    }
}
