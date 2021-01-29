pub fn hungarian(cost_table: &[Vec<i64>]) -> HungarianResult {
    let h = cost_table.len();
    let w = cost_table[0].len();
    let mut right2left = vec![std::usize::MAX; w + 1];
    let mut phi = Potential {
        left: cost_table
            .iter()
            .map(|v| -*v.iter().min().unwrap())
            .collect::<Vec<_>>()
            .into_boxed_slice(),
        right: vec![0; w].into_boxed_slice(),
        cost_table,
    };
    for s in 0..h {
        // dijkstra
        let (pi, mut y) = {
            let mut in_tree = vec![false; w + 1];
            in_tree[w] = true;
            let mut pi = vec![w; w];
            let mut mininum_reduced_cost = (0..w)
                .map(|y| phi.reduced_cost(s, y))
                .collect::<Vec<_>>()
                .into_boxed_slice();
            right2left[w] = s;
            loop {
                let y0 = (0..w)
                    .filter(|&y| !in_tree[y])
                    .min_by_key(|&y| mininum_reduced_cost[y])
                    .unwrap();
                let delta = mininum_reduced_cost[y0];
                phi.left[s] -= delta;
                for y in 0..w {
                    if in_tree[y] {
                        phi.left[right2left[y]] -= delta;
                        phi.right[y] -= delta;
                    } else {
                        mininum_reduced_cost[y0] -= delta;
                    }
                }
                if right2left[y0] == std::usize::MAX {
                    break (pi, y0);
                }
                in_tree[y0] = true;
                for y in (0..w).filter(|&y| !in_tree[y]) {
                    let new_cost = phi.reduced_cost(right2left[y0], y);
                    if !in_tree[y] && new_cost < mininum_reduced_cost[y] {
                        pi[y] = y0;
                        mininum_reduced_cost[y] = new_cost;
                    }
                }
            }
        };
        // augmentation
        while y != w {
            right2left[y] = right2left[pi[y]];
            y = pi[y];
        }
    }
    right2left.pop();

    let Potential {
        left,
        right,
        cost_table,
    } = phi;
    let mut left2right = vec![std::usize::MAX; h].into_boxed_slice();
    let mut value = 0;
    for (y, &x) in right2left.iter().enumerate() {
        left2right[x] = y;
        value += cost_table[x][y];
    }
    let right2left = right2left
        .into_iter()
        .map(|x| if x == std::usize::MAX { None } else { Some(x) })
        .collect::<Vec<_>>()
        .into_boxed_slice();
    HungarianResult {
        left2right,
        right2left,
        left,
        right,
        value,
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Potential<'a> {
    pub left: Box<[i64]>,
    pub right: Box<[i64]>,
    pub cost_table: &'a [Vec<i64>],
}
impl<'a> Potential<'a> {
    pub fn reduced_cost(&self, i: usize, j: usize) -> i64 {
        self.cost_table[i][j] - (self.right[j] - self.left[i])
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct HungarianResult {
    pub left2right: Box<[usize]>,
    pub right2left: Box<[Option<usize>]>,
    pub left: Box<[i64]>,
    pub right: Box<[i64]>,
    pub value: i64,
}

#[cfg(test)]
mod tests {
    use {
        super::{hungarian, HungarianResult},
        test_case::test_case,
    };

    #[test_case(vec![vec![4, 3, 5], vec![3, 5, 9], vec![4, 1, 4]] => (vec![2, 0, 1], 9); "yosupo sample")]
    #[test_case(vec![vec![4, 3, 5], vec![3, 5, 0], vec![4, 1, 4]] => (vec![0, 2, 1], 5); "handmade")]
    fn test_hand(cost_table: Vec<Vec<i64>>) -> (Vec<usize>, i64) {
        let HungarianResult {
            left2right, value, ..
        } = hungarian(&cost_table);
        (left2right.into_vec(), value)
    }
}
