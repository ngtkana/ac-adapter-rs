pub fn hungarian(cost_table: &[Vec<i64>]) -> HungarianResult {
    let h = cost_table.len();
    let w = cost_table[0].len();
    let mut right2left = vec![None; w + 1];
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
            right2left[w] = Some(s);
            loop {
                let (y0, delta) = (0..w)
                    .filter(|&y| !in_tree[y])
                    .map(|y| (y, phi.reduced_cost(right2left[pi[y]].unwrap(), y)))
                    .min_by_key(|&(_, d)| d)
                    .unwrap();
                phi.left[s] -= delta;
                for y in (0..w).filter(|&y| in_tree[y]) {
                    phi.left[right2left[y].unwrap()] -= delta;
                    phi.right[y] -= delta;
                }
                if right2left[y0].is_none() {
                    break (pi, y0);
                }
                in_tree[y0] = true;
                (0..w).filter(|&y| !in_tree[y]).for_each(|y| {
                    pi[y] = [pi[y], y0]
                        .iter()
                        .copied()
                        .min_by_key(|&_y| phi.reduced_cost(right2left[_y].unwrap(), y))
                        .unwrap()
                });
            }
        };
        // augmentation
        while y != w {
            let next_y = pi[y];
            let x = right2left[next_y].unwrap();
            right2left[y] = Some(x);
            y = next_y;
        }
    }
    right2left.pop();

    let Potential {
        left,
        right,
        cost_table,
    } = phi;
    let right2left = right2left.into_boxed_slice();
    let mut left2right = vec![std::usize::MAX; h].into_boxed_slice();
    let mut value = 0;
    for (x, y) in right2left.iter().enumerate().map(|(y, x)| (x.unwrap(), y)) {
        left2right[x] = y;
        value += cost_table[x][y];
    }
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
