use std::mem;

pub fn is_tree(g: &[Vec<usize>]) -> bool {
    // 頂点数 n, 辺数 2n - 2, 頂点番号 < n
    let n = g.len();
    if g.iter().map(std::vec::Vec::len).sum::<usize>() != 2 * n - 2 || g.iter().flatten().any(|&x| n <= x)
    {
        return false;
    }
    // 連結
    let mut stack = vec![0];
    let mut ckd = vec![false; n];
    ckd[0] = true;
    while let Some(x) = stack.pop() {
        for &y in &g[x] {
            if !mem::replace(&mut ckd[y], true) {
                stack.push(y);
            }
        }
    }
    ckd.iter().all(|&b| b)
}
