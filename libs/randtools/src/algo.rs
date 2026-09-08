use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::iter;

/// Prüfer 列 `prufer` から $n = |{\tt prufer}| + 2$ 頂点の木を復元する（隣接リスト形式）。
///
/// 末尾に $n - 1$ を加えた列の各頂点の出現回数から次数を求め、次数 1（葉）になった頂点を
/// 番号の小さい順に取り出しながら列の要素と結んでいく標準的な復元アルゴリズム。取り出した
/// 頂点の次数が 0 になれば、その頂点も新たな葉として扱う。
///
/// # 仕様
///
/// - 入力: 長さ $n - 2$ の列 `prufer`（各要素は $[0, n)$）
/// - 出力: $n$ 頂点・辺数 $n - 1$ の木を表す隣接リスト
///
/// # 計算量
///
/// $O(n \log n)$
pub fn prufer2tree(prufer: &[usize]) -> Vec<Vec<usize>> {
    let n = prufer.len() + 2;
    assert!(prufer.iter().all(|&x| x < n));

    let prufer_y = prufer
        .iter()
        .copied()
        .chain(iter::once(n - 1))
        .collect::<Vec<_>>();
    let mut m = vec![0; n];
    for &y in &prufer_y {
        m[y] += 1;
    }

    let mut heap = m
        .iter()
        .enumerate()
        .filter(|&(_, &x)| x == 0)
        .map(|(i, _)| Reverse(i))
        .collect::<BinaryHeap<_>>();
    let mut prufer_x = Vec::new();
    for &y in &prufer_y {
        prufer_x.push(heap.pop().unwrap().0);
        m[y] -= 1;
        if m[y] == 0 {
            heap.push(Reverse(y));
        }
    }

    let mut g = vec![Vec::new(); n];
    prufer_x.iter().zip(prufer_y.iter()).for_each(|(&x, &y)| {
        g[x].push(y);
        g[y].push(x);
    });
    g
}
