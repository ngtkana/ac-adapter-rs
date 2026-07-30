//! 二部マッチング (Hopcroft-Karp)
//!
//! # 使い方
//!
//! 関数 [`bipartite_matching`] の doc を読んでください。

use std::{collections::VecDeque, mem::replace};

/// 二部マッチング (Hopcroft-Karp)
///
/// # 入力
///
/// 入力は有向二部グラフ $G = (V, E)$ (i.e. $\mathrm{src}(E) \cap \mathrm{tar}(E) = \empty$ な二部グラフ) つまり
///
/// * $L = \mathrm{src}(E), \\ R = \mathrm{tar}(E)$ と捉えるとよいです
/// * 分解 $V = L \sqcup R$ が明示的に与えられていない & 番号空間が共有 (i.e. 番号が被ったらダメ) な入力形式です。
/// * そう捉えると辺は $L → R$ の向きです。(まあ全部逆と捉えてもいいんですけどね)
///
/// このとき、入力の `g` は隣接リスト $g: R → \mathcal{P}(L)$ です。
///
///
/// # 出力
///
/// 出力の `f` は、(`g` と逆向きの)マッチング関数 $L: R → L$ (ただし存在しない場合は [`usize::MAX`])
///
///
/// # 例
///
/// Wikipedia にあった次のグラフを例にします。（結果は異なります。）
///
/// <div style="text-align:center">
/// <figure>
/// <img height=300 src="https://upload.wikimedia.org/wikipedia/commons/e/ee/HopcroftKarpExample.png">
/// </figure>
/// </div>
///
/// ```
/// # use bipartite_matching::bipartite_matching;
/// // 二部グラフ: $L = \\{0, 1\\}$, $R = \\{2\\}$
/// // エッジ: $0 \to 2$, $1 \to 2$
/// let g = [
///     vec![5, 6],
///     vec![9],
///     vec![7, 8],
///     vec![5, 9],
///     vec![6, 8],
///     vec![],
///     vec![],
///     vec![],
///     vec![],
///     vec![],
/// ];
///
/// let result = bipartite_matching(&g);
/// let expected = [
///     usize::MAX,
///     usize::MAX,
///     usize::MAX,
///     usize::MAX,
///     usize::MAX,
///     3,
///     0,
///     2,
///     4,
///     1,
/// ];
///
/// assert_eq!(result, expected);
/// ```
pub fn bipartite_matching(g: &[Vec<usize>]) -> Vec<usize> {
    let n = g.len();
    let mut queue = VecDeque::new();
    let mut f = vec![usize::MAX; n];
    let mut label = vec![usize::MAX; n];
    for x in (0..n).filter(|&i| !g[i].is_empty()) {
        queue.push_back(x);
        label[x] = 0;
    }
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
        for x in 0..n {
            if label[x] == 0 && !primal(x, &mut label, g, &mut f) {
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

/// 左頂点 $x$ から増加経路を DFS で探索
///
/// ラベル値を利用した「現在エッジ」構造：探索済みノードの再訪問を防ぐ。
fn primal(x: usize, label: &mut [usize], g: &[Vec<usize>], f: &mut [usize]) -> bool {
    let d = replace(&mut label[x], usize::MAX);
    for &y in &g[x] {
        if d + 1 == label[y] {
            let z = f[y];
            if z == usize::MAX || (d + 2 == label[z] && primal(z, label, g, f)) {
                f[y] = x;
                return true;
            }
        }
    }
    false
}
