//! Hopcroft-Karp 法による二部マッチング
//!
//! BFS で全頂点から最短増加パス長を求め、その長さちょうどのパスだけを DFS でまとめて
//! マッチングに繰り込む。1 フェーズで最短増加パスを使い切るため、フェーズ数が
//! $O(\sqrt{V})$ に抑えられ、全体で $O(E \sqrt{V})$ を達成する。
//!
//! # 仕様
//!
//! 有向二部グラフ $G = (V, E)$（$\mathrm{src}(E) \cap \mathrm{tar}(E) = \emptyset$）を扱う。
//! $L = \mathrm{src}(E)$、$R = \mathrm{tar}(E)$ とすると辺は $L \to R$ の向き。
//! $L$、$R$ の分解は明示せず、番号空間を共有する形式で入力する（番号の重複不可）。
//!
//! - [`bipartite_matching`]: 隣接リスト $g: R \to \mathcal{P}(L)$ を受け取り、
//!   最大濃度マッチングに対応する $f: R \to L$（マッチしない場合は [`usize::MAX`]）を返す
//!
//! # 計算量
//!
//! - [`bipartite_matching`]: $O(E \sqrt{V})$（$V = |L| + |R|$、$E$: 辺数）

use std::{collections::VecDeque, mem::replace};

/// Hopcroft-Karp 法で二部グラフの最大濃度マッチングを求める。
///
/// 入力 `g` は隣接リスト $g: R \to \mathcal{P}(L)$。出力 `f` は `g` と逆向きの
/// マッチング関数 $f: R \to L$（マッチしない添字は [`usize::MAX`]）。
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
