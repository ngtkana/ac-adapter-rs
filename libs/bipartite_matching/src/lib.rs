//! Hopcroft-Karp アルゴリズムによる二部グラフの最大マッチング
//!
//! # 仕様
//!
//! 有向グラフ $G = (V, E)$ が与えられたとき、$L = \\{ x \in V \mid \exists y \in V: (x, y) \in E \\}$ とし、
//! 二部グラフ $(L, R, E)$ （$R = V \setminus L$）における**最大マッチング** $M \subseteq E$ を求める。
//!
//! マッチング $M$ は以下を満たす：
//! - $M$ の各エッジは頂点を共有しない（独立エッジ集合）
//! - 任意のエッジ $e \in E \setminus M$ に対し、$e$ を $M$ に追加すると独立エッジ集合でなくなる
//!
//! # 入出力
//!
//! - **入力**: グラフ $g: L \to \mathcal{P}(R)$ （隣接リスト表現）
//!   - $g(i) = \\{ j : (i, j) \in E \\}$ （$i \in L$）
//! - **出力**: 関数 $f: R \to L \cup \\{\infty\\}$ （マッチング $M = \\{ (f(j), j) : f(j) \neq \infty \\}$）
//!   - $f(j) = i$ なら $(i, j) \in M$
//!   - $f(j) = \infty$ なら $j$ はマッチされていない
//!
//! # 例
//!
//! ```
//! # use bipartite_matching::bipartite_matching;
//! let g = vec![vec![2], vec![2], vec![]];  // $L = \\{0, 1\\}$, $R = \\{2\\}$
//! let f = bipartite_matching(&g);
//! // 最大マッチング: $0 \to 2$ （$f(2) = 0$）
//! assert_eq!(f[2], 0);
//! ```
//!
//! # 計算量
//!
//! $O(\sqrt{V} \cdot E)$ （$V$ = ノード数、$E$ = エッジ数）

use std::{collections::VecDeque, mem::replace};

/// 二部グラフの最大マッチングを求める
///
/// Hopcroft-Karp アルゴリズムにより $O(\sqrt{V} \cdot E)$ で計算。
///
/// # 入力
/// - `g`: グラフの隣接リスト。$g(i)$ = 左頂点 $i$ から到達可能な右側頂点集合
///
/// # 出力
/// マッチング関数 $f: R \to L \cup \\{\infty\\}$
/// - $f(j) = i$ ($i \neq \infty$) ⟹ 左頂点 $i$ が右頂点 $j$ とマッチング
/// - $f(j) = \infty$ ⟹ 右頂点 $j$ はマッチされていない
///
/// # 例
/// ```
/// # use bipartite_matching::bipartite_matching;
/// // 二部グラフ: $L = \\{0, 1\\}$, $R = \\{2\\}$
/// // エッジ: $0 \to 2$, $1 \to 2$
/// let g = vec![vec![2], vec![2], vec![]];
/// let f = bipartite_matching(&g);
/// // マッチング: $0 \to 2$ （$f(2) = 0$）
/// assert_eq!(f[2], 0);
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
