//! Re-rooted tree DP.
//!
//! * **NOTE: The parent will automatically be removed.**(already removed is also OK)
//!
//! # Notation
//!
//! * $G = (V, E; \ r)$ is a tree.
//! * $G _ x$ is the set of **children** of $x$.
//! * $P _ x$ is the parent of $x$ (undefined if $x = r$).
//!
//! | Math | Rust | Description |
//! |------|------|-------------|
//! | $r$ | `root` | The root of the tree |
//! | $X$ | [`Op::Value`] | DP value |
//! | $A$ | [`Op::Acc`], [`Op::identity()`], [`Op::mul()`] | the monoid of converted values |
//! | $W$ | [`Op::VertexWeight`] | vertex weight (usually be `()`) |
//! | $f: X \to A$ | [`Op::f()`] | Conversion |
//! | $g ^ w: A \to X \ (w \in W)$ | [`Op::g()`] | Conversion |
//!
//! # Usual tree DP
//!
//! $\mathrm{dp}$ is the recursively defined values of the **subtree** rooted at $x$. $\mathrm{ep}$ is the converted values of them.
//!
//! $$
//! \begin{aligned}
//! \mathrm{dp} _ x &= g ^ { W _ x } \left( \prod _ { y \in G _ x } \mathrm{ep} _ y \right) \in X \\\\
//! \mathrm{ep} _ x &= f \left(\mathrm{dp} _ x\right) \in A
//! \end{aligned}
//! $$
//!
//! # Re-rooted tree DP
//!
//! Let $\mathrm{dp}'(x)$ be the result on the tree rooted at $x$, and **with the strict subtree of $x$ removed**.
//!
//! $\mathrm{fp}$ is the converted values of the **parent** (if none, $1 \in A$) ($y \in G _ x$):
//!
//! $$
//! \mathrm{fp}(y) =
//! \begin{cases}
//! 1 & \text{if $y = r$} \\\\
//! f\left(\mathrm{dp}'(x)\right) \in A & \text{otherwise}
//! \end{cases}
//! \in A
//! $$
//!
//! This is computed according to the following recursive formula ($y \in G _ x$):
//!
//! $$
//! \mathrm{fp}(y) =
//! \begin{cases}
//! 1 & \text{if $y = r$} \\\\
//! \left ( f \circ g ^ { W _ x } \right ) \left (
//!     \mathrm{fp}(x) \cdot \prod _ { y' \in G _ x \setminus \\{y\\} } \mathrm{ep}(y')
//! \right ) & \text{otherwise}
//! \end{cases}
//! \in A
//! $$
//!
//! $\mathrm{gp}$ is the value of the total tree **re-rooted at $x$**:
//!
//! $$
//! \mathrm{gp}(x) = g ^ { W _ x } \left(\prod_{y \in G _ x \cup P _ x} \mathrm{ep}(y) \right) \in X
//! $$
//!
//! This is computed according to the following recursive formula:
//!
//! $$
//! \mathrm{gp}(x) = g ^ { W _ x } \left( \mathrm{fp}(x) \cdot \left( \prod _ { y \in G _ x } \mathrm{ep}(y) \right) \right) \in X
//! $$

/// An operation for re-rooted tree DP.
pub trait Op {
    /// $X$: The type of the DP value.
    type Value: Default + Copy;

    /// $A$: The type of the monoid of converted values.
    type Acc: Default + Copy;

    /// $W$: The type of the vertex weight.
    type VertexWeight: Copy;

    /// $1 \in A$: The identity element of the monoid of converted values.
    fn identity() -> Self::Acc;

    /// $a \cdot b$: The operation of the monoid of converted values.
    fn mul(lhs: Self::Acc, rhs: Self::Acc) -> Self::Acc;

    /// $f: X \to A$: Conversion.
    fn f(value: Self::Value) -> Self::Acc;

    /// $g ^ w: A \to X \ (w \in W)$: Conversion.
    fn g(acc: Self::Acc, vertex_weight: Self::VertexWeight) -> Self::Value;
}

/// Given a tree $G = (V, E; \ r)$ and vertex weights $W$, returns the four DP arrays: $\mathrm{dp}$, $\mathrm{ep}$, $\mathrm{fp}$, and $\mathrm{gp}$.
#[allow(clippy::type_complexity)]
pub fn rerooted_tree_dp<O: Op>(
    root: usize,
    g: &mut [Vec<usize>],
    vertex_weights: &[O::VertexWeight],
) -> (Vec<O::Value>, Vec<O::Acc>, Vec<O::Acc>, Vec<O::Value>) {
    let n = g.len();
    let mut parent = vec![!0; n];
    let mut stack = vec![root];
    let mut sorted = vec![];
    while let Some(u) = stack.pop() {
        sorted.push(u);
        g[u].retain(|&v| v != parent[u]);
        for &v in &g[u] {
            parent[v] = u;
            stack.push(v);
        }
    }
    let mut dp = vec![O::Value::default(); n];
    let mut ep = vec![O::Acc::default(); n];
    for &i in sorted.iter().rev() {
        let mut acc = O::identity();
        for &j in &g[i] {
            acc = O::mul(acc, ep[j]);
        }
        dp[i] = O::g(acc, vertex_weights[i]);
        ep[i] = O::f(dp[i]);
    }
    let mut fp = vec![O::Acc::default(); n];
    let mut gp = vec![O::Value::default(); n];
    for &x in &sorted {
        let mut prefix = vec![O::identity(); g[x].len() + 1];
        for (i, &y) in g[x].iter().enumerate() {
            prefix[i + 1] = O::mul(prefix[i], ep[y]);
        }
        let mut suffix = vec![O::identity(); g[x].len() + 1];
        for (i, &y) in g[x].iter().enumerate().rev() {
            suffix[i] = O::mul(suffix[i + 1], ep[y]);
        }
        for (i, &y) in g[x].iter().enumerate() {
            let mut acc = O::identity();
            acc = O::mul(acc, prefix[i]);
            acc = O::mul(acc, suffix[i + 1]);
            acc = O::mul(acc, fp[x]);
            fp[y] = O::f(O::g(acc, vertex_weights[x]));
        }
        let mut acc = fp[x];
        acc = O::mul(acc, prefix[g[x].len()]);
        gp[x] = O::g(acc, vertex_weights[x]);
    }
    (dp, ep, fp, gp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn naive<O: Op>(
        root: usize,
        g: &mut [Vec<usize>],
        vertex_weights: &[O::VertexWeight],
    ) -> O::Value {
        let mut dp = vec![O::Value::default(); g.len()];
        let mut parent = vec![!0; g.len()];
        let mut stack = vec![root];
        let mut sorted = vec![];
        while let Some(u) = stack.pop() {
            sorted.push(u);
            g[u].retain(|&v| v != parent[u]);
            for &v in &g[u] {
                parent[v] = u;
                stack.push(v);
            }
        }
        for &i in sorted.iter().rev() {
            let mut acc = O::identity();
            for &j in &g[i] {
                acc = O::mul(acc, O::f(dp[j]));
            }
            dp[i] = O::g(acc, vertex_weights[i]);
        }
        dp[root]
    }

    #[test]
    fn test_size() {
        enum O {}
        impl Op for O {
            type Acc = usize;
            type Value = usize;
            type VertexWeight = ();

            fn identity() -> Self::Acc {
                0
            }

            fn mul(lhs: Self::Acc, rhs: Self::Acc) -> Self::Acc {
                lhs + rhs
            }

            fn f(value: Self::Value) -> Self::Acc {
                value
            }

            fn g(acc: Self::Acc, (): Self::VertexWeight) -> Self::Value {
                acc + 1
            }
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=50);
            let g = random_graph(&mut rng, n);
            let root = rng.gen_range(0..n);
            let (dp, ep, fp, gp) = rerooted_tree_dp::<O>(root, &mut g.clone(), &vec![(); n]);
            assert_eq!(dp.len(), n);
            assert_eq!(ep.len(), n);
            assert_eq!(fp.len(), n);
            assert_eq!(gp.len(), n);
            for i in 0..n {
                assert_eq!(dp[i], ep[i]);
                assert_eq!(dp[i] + fp[i], n);
                assert_eq!(gp[i], n);
            }
        }
    }

    #[test]
    fn test_bit_or() {
        enum O {}
        impl Op for O {
            type Acc = u64;
            type Value = u64;
            type VertexWeight = u64;

            fn identity() -> Self::Acc {
                0
            }

            fn mul(lhs: Self::Acc, rhs: Self::Acc) -> Self::Acc {
                lhs | rhs
            }

            fn f(value: Self::Value) -> Self::Acc {
                value ^ 1
            }

            fn g(acc: Self::Acc, vertex_weight: Self::VertexWeight) -> Self::Value {
                acc ^ vertex_weight
            }
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..=50);
            let g = random_graph(&mut rng, n);
            let a = (0..n)
                .map(|_| rng.gen_range(0..=u64::MAX))
                .collect::<Vec<_>>();
            let root = rng.gen_range(0..n);
            let (dp, ep, _fp, gp) = rerooted_tree_dp::<O>(root, &mut g.clone(), &a);
            assert_eq!(dp[root], gp[root]);
            for i in 0..n {
                assert_eq!(dp[i] ^ 1, ep[i]);
                assert_eq!(gp[i], naive::<O>(i, &mut g.clone(), &a));
            }
        }
    }

    fn random_graph(rng: &mut StdRng, n: usize) -> Vec<Vec<usize>> {
        let g = if n == 1 {
            vec![vec![]]
        } else {
            prufer_to_graph(&(0..n - 2).map(|_| rng.gen_range(0..n)).collect::<Vec<_>>())
        };
        validate_tree(&g);
        g
    }

    fn prufer_to_graph(prufer: &[usize]) -> Vec<Vec<usize>> {
        let n = prufer.len() + 2;
        let mut prufer_x = Vec::new();
        let mut g = vec![vec![]; n];
        for i in 0..n - 1 {
            let x = (0..n)
                .find(|&x| !prufer_x.contains(&x) && !prufer[i..].contains(&x))
                .unwrap();
            let y = if i == n - 2 { n - 1 } else { prufer[i] };
            prufer_x.push(x);
            g[x].push(y);
            g[y].push(x);
        }
        g
    }

    fn validate_tree(g: &[Vec<usize>]) {
        let n = g.len();
        assert!(g.iter().flatten().all(|&v| v < n));
        assert_eq!(g.iter().map(Vec::len).sum::<usize>(), 2 * (n - 1));
        let mut visited = vec![false; n];
        let mut stack = vec![0];
        while let Some(u) = stack.pop() {
            assert!(!visited[u]);
            visited[u] = true;
            for &v in &g[u] {
                if !visited[v] {
                    stack.push(v);
                }
            }
        }
        assert!(visited.iter().all(|&b| b));
    }
}
