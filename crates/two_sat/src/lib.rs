//! 2-SAT を解きます。
//!
//! # 依存ライブラリ
//!
//! - `scc`
//!
//!
//! # Examples
//!
//! ```
//! # use two_sat::TwoSat;
//! let mut two_sat = TwoSat::new();
//!
//! two_sat.implies(0, true, 1, true);
//! two_sat.implies(1, true, 2, true);
//! two_sat.implies(2, true, 0, false);
//! two_sat.implies(2, true, 1, false);
//!
//! // Debug がきれいです。
//! assert_eq!("[0→1, 1→2, 2→¬0, 2→¬1]", format!("{:?}", &two_sat).as_str());
//!
//! // 解きます。
//! assert_eq!(Some(vec![false, false, true]), two_sat.solve(3));
//! ```

use {
    scc::scc_flatgraph,
    std::{cmp::Ordering, fmt::Debug},
};

/// 2-SAT の本体です。
#[derive(Clone, Default, Hash, PartialEq)]
pub struct TwoSat {
    edges: Vec<[usize; 2]>,
}
impl TwoSat {
    /// Always true を作ります。
    pub fn new() -> Self {
        Self::default()
    }
    /// `(x == a) -> (y == b)` をかつでつなぎます。
    pub fn implies(&mut self, x: usize, a: bool, y: usize, b: bool) {
        let x = 2 * x + a as usize;
        let y = 2 * y + b as usize;
        self.edges.push([x, y]);
        self.edges.push([y ^ 1, x ^ 1]);
    }
    /// 充足する割り当てがあれば返し、なければ `None` を返します。
    pub fn solve(&self, n: usize) -> Option<Vec<bool>> {
        let scc = scc_flatgraph(n * 2, &mut self.edges.clone());
        scc.cmp_of
            .chunks(2)
            .map(|v| match v[0].cmp(&v[1]) {
                Ordering::Less => Some(true),
                Ordering::Equal => None,
                Ordering::Greater => Some(false),
            })
            .collect()
    }
}
impl Debug for TwoSat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(
                self.edges
                    .chunks(2)
                    .map(|chunk| chunk[0])
                    .map(|[x, y]| DebugImplication { x, y }),
            )
            .finish()
    }
}
struct DebugImplication {
    x: usize,
    y: usize,
}
impl Debug for DebugImplication {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}{}→{}{}",
            "¬".repeat(1 - self.x % 2),
            self.x / 2,
            "¬".repeat(1 - self.y % 2),
            self.y / 2
        )
    }
}

#[cfg(test)]
mod tests {
    use {
        super::TwoSat,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::iter::repeat_with,
    };

    #[test]
    fn test_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..60 {
            let n = rng.gen_range(1..=20);
            let m = rng.gen_range(1..=20);
            let implications = repeat_with(|| {
                (
                    rng.gen_range(0..n),
                    rng.gen_ratio(1, 2),
                    rng.gen_range(0..n),
                    rng.gen_ratio(1, 2),
                )
            })
            .take(m)
            .collect::<Vec<_>>();

            let mut two_sat = TwoSat::new();
            implications
                .iter()
                .for_each(|&(x, a, y, b)| two_sat.implies(x, a, y, b));
            let result = two_sat.solve(n);

            if let Some(result) = result {
                assert!(feasible(&result, &implications));
            } else {
                assert!((0..1 << n).all(|bs| {
                    !feasible(
                        &(0..n).map(|i| bs >> i & 1 == 1).collect::<Vec<_>>(),
                        &implications,
                    )
                }));
            }
        }
    }

    fn feasible(result: &[bool], implications: &[(usize, bool, usize, bool)]) -> bool {
        implications
            .iter()
            .all(|&(x, a, y, b)| (result[x] != a) || (result[y] == b))
    }
}
