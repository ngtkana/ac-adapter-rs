//! 2次元平面上の点集合に対する凸包・最遠点対・凸性判定。
//!
//! 凸包は Andrew's monotone chain 法で構築する。座標を辞書順にソートし、下側包・
//! 上側包をそれぞれ [`ccw`] が非負（内側に折れる、または一直線上）になった点を
//! 弾きながら単調スタックで構築することで、凸多角形の頂点列だけが残る。
//! 最遠点対（直径）は必ず凸包の頂点同士であり、凸包を一周する間その対蹠点が
//! 単調に動くという性質（rotating calipers）を使い、全点対を調べずに求める。
//!
//! # 仕様
//!
//! 点は `[i64; 2]`（x, y 座標）で表す。
//!
//! - [`sqmag`][]: 2点間の距離の2乗 $|p_0 - p_1|^2$
//! - [`ccw`][]: 外積 $\det(p_1 - p_0,\ p_2 - p_0)$（符号で3点の向きを判定）
//! - [`convex_hull`][]: 点集合の凸包を、辞書順最小の頂点から時計回りに並べて返す
//! - [`caliper`][]: 点集合の最遠点対とその距離の2乗を返す（`a` は非空が前提）
//! - [`is_convex`][]: 点列が（時計回りの）凸多角形をなすか判定
//!
//! # 例
//!
//! ```
//! use convex_hull::convex_hull;
//! let points = [[0, 0], [2, 0], [2, 2], [0, 2], [1, 1]];
//! let hull = convex_hull(&points);
//! assert_eq!(hull.len(), 4); // 内部の点 [1, 1] は凸包に含まれない
//! ```
//!
//! # 計算量
//!
//! - [`convex_hull`][]: $O(n \log n)$（ソートが支配的）
//! - [`caliper`][]: $O(n \log n)$（内部で凸包を構築するため）
//! - [`is_convex`][]: $O(n)$

type Point = [i64; 2];

/// 2点間の距離の2乗 $|p_0 - p_1|^2$ を返す。
///
/// # 例
///
/// ```
/// use convex_hull::sqmag;
/// assert_eq!(sqmag([0, 0], [3, 4]), 25);
/// ```
pub fn sqmag(p0: Point, p1: Point) -> i64 {
    let [x0, y0] = p0;
    let [x1, y1] = p1;
    let dx = x0 - x1;
    let dy = y0 - y1;
    dx * dx + dy * dy
}

/// 外積 $\det(p_1 - p_0,\ p_2 - p_0)$ を返す。符号で3点 $p_0, p_1, p_2$ の向きが分かる：
/// 正なら反時計回り、負なら時計回り、0なら一直線上。
///
/// # 例
///
/// ```
/// use convex_hull::ccw;
/// assert!(ccw([0, 0], [1, 0], [1, 1]) > 0); // 反時計回り
/// assert!(ccw([0, 0], [1, 1], [1, 0]) < 0); // 時計回り
/// assert_eq!(ccw([0, 0], [1, 1], [2, 2]), 0); // 一直線上
/// ```
pub fn ccw(p0: Point, p1: Point, p2: Point) -> i64 {
    let [x0, y0] = p0;
    let [x1, y1] = p1;
    let [x2, y2] = p2;
    (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
}

// det(p1 - p0, p3 - p2) を求めます。
fn general_ccw(p0: Point, p1: Point, p2: Point, p3: Point) -> i64 {
    let [x0, y0] = p0;
    let [x1, y1] = p1;
    let [x2, y2] = p2;
    let [x3, y3] = p3;
    (x1 - x0) * (y3 - y2) - (x3 - x2) * (y1 - y0)
}

/// 点集合の凸包を、辞書順最小の頂点から時計回りに並べて返す。
///
/// # 仕様
///
/// - `a` が空なら空配列を返す
/// - `a` の要素数が1, 2のときはそのまま（重複除去のみ）返す
///
/// # 例
///
/// ```
/// use convex_hull::convex_hull;
/// let points = [[0, 0], [2, 0], [2, 2], [0, 2], [1, 1]];
/// let hull = convex_hull(&points);
/// assert_eq!(hull.len(), 4); // 内部の点 [1, 1] は凸包に含まれない
/// ```
///
/// # 計算量
///
/// $O(n \log n)$（ソートが支配的）
pub fn convex_hull(a: &[[i64; 2]]) -> Vec<[i64; 2]> {
    if a.is_empty() {
        Vec::new()
    } else if a.len() == 1 {
        vec![a[0]]
    } else if a.len() == 2 {
        if a[0] == a[1] {
            vec![a[0]]
        } else {
            vec![a[0], a[1]]
        }
    } else {
        let mut a = a.to_vec();
        a.sort_unstable();
        a.dedup();
        let mut hull = Vec::new();
        for &p in &a {
            while 2 <= hull.len() && 0 <= ccw(hull[hull.len() - 2], hull[hull.len() - 1], p) {
                hull.pop();
            }
            hull.push(p);
        }
        let mid_len = hull.len();
        for &p in a.iter().rev().skip(1) {
            while mid_len < hull.len() && 0 <= ccw(hull[hull.len() - 2], hull[hull.len() - 1], p) {
                hull.pop();
            }
            hull.push(p);
        }
        if hull.len() > 1 && hull.first() == hull.last() {
            hull.pop();
        }
        hull
    }
}

/// 点集合の最遠点対とその距離の2乗を返す（rotating calipers 法）。
///
/// # 仕様
///
/// 戻り値は `(距離の2乗, [点1, 点2])`。`a` は非空が前提（空なら panic）。
///
/// # 例
///
/// ```
/// use convex_hull::caliper;
/// let points = [[0, 0], [4, 0], [4, 3]];
/// let (d, _) = caliper(&points);
/// assert_eq!(d, 25); // [0, 0] と [4, 3] の距離の2乗 = 4^2 + 3^2
/// ```
///
/// # 計算量
///
/// $O(n \log n)$（内部で凸包を構築するため）
pub fn caliper(a: &[[i64; 2]]) -> (i64, [[i64; 2]; 2]) {
    assert!(!a.is_empty());
    let a = convex_hull(a);
    if a.len() == 1 {
        (0, [a[0], a[0]])
    } else if a.len() == 2 {
        (sqmag(a[0], a[1]), [a[0], a[1]])
    } else {
        let n = a.len();
        let mut d = 0;
        let mut ans_i = usize::MAX;
        let mut ans_j = usize::MAX;
        let min_position = (0..n).min_by_key(|&i| a[i][0]).unwrap();
        let max_position = (0..n).max_by_key(|&i| a[i][0]).unwrap();
        let start_i = min_position.min(max_position);
        let start_j = min_position.max(max_position);
        let mut i = start_i;
        let mut j = start_j;
        while i != start_i + n && j != start_j + n {
            if 0 < general_ccw(a[(i + 1) % n], a[i % n], a[(j + 1) % n], a[j % n]) {
                i += 1;
            } else {
                j += 1;
            }
            let e = sqmag(a[i % n], a[j % n]);
            if d < e {
                d = e;
                ans_i = i;
                ans_j = j;
            }
        }
        (d, [a[ans_i % n], a[ans_j % n]])
    }
}

/// 点列 `a` が（時計回りの）凸多角形をなすか判定する。
///
/// 隣接する3頂点すべてで [`ccw`] が負（時計回り）であることを確認する。
/// 頂点数が2以下の場合は常に true。
///
/// # 例
///
/// ```
/// use convex_hull::is_convex;
/// assert!(is_convex(&[[0, 0], [0, 1], [1, 1], [1, 0]])); // 時計回りの正方形
/// assert!(!is_convex(&[[0, 0], [1, 0], [1, 1], [0, 1]])); // 反時計回りなので false
/// ```
pub fn is_convex(a: &[[i64; 2]]) -> bool {
    let n = a.len();
    n <= 2 || (0..n).all(|i| ccw(a[i], a[(i + 1) % n], a[(i + 2) % n]) < 0)
}

#[cfg(test)]
mod tests {
    use super::caliper;
    use super::convex_hull;
    use super::is_convex;
    use super::sqmag;
    use rand::prelude::*;
    use std::iter;

    #[test]
    fn test_convex_hull_small() {
        test_convex_hull_base(4, 10, 2000);
    }

    #[test]
    fn test_convex_hull_middle() {
        test_convex_hull_base(100, 100, 100);
    }

    #[test]
    fn test_convex_hull_large() {
        test_convex_hull_base(1_000_000_000, 400, 20);
    }

    fn test_convex_hull_base(coord_max: i64, vertex_number: usize, iteration: u32) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iteration {
            let n = rng.gen_range(0..vertex_number);
            let a = iter::repeat_with(|| {
                [
                    rng.gen_range(-coord_max..=coord_max),
                    rng.gen_range(-coord_max..=coord_max),
                ]
            })
            .take(n)
            .collect::<Vec<_>>();

            println!("Point group size: {:?}", a.len());
            let result = convex_hull(&a);

            assert!(is_convex(&result));
        }
    }

    #[test]
    fn test_caliper_small() {
        test_caliper_base(4, 10, 2000);
    }

    #[test]
    fn test_caliper_middle() {
        test_caliper_base(100, 100, 100);
    }

    #[test]
    fn test_caliper_large() {
        test_caliper_base(1_000_000_000, 400, 20);
    }

    fn test_caliper_base(coord_max: i64, vertex_number: usize, iteration: u32) {
        fn brute(a: &[[i64; 2]]) -> i64 {
            a.iter()
                .copied()
                .flat_map(|p| a.iter().copied().map(move |q| [p, q]))
                .map(|[p, q]| sqmag(p, q))
                .max()
                .unwrap()
        }
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..iteration {
            let n = rng.gen_range(1..vertex_number);
            let a = iter::repeat_with(|| {
                [
                    rng.gen_range(-coord_max..=coord_max),
                    rng.gen_range(-coord_max..=coord_max),
                ]
            })
            .take(n)
            .collect::<Vec<_>>();

            println!("Point group: {:?}", &a);
            println!("Point group size: {:?}", a.len());
            let (d, [p, q]) = caliper(&a);
            assert_eq!(d, sqmag(p, q));
            assert_eq!(d, brute(&a));
        }
    }
}
