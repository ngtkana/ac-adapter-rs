type Point = [i64; 2];

/// |p0 - p1| ^ 2 を求めます。
pub fn sqmag(p0: Point, p1: Point) -> i64 {
    let [x0, y0] = p0;
    let [x1, y1] = p1;
    let dx = x0 - x1;
    let dy = y0 - y1;
    dx * dx + dy * dy
}

/// det(p1 - p0, p2 - p0) を求めます。
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

/// 凸包を求めます。
/// 具体的には、辞書順最小の頂点から始めて、時計回りの凸包を作ります。
/// a が空のときには空配列を返します。
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
        if hull.first().unwrap() == hull.first().unwrap() {
            hull.pop();
        }
        hull
    }
}

/// 凸包を求めます。
/// 具体的には、辞書順最小の頂点から始めて、時計回りの凸包を作ります。
/// a が空のときには空配列を返します。
#[allow(clippy::many_single_char_names)]
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
        let mut ans_i = std::usize::MAX;
        let mut ans_j = std::usize::MAX;
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

/// 凸であれば true を返します。
pub fn is_convex(a: &[[i64; 2]]) -> bool {
    a.len() <= 2 || (0..a.len() - 2).all(|i| ccw(a[i], a[i + 1], a[i + 2]) < 0)
}

#[cfg(test)]
mod tests {
    use {
        super::{caliper, convex_hull, is_convex, sqmag},
        rand::prelude::*,
        std::iter,
    };

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

    #[allow(clippy::many_single_char_names)]
    fn test_caliper_base(coord_max: i64, vertex_number: usize, iteration: u32) {
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

        fn brute(a: &[[i64; 2]]) -> i64 {
            a.iter()
                .copied().flat_map(|p| a.iter().copied().map(move |q| [p, q]))
                .map(|[p, q]| sqmag(p, q))
                .max()
                .unwrap()
        }
    }
}
