//! Monotone minima のアルゴリズムと、それによる tropical convolutions を提供します。
//!
//! # 問題例
//!
//! - [ABC 218 H - Red and Blue Lamps](https://atcoder.jp/contests/abc218/tasks/abc218_h)
use std::cmp::Ordering;
use std::cmp::Reverse;
use std::ops::Add;

////////////////////////////////////////////////////////////////////////////////
// Monotone minima
////////////////////////////////////////////////////////////////////////////////
/// 行ごとのセル比較 `cmp(i, j, k)` を受け取って、monotone minima をします。
pub fn monotone_minima_by(
    h: usize,                                                    // a.len()
    w: usize,                                                    // a[0].len()
    mut cmp: impl FnMut(usize, usize, usize) -> Ordering + Copy, // a[i][j].cmp(&a[i][k])
) -> Vec<usize> {
    assert!(0 < w);
    let mut ans = vec![0; h];
    ans[0] = (0..w).rev().min_by(|&j, &k| cmp(0, j, k)).unwrap();
    for d in (0..h.next_power_of_two().trailing_zeros() as usize)
        .rev()
        .map(|d| 1 << d)
    {
        for i in (d..h).step_by(2 * d) {
            let start = ans[i - d];
            let end = ans.get(i + d).copied().unwrap_or(w - 1);
            ans[i] = (start..=end).rev().min_by(|&j, &k| cmp(i, j, k)).unwrap();
        }
    }
    ans
}

/// 行ごとのセル比較 `cmp(i, j, k)` を受け取って、monotone maxima をします。
pub fn monotone_maxima_by(
    h: usize,                                                    // a.len()
    w: usize,                                                    // a[0].len()
    mut cmp: impl FnMut(usize, usize, usize) -> Ordering + Copy, // a[i][j].cmp(&a[i][k])
) -> Vec<usize> {
    monotone_minima_by(h, w, move |i, j, k| cmp(i, k, j))
}

/// 行列 `f(i, j)` を受け取って、monotone minima をします。
pub fn monotone_minima<T: Ord>(h: usize, w: usize, f: impl Fn(usize, usize) -> T) -> Vec<usize> {
    monotone_minima_by(h, w, |i, j, k| f(i, j).cmp(&f(i, k)))
}

/// 行列 `f(i, j)` を受け取って、monotone maxima をします。
pub fn monotone_maxima<T: Ord>(h: usize, w: usize, f: impl Fn(usize, usize) -> T) -> Vec<usize> {
    monotone_maxima_by(h, w, |i, j, k| f(i, j).cmp(&f(i, k)))
}

////////////////////////////////////////////////////////////////////////////////
// Convolution
////////////////////////////////////////////////////////////////////////////////
/// convex な列に対して min-plus convolution を計算します。
pub fn convex_minplus_convolution<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Copy + Ord + Add<Output = T>,
{
    if a.is_empty() && b.is_empty() {
        return Vec::new();
    }
    monotone_maxima(a.len() + b.len() - 1, a.len(), move |i, j| {
        i.checked_sub(j)
            .and_then(|ij| b.get(ij))
            .map(|&y| Reverse(a[j] + y))
    })
    .into_iter()
    .enumerate()
    .map(|(i, j)| a[j] + b[i - j])
    .collect()
}

/// concave な列に対して max-plus convolution を計算します。
pub fn concave_maxplus_convolution<T>(a: &[T], b: &[T]) -> Vec<T>
where
    T: Copy + Ord + Add<Output = T>,
{
    if a.is_empty() && b.is_empty() {
        return Vec::new();
    }
    monotone_maxima(a.len() + b.len() - 1, a.len(), move |i, j| {
        i.checked_sub(j).and_then(|ij| b.get(ij)).map(|&y| a[j] + y)
    })
    .into_iter()
    .enumerate()
    .map(|(i, j)| a[j] + b[i - j])
    .collect()
}

#[cfg(test)]
mod tests {
    use super::concave_maxplus_convolution;
    use super::convex_minplus_convolution;
    use super::monotone_minima;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::iter::once;
    use std::iter::repeat_with;

    ////////////////////////////////////////////////////////////////////////////////
    // Monotone minima
    ////////////////////////////////////////////////////////////////////////////////
    // generated by https://kmyk.github.io/monotone-matrix-visualizer/
    const MONOTONE_0: [[u32; 18]; 9] = [
        [
            91, 3, 72, 36, 42, 90, 15, 71, 68, 51, 22, 20, 38, 7, 98, 54, 67, 37,
        ],
        [
            36, 49, 68, 72, 60, 0, 55, 39, 46, 64, 59, 99, 74, 10, 90, 94, 79, 33,
        ],
        [
            97, 72, 52, 15, 4, 73, 89, 68, 34, 78, 42, 0, 78, 33, 14, 21, 48, 7,
        ],
        [
            76, 29, 30, 47, 47, 83, 69, 88, 93, 74, 71, 6, 90, 63, 69, 76, 66, 85,
        ],
        [
            68, 63, 6, 64, 42, 69, 19, 9, 63, 17, 13, 19, 3, 28, 91, 35, 62, 17,
        ],
        [
            15, 50, 18, 41, 11, 78, 69, 31, 9, 97, 72, 99, 8, 63, 84, 43, 89, 62,
        ],
        [
            75, 74, 58, 34, 59, 29, 54, 64, 17, 54, 77, 17, 85, 86, 2, 63, 64, 86,
        ],
        [
            71, 3, 30, 25, 13, 67, 34, 13, 36, 53, 54, 33, 45, 70, 2, 21, 94, 9,
        ],
        [
            43, 81, 29, 10, 17, 16, 74, 13, 24, 37, 46, 55, 39, 48, 2, 35, 51, 85,
        ],
    ];
    const MONOTONE_1: [[u32; 18]; 9] = [
        [
            0, 1, 74, 3, 88, 84, 51, 10, 4, 95, 55, 78, 56, 60, 89, 56, 90, 17,
        ],
        [
            8, 16, 9, 16, 54, 26, 32, 31, 68, 18, 93, 77, 55, 59, 81, 17, 39, 38,
        ],
        [
            83, 0, 46, 45, 45, 81, 97, 81, 90, 71, 77, 56, 36, 29, 61, 62, 53, 83,
        ],
        [
            64, 7, 33, 34, 76, 29, 35, 90, 19, 30, 40, 99, 96, 17, 91, 86, 84, 26,
        ],
        [
            8, 50, 0, 37, 9, 7, 69, 29, 96, 16, 94, 71, 87, 65, 72, 54, 10, 28,
        ],
        [
            49, 57, 3, 87, 78, 87, 60, 87, 45, 25, 48, 72, 6, 56, 88, 71, 80, 75,
        ],
        [
            27, 62, 10, 77, 92, 16, 58, 14, 8, 84, 46, 40, 15, 88, 52, 90, 85, 59,
        ],
        [
            91, 89, 19, 33, 29, 5, 94, 29, 11, 3, 58, 39, 53, 96, 48, 76, 88, 85,
        ],
        [
            14, 56, 27, 93, 57, 30, 27, 63, 48, 65, 35, 94, 22, 97, 10, 48, 22, 50,
        ],
    ];
    const MONOTONE_2: [[u32; 18]; 9] = [
        [
            3, 43, 10, 17, 10, 5, 24, 90, 58, 10, 24, 47, 70, 32, 13, 81, 81, 61,
        ],
        [
            52, 30, 12, 76, 59, 65, 38, 22, 81, 57, 36, 15, 13, 22, 15, 73, 16, 17,
        ],
        [
            21, 88, 47, 56, 88, 0, 52, 16, 84, 20, 36, 77, 3, 6, 86, 17, 86, 29,
        ],
        [
            40, 99, 43, 93, 49, 59, 14, 81, 62, 97, 99, 89, 51, 79, 44, 56, 69, 85,
        ],
        [
            41, 47, 60, 92, 59, 94, 3, 40, 5, 96, 37, 76, 94, 81, 56, 26, 91, 18,
        ],
        [
            56, 44, 19, 2, 84, 36, 0, 74, 88, 3, 23, 26, 81, 37, 78, 33, 31, 44,
        ],
        [
            92, 89, 23, 18, 86, 30, 90, 33, 67, 3, 35, 89, 81, 34, 63, 86, 41, 8,
        ],
        [
            74, 66, 10, 24, 79, 24, 65, 97, 63, 29, 96, 77, 7, 82, 43, 25, 77, 82,
        ],
        [
            17, 48, 54, 45, 94, 56, 88, 18, 10, 60, 7, 78, 93, 4, 61, 93, 93, 19,
        ],
    ];

    fn minima_brute(a: &[[u32; 18]; 9]) -> Vec<usize> {
        a.iter()
            .map(|v| (0..v.len()).rev().min_by_key(|&j| v[j]).unwrap())
            .collect()
    }

    #[test]
    fn test_monotone_minima_by() {
        let a = MONOTONE_0;
        let result = monotone_minima(9, 18, |i, j| a[i][j]);
        let expected = minima_brute(&a);
        assert_eq!(result, expected);

        let a = MONOTONE_1;
        let result = monotone_minima(9, 18, |i, j| a[i][j]);
        let expected = minima_brute(&a);
        assert_eq!(result, expected);

        let a = MONOTONE_2;
        let result = monotone_minima(9, 18, |i, j| a[i][j]);
        let expected = minima_brute(&a);
        assert_eq!(result, expected);
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Convex min-plus convolution
    ////////////////////////////////////////////////////////////////////////////////
    fn generate_convex_sequence(rng: &mut StdRng, n: usize) -> Vec<i32> {
        assert!(2 <= n);
        let mut ans = repeat_with(|| rng.gen_range(0..=10))
            .take(n - 2)
            .collect::<Vec<_>>();
        ans = once(0)
            .chain(ans)
            .scan(0, |state, x| {
                *state += x;
                Some(*state)
            })
            .collect();
        let d = ans.last().unwrap() - ans.first().unwrap();
        let init = rng.gen_range(-d..=0);
        ans.iter_mut().for_each(|x| *x += init);
        ans = once(0)
            .chain(ans)
            .scan(0, |state, x| {
                *state += x;
                Some(*state)
            })
            .collect();
        let init = -ans.iter().copied().min().unwrap();
        ans.iter_mut().for_each(|x| *x += init);
        let init =
            rng.gen_range(ans.iter().copied().min().unwrap()..=ans.iter().copied().max().unwrap());
        ans.iter_mut().for_each(|x| *x += init);
        ans
    }

    fn minplus_convolution_brute(a: &[i32], b: &[i32]) -> Vec<i32> {
        let mut c = vec![i32::MAX; a.len() + b.len() - 1];
        for (i, &x) in a.iter().enumerate() {
            for (j, &y) in b.iter().enumerate() {
                c[i + j] = c[i + j].min(x + y);
            }
        }
        c
    }

    #[test]
    fn test_convex_minplus_convolution() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(2..20);
            let a = generate_convex_sequence(&mut rng, n);
            let b = generate_convex_sequence(&mut rng, n);
            let result = convex_minplus_convolution(&a, &b);
            let expected = minplus_convolution_brute(&a, &b);
            assert_eq!(&result, &expected);
        }
    }

    ////////////////////////////////////////////////////////////////////////////////
    // Concave max-plus convolution
    ////////////////////////////////////////////////////////////////////////////////
    fn generate_concave_sequence(rng: &mut StdRng, n: usize) -> Vec<i32> {
        let mut ans = generate_convex_sequence(rng, n);
        let max = *ans.iter().max().unwrap();
        ans.iter_mut().for_each(|x| *x = max - *x);
        let init =
            rng.gen_range(ans.iter().copied().min().unwrap()..=ans.iter().copied().max().unwrap());
        ans.iter_mut().for_each(|x| *x += init);
        ans
    }

    fn maxplus_convolution_brute(a: &[i32], b: &[i32]) -> Vec<i32> {
        let mut c = vec![i32::MIN; a.len() + b.len() - 1];
        for (i, &x) in a.iter().enumerate() {
            for (j, &y) in b.iter().enumerate() {
                c[i + j] = c[i + j].max(x + y);
            }
        }
        c
    }

    #[test]
    fn test_concave_maxplus_convolution() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(2..20);
            let a = generate_concave_sequence(&mut rng, n);
            let b = generate_concave_sequence(&mut rng, n);
            let result = concave_maxplus_convolution(&a, &b);
            let expected = maxplus_convolution_brute(&a, &b);
            assert_eq!(&result, &expected);
        }
    }
}
