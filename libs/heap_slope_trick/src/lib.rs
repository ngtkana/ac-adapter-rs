//! [`BinaryHeap`] 二本で slope trick をします。
//!
//! [詳しくは `HeapSlopeTrick` をご覧ください。](HeapSlopeTrick)

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::mem::swap;

/// 足し算をします。
///
/// # TODO
///
/// テストを書きたいです。
///
/// # 計算量
///
/// O ( N lg N )、ただし N は a と b のうち大きい方長さ
pub fn merge(mut a: HeapSlopeTrick, mut b: HeapSlopeTrick) -> HeapSlopeTrick {
    if a.small.len() + a.large.len() < b.small.len() + b.large.len() {
        swap(&mut a, &mut b);
    }
    let HeapSlopeTrick {
        minimum,
        small,
        large,
        shift_small,
        shift_large,
    } = b;
    let a_shift_small = a.shift_small;
    let a_shift_large = a.shift_large;
    a.minimum += minimum;
    a.small
        .extend(small.into_iter().map(|x| x + shift_small - a_shift_small));
    a.large.extend(
        large
            .into_iter()
            .map(|Reverse(x)| Reverse(x + shift_large - a_shift_large)),
    );
    a
}

/// 本体です。
///
/// # Examples
///
/// ```
/// # use heap_slope_trick::HeapSlopeTrick;
/// // f(x) = 0
/// let mut slope = HeapSlopeTrick::new();
///
/// // f(x) <- f(x) + |x - 2|
/// slope.add_abs(2);
/// assert_eq!(slope.eval(0), 2);
/// assert_eq!(slope.eval(1), 1);
/// assert_eq!(slope.eval(2), 0);
/// assert_eq!(slope.eval(3), 1);
///
/// // f(x) <- min(f(x-2), f(x-1), f(x))
/// slope.sliding_window_minimum(0, 2);
/// assert_eq!(slope.eval(0), 2);
/// assert_eq!(slope.eval(1), 1);
/// assert_eq!(slope.eval(2), 0);
/// assert_eq!(slope.eval(3), 0);
/// assert_eq!(slope.eval(4), 0);
/// assert_eq!(slope.eval(5), 1);
/// ```
#[derive(Clone, Debug, Default)]
pub struct HeapSlopeTrick {
    minimum: i64,
    small: BinaryHeap<i64>,
    large: BinaryHeap<Reverse<i64>>,
    shift_small: i64,
    shift_large: i64,
}
impl HeapSlopeTrick {
    /// 零関数 f(x) = 0
    pub fn new() -> Self { Self::default() }

    /// 一点評価 f(x)
    pub fn eval(&self, x: i64) -> i64 {
        self.minimum
            + self
                .small
                .iter()
                .copied()
                .map(|small| (small + self.shift_small - x).max(0))
                .chain(
                    self.large
                        .iter()
                        .copied()
                        .map(|Reverse(large)| (x - large - self.shift_large).max(0)),
                )
                .sum::<i64>()
    }

    /// 最小値を取る x の集合（と [MIN, MAX] の交差）を取得 argmin { f(x) | x in ]-∞, ∞[ }
    pub fn get_argmin(&self) -> [i64; 2] {
        [
            self.small
                .peek()
                .map_or(std::i64::MIN, |&x| x + self.shift_small),
            self.large
                .peek()
                .map_or(std::i64::MAX, |&Reverse(x)| x + self.shift_large),
        ]
    }

    /// 最小値取得 min { f(x) | x in ]-∞, ∞[ }
    pub fn get_minimum(&self) -> i64 { self.minimum }

    /// 定数関数加算 g(x) = f(x) + c
    pub fn add_const(&mut self, c: i64) { self.minimum += c; }

    /// 傾き +1 のカットオフ一次関数加算 g(x) = f(x) + max(x - a, 0)
    pub fn add_cutoff_diagonal(&mut self, a: i64) {
        self.small.push(a - self.shift_small);
        self.large.push(Reverse(
            self.small.pop().unwrap() + self.shift_small - self.shift_large,
        ));
        self.minimum += (self.large.peek().unwrap().0 + self.shift_large - a).max(0);
    }

    /// 傾き -1 のカットオフ一次関数加算 g(x) = f(x) + max(a - x, 0)
    pub fn add_cutoff_anti_diagonal(&mut self, a: i64) {
        self.large.push(Reverse(a - self.shift_large));
        self.small
            .push(self.large.pop().unwrap().0 + self.shift_large - self.shift_small);
        self.minimum += (a - (self.small.peek().unwrap() + self.shift_small)).max(0);
    }

    /// 絶対値関数加算 g(x) = f(x) + |x - a|
    pub fn add_abs(&mut self, a: i64) {
        self.add_cutoff_diagonal(a);
        self.add_cutoff_anti_diagonal(a);
    }

    /// 左から累積最小値 g(x) = min { f(y) | y ∈ ]-∞, x] }
    pub fn cumulative_min_from_left(&mut self) { self.large.clear(); }

    /// 右から累積最小値 g(x) = min { f(y) | y ∈ [x, ∞[ }
    pub fn cumulative_min_from_right(&mut self) { self.small.clear(); }

    /// 平行移動 g(x) = f ( x - a )
    pub fn shift(&mut self, a: i64) {
        self.shift_small += a;
        self.shift_large += a;
    }

    /// スライド最小値 g(x) = min { f(y) |  y ∈ [x - b, x - a]  }
    pub fn sliding_window_minimum(&mut self, a: i64, b: i64) {
        assert!(a <= b);
        self.shift_small += a;
        self.shift_large += b;
    }

    /// 差分の最小値 min { f(x + 1) - f(x) | x ∈ ]-∞, ∞[ }
    pub fn get_tilt_minimum(&self) -> i64 { -(self.small.len() as i64) }

    /// 差分の最大値 max { f(x + 1) - f(x) | x ∈ ]-∞, ∞[ }
    pub fn get_tilt_maximum(&self) -> i64 { self.large.len() as i64 }

    /// 関節点（二階差分が正である点）全体の列 { (x, f(x)) | f(x) + f(x) < f(x - 1) + f(x + 1) }
    pub fn articulation_points(&self) -> Vec<[i64; 2]> {
        let mut xs = self
            .small
            .iter()
            .copied()
            .map(|x| x + self.shift_small)
            .chain(
                self.large
                    .iter()
                    .copied()
                    .map(|Reverse(x)| x + self.shift_large),
            )
            .collect::<Vec<_>>();
        xs.sort_unstable();
        xs.dedup();
        xs.iter().map(|&x| [x, self.eval(x)]).collect()
    }

    /// 関節点と差分の範囲を返します。
    pub fn summary(&self) -> Summary {
        Summary {
            articulation_points: self.articulation_points(),
            tilt: [self.get_tilt_minimum(), self.get_tilt_maximum()],
        }
    }
}

/// [`HeapSlopeTrick::summary()`] の戻り値です。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct Summary {
    articulation_points: Vec<[i64; 2]>,
    tilt: [i64; 2],
}

#[cfg(test)]
mod tests {
    use super::HeapSlopeTrick;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::cmp::Ordering;
    use std::mem::swap;

    const XMAX: i64 = 1_000;
    const XMIN: i64 = -XMAX;
    const X_EVAL_MAX: i64 = 500;
    const X_ADD_MAX: i64 = 300;
    const X_SHIFT_MAX: i64 = 10;

    #[test]
    fn test_compare_with_slice() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let mut slope = HeapSlopeTrick::new();
            let mut brute = Brute::new();
            for _ in 0..20 {
                match rng.gen_range(0..14) {
                    // eval
                    0 => {
                        let x = rng.gen_range(-X_EVAL_MAX..=X_EVAL_MAX);
                        let result = slope.eval(x);
                        let expected = brute.eval(x);
                        assert_eq!(result, expected);
                    }
                    // get_argmin
                    1 => {
                        let result = slope.get_argmin();
                        let expected = brute.get_argmin();
                        assert_eq!(result, expected);
                    }
                    // get_minimum
                    2 => {
                        let result = slope.get_minimum();
                        let expected = brute.get_minimum();
                        assert_eq!(result, expected);
                    }
                    // add_const
                    3 => {
                        let c = rng.gen_range(-X_ADD_MAX..=X_ADD_MAX);
                        slope.add_const(c);
                        brute.add_const(c);
                    }
                    // add_abs
                    4 => {
                        let a = rng.gen_range(-X_SHIFT_MAX..=X_SHIFT_MAX);
                        slope.add_abs(a);
                        brute.add_abs(a);
                    }
                    // add_cutoff_diagonal
                    5 => {
                        let a = rng.gen_range(-X_SHIFT_MAX..=X_SHIFT_MAX);
                        slope.add_cutoff_diagonal(a);
                        brute.add_cutoff_diagonal(a);
                    }
                    // add_cutoff_anti_diagonal
                    6 => {
                        let a = rng.gen_range(-X_SHIFT_MAX..=X_SHIFT_MAX);
                        slope.add_cutoff_anti_diagonal(a);
                        brute.add_cutoff_anti_diagonal(a);
                    }
                    // cumulative_min_from_left
                    7 => {
                        slope.cumulative_min_from_left();
                        brute.cumulative_min_from_left();
                    }
                    // cumulative_min_from_right
                    8 => {
                        slope.cumulative_min_from_right();
                        brute.cumulative_min_from_right();
                    }
                    // shift
                    9 => {
                        let a = rng.gen_range(-X_SHIFT_MAX..=X_SHIFT_MAX);
                        slope.shift(a);
                        brute.shift(a);
                    }
                    // sliding_window_minimum
                    10 => {
                        let mut a = rng.gen_range(-X_SHIFT_MAX..=X_SHIFT_MAX);
                        let mut b = rng.gen_range(-X_SHIFT_MAX..=X_SHIFT_MAX);
                        if b < a {
                            swap(&mut a, &mut b);
                        }
                        slope.sliding_window_minimum(a, b);
                        brute.sliding_window_minimum(a, b);
                    }
                    // get_tilt_minimum
                    11 => {
                        let result = slope.get_tilt_minimum();
                        let expected = brute.get_tilt_minimum();
                        assert_eq!(result, expected);
                    }
                    // get_tilt_maximum
                    12 => {
                        let result = slope.get_tilt_maximum();
                        let expected = brute.get_tilt_maximum();
                        assert_eq!(result, expected);
                    }
                    // articulation_points
                    13 => {
                        let result = slope.articulation_points();
                        let expected = brute.articulation_points();
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    struct Brute {
        values: Vec<i64>,
    }
    impl Brute {
        fn new() -> Self {
            Self {
                values: vec![0; (XMAX - XMIN + 1) as usize],
            }
        }

        fn eval(&self, x: i64) -> i64 {
            assert!((XMIN..=XMAX).contains(&x));
            self.values[(x - XMIN) as usize]
        }

        fn get_argmin(&self) -> [i64; 2] {
            let n = self.values.len();
            let min = self.get_minimum();
            let start = self.values.iter().position(|&y| y == min).unwrap();
            let end = n - 1 - self.values.iter().rev().position(|&y| y == min).unwrap();
            [
                if start == 0 || self.values[start - 1] == std::i64::MAX {
                    std::i64::MIN
                } else {
                    XMIN + start as i64
                },
                if end == n - 1 || self.values[end + 1] == std::i64::MAX {
                    std::i64::MAX
                } else {
                    XMIN + end as i64
                },
            ]
        }

        fn get_minimum(&self) -> i64 { self.values.iter().copied().min().unwrap() }

        fn add_const(&mut self, c: i64) {
            self.values
                .iter_mut()
                .for_each(|x| *x = if *x == std::i64::MAX { std::i64::MAX } else { *x + c });
        }

        fn add_fn(&mut self, f: impl Fn(i64) -> i64) {
            for x in XMIN..=XMAX {
                let i = (x - XMIN) as usize;
                let orig = self.values[i];
                self.values[i] = if orig == std::i64::MAX { std::i64::MAX } else { orig + f(x) };
            }
        }

        fn add_abs(&mut self, a: i64) { self.add_fn(|x| (x - a).abs()); }

        fn add_cutoff_diagonal(&mut self, a: i64) { self.add_fn(|x| (x - a).max(0)); }

        fn add_cutoff_anti_diagonal(&mut self, a: i64) { self.add_fn(|x| (a - x).max(0)); }

        fn cumulative_min_from_left(&mut self) {
            for i in 0..self.values.len() - 1 {
                self.values[i + 1] = self.values[i + 1].min(self.values[i]);
            }
        }

        fn cumulative_min_from_right(&mut self) {
            for i in (0..self.values.len() - 1).rev() {
                self.values[i] = self.values[i].min(self.values[i + 1]);
            }
        }

        fn shift(&mut self, a: i64) {
            match a.cmp(&0) {
                Ordering::Less => {
                    let a = -a as usize;
                    self.values.rotate_left(a);
                    let n = self.values.len();
                    self.values[n - a..]
                        .iter_mut()
                        .for_each(|x| *x = std::i64::MAX);
                }
                Ordering::Greater => {
                    let a = a as usize;
                    self.values.rotate_right(a);
                    self.values[..a].iter_mut().for_each(|x| *x = std::i64::MAX);
                }
                Ordering::Equal => (),
            }
        }

        fn sliding_window_minimum(&mut self, a: i64, b: i64) {
            let n = self.values.len() as i64;
            self.values = (0..n)
                .map(|i| {
                    (((i - b).max(0).min(n) as usize)..((i - a + 1).min(n).max(0) as usize))
                        .map(|j| self.values[j])
                        .min()
                        .unwrap_or(std::i64::MAX)
                })
                .collect();
        }

        fn get_tilt_minimum(&self) -> i64 {
            self.values
                .windows(2)
                .filter(|v| v[0] != std::i64::MAX && v[1] != std::i64::MAX)
                .map(|v| v[1] - v[0])
                .min()
                .unwrap()
        }

        fn get_tilt_maximum(&self) -> i64 {
            self.values
                .windows(2)
                .filter(|v| v[0] != std::i64::MAX && v[1] != std::i64::MAX)
                .map(|v| v[1] - v[0])
                .max()
                .unwrap()
        }

        fn articulation_points(&self) -> Vec<[i64; 2]> {
            self.values
                .windows(3)
                .enumerate()
                .filter(|(_, v)| {
                    v[0] != std::i64::MAX && v[2] != std::i64::MAX && v[0] + v[2] > v[1] * 2
                })
                .map(|(i, v)| [XMIN + 1 + i as i64, v[1]])
                .collect()
        }
    }
}
