//! 傾き単調な直線群を管理し、任意の $x$ における最大値・最小値クエリに答える Convex Hull Trick。
//!
//! 直線を追加するたびに、傾きの単調性と定数項の優劣から不要な直線をスタック的に取り除き、
//! 常に「下側（または上側）包絡線を構成する直線だけ」を `Vec` で保持する。クエリは黄金分割探索で
//! 答える。クエリの $x$ が挿入順に単調に動く場合は [`VecLines::get`] としゃくとり法を組み合わせる
//! ことで、`eval_gcc` よりさらに高速に処理できる。
//!
//! # 仕様
//!
//! [`Constraint`] で傾きの単調方向を指定する（[`VecLinesDecreasing`] は単調減少、
//! [`VecLinesIncreasing`] は単調増加）。
//!
//! - `push` は直線 $y = ax + b$ を `[a, b]` で追加する。傾きの単調性に反すると panic する
//! - `eval_gcc` は $x$ における最適値（[`VecLinesDecreasing`] は最小値、
//!   [`VecLinesIncreasing`] は最大値）を返す
//! - `get` は `index` 番目の直線 [`Line`] を返す
//! - `len`、`is_empty`、`iter_copied` で内部状態を参照する
//!
//! 傾きが等しい直線を追加した場合、定数項が真に改善していれば直前の直線を置き換えてから
//! 通常の不要直線除去を行い、改善していなければ追加を無視する。
//!
//! # 例
//!
//! ```
//! use vec_lines::VecLinesDecreasing;
//!
//! let mut lines = VecLinesDecreasing::<i32>::new();
//! lines.push([1, 0]); // y = x
//! lines.push([0, 10]); // y = 10
//! lines.push([-1, 30]); // y = -x + 30
//!
//! assert_eq!(lines.eval_gcc(-10), Some(-10)); // x = -10 での最小値
//! assert_eq!(lines.eval_gcc(15), Some(10)); // y = 10 での最小値
//! assert_eq!(lines.eval_gcc(40), Some(-10)); // -x + 30 での最小値
//! ```
//!
//! # 計算量
//!
//! - `push`: 償却 $O(1)$
//! - `eval_gcc`: $O(\log n)$（$n$ は管理している直線の本数）
use std::convert::TryFrom;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Add;
use std::ops::Mul;
use std::ops::Sub;

/// 傾きが単調減少な直線群を管理する [`VecLines`]。
pub type VecLinesDecreasing<T> = VecLines<T, DecreasingTilt>;
/// 傾きが単調増加な直線群を管理する [`VecLines`]。
pub type VecLinesIncreasing<T> = VecLines<T, IncreasingTilt>;

/// 傾き単調な直線群。詳細はクレートの説明を参照。
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct VecLines<T, C> {
    lines: Vec<Line<T>>,
    _marker: PhantomData<fn(C) -> C>,
}
impl<T: Signed, C: Constraint> VecLines<T, C> {
    /// 空の直線群を構築する。
    ///
    /// # 例
    /// ```
    /// use vec_lines::VecLinesDecreasing;
    /// let lines = VecLinesDecreasing::<i32>::new();
    /// assert!(lines.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            lines: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// 直線を 1 本も持たなければ `true` を返す。
    pub fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }

    /// 管理している直線の本数を返す。不要な直線は自動的に削除されるため、
    /// [`push`](Self::push) のたびに単調増加するとは限らない。
    pub fn len(&self) -> usize {
        self.lines.len()
    }

    /// `index` 番目の直線 [`Line`] を返す。範囲外なら `None`。
    ///
    /// # 例
    /// ```
    /// use vec_lines::VecLinesDecreasing;
    /// let mut lines = VecLinesDecreasing::<i32>::new();
    /// lines.push([1, 0]);
    /// assert_eq!(lines.get(0).unwrap().eval(100), 100);
    /// assert!(lines.get(1).is_none());
    /// ```
    pub fn get(&self, index: usize) -> Option<Line<T>> {
        self.lines.get(index).copied()
    }

    /// 直線 $y = ax + b$ を `[a, b]` で追加する。
    ///
    /// # Panics
    ///
    /// マーカー `C` の定める傾きの単調性に違反するとき。
    ///
    /// # 計算量
    ///
    /// 償却 $O(1)$。
    pub fn push(&mut self, line: [T; 2]) {
        assert!(
            self.lines.last().is_none_or(|prv| C::ok(*prv, Line(line))),
            "傾きの単調性に違反しています。"
        );
        if let Some(&Line(prv)) = self.lines.last()
            && prv[0] == line[0]
        {
            if C::strictly_better(line[1], prv[1]) {
                self.lines.pop();
            } else {
                return;
            }
        }
        self.lines.push(Line(line));
        while 3 <= self.lines.len()
            && weakly_convex(
                *<&[Line<_>; 3]>::try_from(&self.lines[self.lines.len() - 3..]).unwrap(),
            )
        {
            let p = self.lines.pop().unwrap();
            self.lines.pop().unwrap();
            self.lines.push(p);
        }
    }

    /// 黄金分割探索で $x$ における最適値を計算する。直線が 1 本もなければ `None`。
    ///
    /// # 計算量
    ///
    /// $O(\log n)$（$n$ は管理している直線の本数）。
    pub fn eval_gcc(&self, x: T) -> Option<T> {
        if self.lines.is_empty() {
            return None;
        }
        let mut i0 = -1;
        let mut i3 = self.len() as isize;
        while 3 <= i3 - i0 {
            let [i1, i2] = golden_section([i0, i3]);
            if C::strictly_better(
                self.lines[i1 as usize].eval(x),
                self.lines[i2 as usize].eval(x),
            ) {
                i3 = i2;
            } else {
                i0 = i1;
            }
        }
        assert!((2..=3).contains(&(i3 - i0)));
        let y1 = self.lines[(i0 + 1) as usize].eval(x);
        let y2 = self.lines[(i3 - 1) as usize].eval(x);
        Some(if C::strictly_better(y1, y2) { y1 } else { y2 })
    }

    /// 管理している直線を順番に返すイテレータを返す。
    ///
    /// # 例
    /// ```
    /// use vec_lines::VecLinesDecreasing;
    /// let mut lines = VecLinesDecreasing::<i32>::new();
    /// lines.push([1, 0]);
    /// lines.push([0, 10]);
    /// let coeffs = lines.iter_copied().map(|l| l.into_coeff()).collect::<Vec<_>>();
    /// assert_eq!(coeffs, vec![[1, 0], [0, 10]]);
    /// ```
    pub fn iter_copied(&self) -> impl '_ + Iterator<Item = Line<T>> {
        self.lines.iter().copied()
    }
}

/// 一次関数 $ax + b$ を `[a, b]` の形で保持する。中身は `.0` でも [`Line::into_coeff`] でも取れる。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, Copy)]
pub struct Line<T>(pub [T; 2]);
impl<T: Signed> Line<T> {
    /// $x$ における値 $ax + b$ を計算する。
    ///
    /// # 例
    /// ```
    /// use vec_lines::Line;
    /// let line = Line([2, 10]);
    /// assert_eq!(line.eval(2), 14);
    /// ```
    pub fn eval(self, x: T) -> T {
        self.0[0] * x + self.0[1]
    }

    /// 係数 `[a, b]` を返す。
    pub fn into_coeff(self) -> [T; 2] {
        self.0
    }
}

fn weakly_convex<T: Signed>(
    [Line([a0, b0]), Line([a1, b1]), Line([a2, b2])]: [Line<T>; 3],
) -> bool {
    (a2 - a1) * (b1 - b0) <= (a1 - a0) * (b2 - b1)
}

fn golden_section([i0, i3]: [isize; 2]) -> [isize; 2] {
    let d = ((i3 - i0) as f64 * (5_f64.sqrt() - 1.0) / 2.0).ceil() as isize;
    [i3 - d, i0 + d]
}

/// 傾きがどちら向きに単調かを表すマーカートレイト。
pub trait Constraint: Clone + Debug + Hash + PartialEq {
    fn ok<T: Signed>(prv: Line<T>, crr: Line<T>) -> bool;
    fn strictly_better<T: Signed>(x: T, y: T) -> bool;
}
/// 傾き単調減少を意味するマーカー型。
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum DecreasingTilt {}
/// 傾き単調増加を意味するマーカー型。
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum IncreasingTilt {}
impl Constraint for DecreasingTilt {
    fn ok<T: Signed>(Line([a0, _]): Line<T>, Line([a1, _]): Line<T>) -> bool {
        a0 >= a1
    }

    fn strictly_better<T: Signed>(x: T, y: T) -> bool {
        x < y
    }
}
impl Constraint for IncreasingTilt {
    fn ok<T: Signed>(Line([a0, _]): Line<T>, Line([a1, _]): Line<T>) -> bool {
        a0 <= a1
    }

    fn strictly_better<T: Signed>(x: T, y: T) -> bool {
        x > y
    }
}

/// [`VecLines`] が要素として扱える符号つき整数。標準の符号つき整数型に実装済み。
pub trait Signed:
    Debug
    + Clone
    + Copy
    + Default
    + Hash
    + PartialOrd
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
{
}
macro_rules! impl_signed {
    ($($T:ty),* $(,)?) => {$(
        impl Signed for $T {}
    )*}
}
impl_signed! { i8, i16, i32, i64, i128, isize }

impl<T: Signed, C: Constraint> Default for VecLines<T, C> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::golden_section;
    use super::VecLinesDecreasing;
    use super::VecLinesIncreasing;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use test_case::test_case;

    #[test_case([0, 3] => [1, 2])]
    #[test_case([0, 4] => [1, 3])]
    #[test_case([0, 5] => [1, 4])]
    #[test_case([0, 6] => [2, 4])]
    #[test_case([0, 7] => [2, 5])]
    fn test_golden_section(x: [isize; 2]) -> [isize; 2] {
        golden_section(x)
    }

    /*
    こちらの問題の本質部分です。

    COLOCON -Colopl programming contest 2018- Final（オープンコンテスト）
    C - スペースエクスプローラー高橋君
    https://atcoder.jp/contests/colopl2018-final-open/tasks/colopl2018_final_c
     */
    #[test]
    fn test_decreasing_tilt() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let mut lines = VecLinesDecreasing::new();
            let mut raw_lines = Vec::new();
            let n = rng.gen_range(1..20);
            for x in 0..3 * n {
                let x = x / 3;
                let y = rng.gen_range(0..(n * n));
                let one = -2 * x;
                let zero = x * x + y;
                raw_lines.push([one, zero]);
                lines.push([one, zero]);
            }
            let mut i = 0;
            for x in 0..n {
                // 全探索
                let expected = lines.iter_copied().map(|line| line.eval(x)).min().unwrap();

                // しゃくとり法
                let mut result = lines.get(i).unwrap().eval(x);
                while let Some(swp) = lines.get(i + 1).map(|line| line.eval(x)) {
                    if result <= swp {
                        break;
                    }
                    result = swp;
                    i += 1;
                }
                assert_eq!(result, expected);

                // 黄金分割探索
                let result = lines.eval_gcc(x).unwrap();
                assert_eq!(result, expected);
            }
        }
    }

    #[test]
    fn test_increasing_tilt() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let mut lines = VecLinesIncreasing::new();
            let mut raw_lines = Vec::new();
            let n = rng.gen_range(1..20);
            for x in 0..3 * n {
                let x = x / 3;
                let y = rng.gen_range(0..(n * n));
                let one = 2 * x;
                let zero = x * x + y;
                raw_lines.push([one, zero]);
                lines.push([one, zero]);
            }
            let mut i = 0;
            for x in 0..n {
                // 全探索
                let expected = lines.iter_copied().map(|line| line.eval(x)).max().unwrap();

                // しゃくとり法
                let mut result = lines.get(i).unwrap().eval(x);
                while let Some(swp) = lines.get(i + 1).map(|line| line.eval(x)) {
                    if swp <= result {
                        break;
                    }
                    result = swp;
                    i += 1;
                }
                assert_eq!(result, expected);

                // 黄金分割探索
                let result = lines.eval_gcc(x).unwrap();
                assert_eq!(result, expected);
            }
        }
    }
}
