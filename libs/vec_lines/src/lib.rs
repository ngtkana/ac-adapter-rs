//! 傾き単調な直線の列を `Vec` で管理します。
//!
//! [基本的な使い方は `VecLines` をご覧ください。](VecLines)
use std::convert::TryFrom;
use std::fmt::Debug;
use std::hash::Hash;
use std::marker::PhantomData;
use std::ops::Add;
use std::ops::Mul;
use std::ops::Sub;

/// 傾きが単調減少な直線の列を管理します。
pub type VecLinesDecreasing<T> = VecLines<T, DecreasingTilt>;
/// 傾きが単調増加な直線の列を管理します。
pub type VecLinesIncreasing<T> = VecLines<T, IncreasingTilt>;

/// 傾き単調な直線の列を `Vec` で管理します。
///
/// # 使い方
///
/// ```
/// # use vec_lines::VecLinesDecreasing;
/// // 傾きが単調減少な直線の列を管理します。
/// let mut lines = VecLinesDecreasing::<i32>::new();
///
/// // 直線を挿入していきます。
/// lines.push([1, 0]);
/// lines.push([0, 10]);
/// lines.push([-1, 30]);
/// assert_eq!(lines.len(), 3);
///
/// // 黄金分割探索で最適値を計算できます。
/// assert_eq!(lines.eval_gcc(-10), Some(-10)); // x
/// assert_eq!(lines.eval_gcc(15), Some(10)); // 10
/// assert_eq!(lines.eval_gcc(40), Some(-10)); // -x + 30
///
/// // 直線番号指定でも評価します。（しゃくとり法などのため）
/// assert_eq!(lines.get(0).unwrap().eval(100), 100);
/// assert_eq!(lines.get(1).unwrap().eval(100), 10);
/// assert_eq!(lines.get(2).unwrap().eval(100), -70);
/// ```
///
///
/// # 傾きの等しい直線を入れたときの挙動
///
/// 定数項を比較して、真に改善している場合は直前のものを消して挿入し、
/// そこから改めて通常の不要直線除去のアルゴリズムを実行します。
/// 一方改善していない場合は挿入せず処理を終了します。
///
/// ただし改善しているというのは、
///
/// * 制約が [`DecreasingTilt`] のときには、定数項が小さいことを、
/// * 制約が [`IncreasingTilt`] のときには、定数項が大きいこと
///
/// を意味します。
///
/// ```
/// # use vec_lines::{VecLinesDecreasing, Line};
/// // 前よりも良いものがくると置き換えます。
/// let mut lines = VecLinesDecreasing::<i32>::new();
/// lines.push([0, 10]);
/// lines.push([0, 0]);
/// let expected = vec![Line([0, 0])];
/// assert_eq!(lines.iter_copied().collect::<Vec<_>>(), expected);
///
/// // 前よりも良くないものは無視します。
/// let mut lines = VecLinesDecreasing::<i32>::new();
/// lines.push([0, 0]);
/// lines.push([0, 10]);
/// let expected = vec![Line([0, 0])];
/// assert_eq!(lines.iter_copied().collect::<Vec<_>>(), expected);
///
/// // 置き換えたあとは通常の不要直線除去アルゴリズムが走ります。
/// let mut lines = VecLinesDecreasing::<i32>::new();
/// lines.push([1, 0]);
/// lines.push([0, 10]);
/// lines.push([-1, 1000]);
/// lines.push([-1, 0]);
/// let expected = vec![Line([1, 0]), Line([-1, 0])];
/// assert_eq!(lines.iter_copied().collect::<Vec<_>>(), expected);
/// ```
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub struct VecLines<T, C> {
    lines: Vec<Line<T>>,
    _marker: PhantomData<fn(C) -> C>,
}
impl<T: Signed, C: Constraint> VecLines<T, C> {
    /// 傾き単調な直線の列を `Vec` で管理します。
    ///
    /// # 使い方
    ///
    /// ```
    /// # use vec_lines::{VecLinesDecreasing, VecLinesIncreasing, VecLines, DecreasingTilt,
    /// # IncreasingTilt};
    /// // 傾きが単調減少な直線の列を管理します。
    /// let lines = VecLinesDecreasing::<i32>::new();
    ///
    /// // 傾きが単調減少な直線の列を管理します。
    /// let lines = VecLinesDecreasing::<i32>::new();
    ///
    /// // それぞれ、別名を使わずに構築する方法です。
    /// let lines = VecLines::<i32, DecreasingTilt>::new();
    /// let lines = VecLines::<i32, IncreasingTilt>::new();
    /// ```
    pub fn new() -> Self {
        Self {
            lines: Vec::new(),
            _marker: PhantomData,
        }
    }

    /// 管理している直線が 0 本のとき `true`、さもなくば `false` を返します。
    ///
    /// # 使い方
    /// ```
    /// # use vec_lines::VecLinesDecreasing;
    /// let lines = VecLinesDecreasing::<i32>::new();
    /// assert!(lines.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool { self.lines.is_empty() }

    /// 管理している直線の本数を返します。
    ///
    /// 不要な直線が自動的に削除されると、このメソッドの返す値も減少します。
    ///
    /// # 使い方
    /// ```
    /// # use vec_lines::VecLinesDecreasing;
    /// let mut lines = VecLinesDecreasing::<i32>::new();
    /// assert_eq!(lines.len(), 0);
    ///
    /// lines.push([0, 0]);
    /// ```
    pub fn len(&self) -> usize { self.lines.len() }

    /// index 番目の直線を返します。
    ///
    /// # 使い方
    ///
    /// ```
    /// # use vec_lines::VecLinesDecreasing;
    /// let mut lines = VecLinesDecreasing::<i32>::new();
    /// lines.push([1, 0]);
    /// lines.push([0, 10]);
    /// lines.push([-1, 30]);
    ///
    /// // 直線を手に入れたら、次は `Line::eval` で評価です。
    /// assert_eq!(lines.get(0).unwrap().eval(100), 100);
    /// ```
    pub fn get(&self, index: usize) -> Option<Line<T>> { self.lines.get(index).copied() }

    /// 後ろに直線を挿入します。
    ///
    /// # Panics
    ///
    /// * マーカー `C` の定める傾きの単調性に反するとき。
    ///
    ///
    /// # 計算量
    ///
    /// 償却定数時間。
    ///
    ///
    /// # 使い方
    ///
    /// ```
    /// # use vec_lines::VecLinesDecreasing;
    /// let mut lines = VecLinesDecreasing::<i32>::new();
    /// lines.push([1, 0]);
    /// lines.push([0, 10]);
    /// lines.push([-1, 30]);
    ///
    /// // 直線を手に入れたら、次は `Line::eval` で評価です。
    /// assert_eq!(lines.get(0).unwrap().eval(100), 100);
    /// ```
    pub fn push(&mut self, line: [T; 2]) {
        assert!(
            self.lines
                .last()
                .map_or(true, |prv| C::ok(*prv, Line(line))),
            "傾きの単調性に違反しています。"
        );
        if let Some(&Line(prv)) = self.lines.last() {
            if prv[0] == line[0] {
                if C::strictly_better(line[1], prv[1]) {
                    self.lines.pop();
                } else {
                    return;
                }
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

    /// 黄金分割探索で最適値を計算します。
    ///
    /// # 計算量
    ///
    /// 管理している直線の本数を n として、Θ( lg n )。
    ///
    ///
    /// # 使い方
    ///
    /// ```
    /// # use vec_lines::VecLinesDecreasing;
    /// let mut lines = VecLinesDecreasing::<i32>::new();
    /// lines.push([1, 0]);
    /// lines.push([0, 10]);
    /// lines.push([-1, 30]);
    ///
    /// assert_eq!(lines.eval_gcc(-10), Some(-10)); // x
    /// assert_eq!(lines.eval_gcc(15), Some(10)); // 10
    /// assert_eq!(lines.eval_gcc(40), Some(-10)); // -x + 30
    /// ```
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

    /// 管理している直線を順番に返すイテレータを返します。
    ///
    /// # 使い方
    ///
    /// ```
    /// # use vec_lines::{VecLinesDecreasing, Line};
    /// let mut lines = VecLinesDecreasing::<i32>::new();
    /// lines.push([1, 0]);
    /// lines.push([0, 10]);
    /// lines.push([-1, 30]);
    ///
    /// let lines = lines
    ///     .iter_copied()
    ///     .map(Line::into_coeff)
    ///     .collect::<Vec<_>>();
    /// assert_eq!(lines, vec![[1, 0], [0, 10], [-1, 30]]);
    /// ```
    pub fn iter_copied(&self) -> impl '_ + Iterator<Item = Line<T>> { self.lines.iter().copied() }
}

/// 一次関数 $ax + b$ を、`[a, b]` の形で管理します。
///
/// 中身は `.0` でも `into_coeff` でもとれます。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq, Copy)]
pub struct Line<T>(pub [T; 2]);
impl<T: Signed> Line<T> {
    /// 特定の x 座標における値を計算します。
    ///
    /// # 使い方
    /// ```
    /// # use vec_lines::Line;
    /// let line = Line([2, 10]);
    /// assert_eq!(line.eval(2), 14);
    /// ```
    pub fn eval(self, x: T) -> T { self.0[0] * x + self.0[1] }

    /// 係数を返します。
    ///
    /// # 使い方
    /// ```
    /// # use vec_lines::Line;
    /// let line = Line([2, 10]);
    /// assert_eq!(line.into_coeff(), [2, 10]);
    /// ```
    pub fn into_coeff(self) -> [T; 2] { self.0 }
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

/// 傾きがどちら向きに単調かをあらわすマーカー
pub trait Constraint: Clone + Debug + Hash + PartialEq {
    fn ok<T: Signed>(prv: Line<T>, crr: Line<T>) -> bool;
    fn strictly_better<T: Signed>(x: T, y: T) -> bool;
}
/// 傾き単調減少を意味するマーカー
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum DecreasingTilt {}
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
/// 傾き単調増加を意味するマーカー
pub enum IncreasingTilt {}
impl Constraint for DecreasingTilt {
    fn ok<T: Signed>(Line([a0, _]): Line<T>, Line([a1, _]): Line<T>) -> bool { a0 >= a1 }

    fn strictly_better<T: Signed>(x: T, y: T) -> bool { x < y }
}
impl Constraint for IncreasingTilt {
    fn ok<T: Signed>(Line([a0, _]): Line<T>, Line([a1, _]): Line<T>) -> bool { a0 <= a1 }

    fn strictly_better<T: Signed>(x: T, y: T) -> bool { x > y }
}

/// 符号つき整数
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
    fn default() -> Self { Self::new() }
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
    fn test_golden_section(x: [isize; 2]) -> [isize; 2] { golden_section(x) }

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
