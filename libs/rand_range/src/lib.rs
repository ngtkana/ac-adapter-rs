//! 非減少な整数列を一様ランダムに生成する。
//!
//! 範囲から $K$ 個の値を独立に一様サンプリングしてから昇順に並べ替えるだけでは、
//! 値が衝突した箇所に分布が偏ってしまう。ソート中に同順位が生じるたびに後ろの要素を
//! $1$ 減らす（内部の `skew_sort`）ことでこの偏りを補正し、非減少数列
//! $\min(I) \le x_0 \le x_1 \le \dots \le x_{K-1} \le \max(I)$ が一様分布になるようにする。
//!
//! # 仕様
//!
//! - [`RngRange::gen_range_many`][]: [`Rng`] の拡張メソッド。範囲 `range`（$I$）から長さ $K$ の
//!   非減少数列を一様ランダムに生成する
//!
//! # 例
//!
//! ```
//! use rand_range::RngRange;
//! use rand::{Rng, SeedableRng, rngs::StdRng};
//!
//! let mut rng = StdRng::seed_from_u64(42);
//! let [a, b, c] = rng.gen_range_many(0..=10);
//! assert!(0 <= a && a <= b && b <= c && c <= 10);
//! ```
//!
//! # 計算量
//!
//! - [`RngRange::gen_range_many`][]: $O(K^2)$（$K$ は生成する数列の長さ。内部のソートがボトルネック）

use rand::{
    Rng,
    distributions::uniform::{SampleRange, SampleUniform},
};

/// [`RngRange::gen_range_many`] が内部で使う整数型の抽象化（加算・1減算ができる型）。
pub trait Int: Ord + SampleUniform + Sized + Copy {
    fn add_usize(self, other: usize) -> Self;
    fn sub_one(&mut self);
}

macro_rules! impl_int {
    ($($type:ty),+$(,)?) => {
       $(
           impl Int for $type {
               fn add_usize(self, other: usize) -> Self {
                   self + other as Self
               }
               fn sub_one(&mut self) {
                   *self -= 1;
               }
           }
       )+
    };
}

impl_int! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

/// `Range`・`RangeInclusive` を統一的に扱うためのトレイト（右端を `usize` 分拡張できる）。
pub trait RangeTrait {
    type Item: Int;
    fn add_usize(&self, extra: usize) -> Self;
}

impl<T: Int> RangeTrait for std::ops::Range<T> {
    type Item = T;

    fn add_usize(&self, extra: usize) -> Self {
        let Self { start, end } = *self;
        Self {
            start,
            end: end.add_usize(extra),
        }
    }
}

impl<T: Int> RangeTrait for std::ops::RangeInclusive<T> {
    type Item = T;

    fn add_usize(&self, extra: usize) -> Self {
        *self.start()..=self.end().add_usize(extra)
    }
}

/// [`gen_range_many`](RngRange::gen_range_many) を実装している、[`Rng`] の拡張トレイト。
pub trait RngRange: Rng {
    /// 範囲 `range`（$I$）に収まる、長さ $K$ の非減少数列を一様ランダムに生成する。
    ///
    /// $$
    /// \min(I) \le x_0 \le x_1 \le \dots \le x_{K-1} \le \max(I)
    /// $$
    ///
    /// # 例
    ///
    /// ```
    /// use rand_range::RngRange;
    /// use rand::{Rng, SeedableRng, rngs::StdRng};
    ///
    /// let mut rng = StdRng::seed_from_u64(42);
    /// let [a, b, c] = rng.gen_range_many(0..=10);
    /// assert!(0 <= a && a <= b && b <= c && c <= 10);
    /// ```
    fn gen_range_many<const K: usize, T: Int>(
        &mut self,
        range: impl SampleRange<T> + RangeTrait<Item = T>,
    ) -> [T; K] {
        let mut item =
            std::array::from_fn::<_, K, _>(|i| self.gen_range(range.add_usize(K - i - 1)));
        skew_sort(&mut item);
        item
    }
}

impl<T: Rng> RngRange for T {}

fn skew_sort<T: Int>(items: &mut [T]) {
    for i in 0..items.len() - 1 {
        for j in 0..items.len() - 1 - i {
            if items[j] > items[j + 1] {
                items.swap(j, j + 1);
                items[j + 1].sub_one();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{SeedableRng, rngs::StdRng};
    use std::collections::HashMap;

    #[test]
    fn test_skew_sort() {
        for n in 2..=5 {
            let mut map = HashMap::new();
            for a in 0..=n {
                for b in 0..n {
                    let mut items = [a, b];
                    skew_sort(&mut items);
                    *map.entry(items).or_insert(0) += 1;
                }
            }
            for a in 0..n {
                for b in a..n {
                    assert_eq!(map[&[a, b]], 2);
                }
            }
        }
        for n in 3..=5 {
            let mut map = HashMap::new();
            for a in 0..=n + 1 {
                for b in 0..=n {
                    for c in 0..n {
                        let mut items = [a, b, c];
                        skew_sort(&mut items);
                        *map.entry(items).or_insert(0) += 1;
                    }
                }
            }
            for a in 0..n {
                for b in a..n {
                    for c in b..n {
                        assert_eq!(map[&[a, b, c]], 6);
                    }
                }
            }
        }
        for n in 4..=5 {
            let mut map = HashMap::new();
            for a in 0..=n + 2 {
                for b in 0..=n + 1 {
                    for c in 0..=n {
                        for d in 0..n {
                            let mut items = [a, b, c, d];
                            skew_sort(&mut items);
                            *map.entry(items).or_insert(0) += 1;
                        }
                    }
                }
            }
            for a in 0..n {
                for b in a..n {
                    for c in b..n {
                        for d in c..n {
                            assert_eq!(map[&[a, b, c, d]], 24);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_gen_range_meny() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..=5);
            let [a, b] = rng.gen_range_many(0..=n);
            assert!(0 <= a && a <= b && b <= n);
        }
        for _ in 0..200 {
            let n = rng.gen_range(2..=6);
            let [a, b, c] = rng.gen_range_many(0..=n);
            assert!(0 <= a && a <= b && b <= c && c <= n);
        }
        for _ in 0..200 {
            let n = rng.gen_range(3..=7);
            let [a, b, c, d] = rng.gen_range_many(0..=n);
            assert!(0 <= a && a <= b && b <= c && c <= d && d <= n);
        }
    }
}
