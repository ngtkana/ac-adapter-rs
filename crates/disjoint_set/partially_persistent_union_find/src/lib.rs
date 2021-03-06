//! 部分永続化された、素集合データ構造です。
//!
//! [構造体 `PartiallyPersistentUnionFind` のドキュメントをご覧ください。](PartiallyPersistentUnionFind)
//!

use std::{mem::swap, usize::MAX};

/// 部分永続化された、素集合データ構造です。
///
/// # 時刻について
///
/// `MAX` といえば `std::usize:MAX` のことであるとします。
///
/// * 入力できるのは `1..=MAX`。
/// * 過去クエリで時刻 t を指定すると、t
/// と同じかそれより小さな時刻のイベントが適用された状態を参照します。
/// * t = `MAX` でクエリすると最終状態を参照します。（仮に時刻 `MAX`
/// にイベントが存在したとしても。）
///
/// # Examples
///
/// ```
/// use partially_persistent_union_find::PartiallyPersistentUnionFind;
///
/// // 頂点数を指定してクエリ
/// let mut uf = PartiallyPersistentUnionFind::new(5);
///
/// // 時刻を指定して union
/// assert!( uf.union(0, 1, 10));
/// assert!( uf.union(2, 3, 20));
/// assert!(!uf.union(3, 2, 30)); // すでに結ばれている場合は `false`
/// assert!( uf.union(3, 4, 40));
/// assert!(!uf.union(3, 3, 30)); // すでに結ばれている場合は `false`
///
/// // 時刻を指定して find
/// assert_ne!(uf.find(0, 9), uf.find(1, 9));
/// assert_eq!(uf.find(0, 10), uf.find(1, 10));
/// assert_ne!(uf.find(0, 99), uf.find(2, 99));
/// assert_eq!(uf.find(2, 99), uf.find(3, 99));
///
/// // 時刻を指定して same
/// assert!(!uf.same(0, 1, 9));
/// assert!( uf.same(0, 1, 10));
///
/// // 1 以上の時刻を指定して size
/// assert_eq!(uf.size(0, 9), 1);
/// assert_eq!(uf.size(0, 10), 2);
/// assert_eq!(uf.size(2, 19), 1);
/// assert_eq!(uf.size(2, 39), 2);
/// assert_eq!(uf.size(2, 40), 3);
///
/// // union された時刻をクエリ
/// assert_eq!(uf.time(0, 0), Some(0));
/// assert_eq!(uf.time(0, 1), Some(10));
/// assert_eq!(uf.time(2, 3), Some(20));
/// assert_eq!(uf.time(0, 3), None);
/// ```
///
///
/// # 時刻 `MAX` にイベントがある場合も同様です。
///
/// ```
/// use partially_persistent_union_find::PartiallyPersistentUnionFind;
/// use std::usize::MAX;
///
/// let mut uf = PartiallyPersistentUnionFind::new(5);
///
/// // MAX にイベントをセット
/// uf.union(0, 1, MAX);
///
/// // 適用前を参照
/// assert!(!uf.same(0, 1, MAX - 1));
///
/// // 適用後を参照
/// assert!( uf.same(0, 1, MAX));
/// ```
///
///
/// # 速度面
///
/// * [`size`](PartiallyPersistentUnionFind::size) を実現するために n
/// 回程度の動的メモリ確保の必要なフィールド `size_history` を管理しているため、
/// 定数倍が重くなっています。
///
#[derive(Clone, Debug)]
pub struct PartiallyPersistentUnionFind {
    parent: Vec<isize>,
    time_stamp: Vec<usize>,
    size_history: Vec<Vec<[usize; 2]>>,
    last_stamp: usize,
}

impl PartiallyPersistentUnionFind {
    /// 新しくデータ構造を構築します。
    ///
    /// # 制約
    ///
    /// `n < std::isize::MAX`
    ///
    /// # Examples
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let uf = PartiallyPersistentUnionFind::new(5);
    /// ```
    ///
    pub fn new(n: usize) -> Self {
        assert!(n < std::isize::MAX as usize);
        Self {
            parent: vec![-1; n],
            time_stamp: vec![MAX; n],
            size_history: vec![Vec::new(); n],
            last_stamp: 0,
        }
    }
    /// 時刻 time の代表の頂点番号を返します。
    ///
    /// [See `PartiallyPersistentUnionFind` for examples.](PartiallyPersistentUnionFind)
    ///
    /// # 出力の要件
    ///
    /// * i と j が同じ成分に属することと、`find(i) == find(j)` であることが同値である。
    /// * `find(i)` は i の属する成分の要素のうちいずれかである。
    ///
    /// # Examples
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert_ne!(uf.find(0, 9), uf.find(1, 9));
    /// ```
    pub fn find(&self, index: usize, time: usize) -> usize {
        if time < self.time_stamp[index] || self.parent[index] < 0 {
            index
        } else {
            self.find(self.parent[index] as usize, time)
        }
    }
    /// 時刻 time に i と j が同じ成分に属するならば `true`、属さないならば `false` を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert_eq!(uf.size(0, 9), 1);
    /// ```
    pub fn same(&self, i: usize, j: usize, time: usize) -> bool {
        self.find(i, time) == self.find(j, time)
    }
    /// 2 頂点が結合された時刻を返します。
    ///
    /// `i == j` の場合は 0 を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert_eq!(uf.time(0, 1), Some(10));
    /// ```
    pub fn time(&self, mut i: usize, mut j: usize) -> Option<usize> {
        let mut time = 0;
        while self.time_stamp[i] != self.time_stamp[j] {
            if self.time_stamp[i] > self.time_stamp[j] {
                swap(&mut i, &mut j);
            }
            time = self.time_stamp[i];
            i = self.parent[i] as usize;
        }
        if i == j {
            Some(time)
        } else {
            None
        }
    }
    /// 時刻 time の i の属する成分の要素数を返します。
    ///
    /// # Examples
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert_eq!(uf.size(0, 9), 1);
    /// ```
    pub fn size(&self, mut index: usize, time: usize) -> usize {
        index = self.find(index, time);
        let size_history = &self.size_history[index];
        if size_history.get(0).map_or(true, |&[s, _]| time < s) {
            return 1;
        }
        let mut l = 0;
        let mut r = size_history.len();
        while 1 < r - l {
            let c = l + (r - l) / 2;
            *if size_history[c][0] <= time {
                &mut l
            } else {
                &mut r
            } = c;
        }
        size_history[l][1]
    }
    /// 今までのどのクエリ時刻よりも真に大きな時刻 time を指定して、頂点 i, j を結合します。
    ///
    /// ただし、初回クエリ時刻は 1 以上である必要があります。
    ///
    ///
    /// # Returns
    ///
    /// * i と j が異なる成分に属していたとき `true` を返します。
    /// * そうでないとき、`false` を返します。
    ///
    ///
    /// # Panics
    ///
    /// * `time == 0` のとき。
    /// * time と同じかそれより大きなクエリを受け取ったことがあるとき。
    ///
    /// # Examples
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// ```
    pub fn union(&mut self, mut i: usize, mut j: usize, time: usize) -> bool {
        assert!(self.last_stamp < time);
        i = self.find(i, time);
        j = self.find(j, time);
        if i == j {
            return false;
        }
        if self.parent[i] > self.parent[j] {
            swap(&mut i, &mut j);
        }
        self.parent[i] += self.parent[j];
        self.size_history[i].push([time, -self.parent[i] as usize]);
        self.parent[j] = i as isize;
        self.time_stamp[j] = time;
        true
    }
}

#[cfg(test)]
mod tests {
    use {
        super::PartiallyPersistentUnionFind,
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        randtools::DistinctTwo,
        std::usize::MAX,
    };

    #[test]
    fn test_rand() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(2..=12);
            let q = rng.gen_range(1..=12);

            let mut uf = PartiallyPersistentUnionFind::new(n);
            let mut history = Vec::new();
            for _ in 0..q {
                match rng.gen_range(0..4) {
                    // union
                    0 => {
                        let (u, v) = rng.sample(DistinctTwo(0..n));
                        uf.union(u, v, history.len() + 1);
                        history.push([u, v, history.len() + 1]);
                    }
                    // compare find
                    1 => {
                        let u = rng.gen_range(0..n);
                        let v = rng.gen_range(0..n);
                        let time = rng.gen_range(0..=history.len());
                        let cmp = retake(n, time, &history);
                        assert_eq!(uf.find(u, time) == uf.find(v, time), cmp[u] == cmp[v]);
                    }
                    // size
                    2 => {
                        let u = rng.gen_range(0..n);
                        let t = rng.gen_range(0..history.len() + 1);
                        let result = uf.size(u, t);
                        let cmp = retake(n, t, &history);
                        let expected = cmp.iter().filter(|&&c| c == cmp[u]).count();
                        assert_eq!(result, expected);
                    }
                    // time
                    3 => {
                        let (u, v) = rng.sample(DistinctTwo(0..n));
                        let result = uf.time(u, v);
                        let expected = time_brute(&uf, u, v);
                        assert_eq!(result, expected);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }

    fn time_brute(uf: &PartiallyPersistentUnionFind, u: usize, v: usize) -> Option<usize> {
        let mut left = 0;
        let mut right = MAX;
        if uf.find(u, MAX) != uf.find(v, MAX) {
            return None;
        }
        if u == v {
            return Some(0);
        }
        while 1 < right - left {
            let center = left + (right - left) / 2;
            *if uf.find(u, center) == uf.find(v, center) {
                &mut right
            } else {
                &mut left
            } = center;
        }
        Some(right)
    }

    fn retake(n: usize, t: usize, history: &[[usize; 3]]) -> Vec<usize> {
        let mut cmp = (0..n).collect_vec();
        for [u, v] in history
            .iter()
            .copied()
            .filter(|&[_, _, s]| s <= t)
            .map(|[u, v, _]| [u, v])
        {
            let u = cmp[u];
            let v = cmp[v];
            for x in &mut cmp {
                if *x == v {
                    *x = u;
                }
            }
        }
        cmp
    }
}
