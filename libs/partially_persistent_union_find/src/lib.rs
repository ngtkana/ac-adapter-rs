//! union 操作に時刻を付与し、過去の任意時刻での find・same・size を参照できる部分永続 Union-Find。
//!
//! 通常の Union-Find が使う経路圧縮は、過去の親情報を上書きしてしまうため使えない。
//! 代わりに union by size のみで木の高さを $O(\log n)$ に抑え、各頂点に「自身が親へ
//! 併合された時刻」（`time_stamp`）を持たせる。[`find`](PartiallyPersistentUnionFind::find)
//! は指定時刻 `t` までに親へ併合されたノードだけを辿ることで、時刻 `t` 時点の状態を復元する。
//! 各代表元は自身のサイズが変化した時刻の履歴（`size_history`）を持ち、
//! [`size`](PartiallyPersistentUnionFind::size) はここを二分探索して答える。
//!
//! # 仕様
//!
//! 時刻は `usize` で表す。[`union`](PartiallyPersistentUnionFind::union) は
//! 呼び出すたびに狭義単調増加する時刻を要求する（`time == 0` または既存の時刻以下は panic）。
//! `t = usize::MAX` は「最終状態」を意味し、時刻 `usize::MAX` に union があってもそれを含む。
//!
//! - [`PartiallyPersistentUnionFind::new`][]: 頂点数 $n$（$n < \mathrm{isize::MAX}$）で初期化
//! - [`PartiallyPersistentUnionFind::union`][]: 時刻 `time` に頂点 `i`, `j` を結合。既に同じ成分なら `false`
//! - [`PartiallyPersistentUnionFind::find`][]: 時刻 `time` における頂点 `index` の代表元
//! - [`PartiallyPersistentUnionFind::same`][]: 時刻 `time` に `i`, `j` が同じ成分か判定
//! - [`PartiallyPersistentUnionFind::size`][]: 時刻 `time` における `index` の属する成分のサイズ
//! - [`PartiallyPersistentUnionFind::time`][]: `i`, `j` が結合された時刻（未結合なら `None`、`i == j` なら `Some(0)`）
//!
//! # 例
//!
//! ```
//! use partially_persistent_union_find::PartiallyPersistentUnionFind;
//!
//! let mut uf = PartiallyPersistentUnionFind::new(5);
//! assert!(uf.union(0, 1, 10));
//! assert!(uf.union(2, 3, 20));
//! assert!(!uf.union(3, 2, 30)); // すでに結ばれている場合は `false`
//!
//! // 時刻を指定して find・same
//! assert_ne!(uf.find(0, 9), uf.find(1, 9)); // 時刻 9 ではまだ未結合
//! assert_eq!(uf.find(0, 10), uf.find(1, 10)); // 時刻 10 で結合
//! assert!(uf.same(0, 1, 10));
//!
//! // 時刻を指定して size
//! assert_eq!(uf.size(0, 9), 1);
//! assert_eq!(uf.size(0, 10), 2);
//!
//! // 結合時刻を取得
//! assert_eq!(uf.time(0, 1), Some(10));
//! assert_eq!(uf.time(0, 3), None);
//! ```
//!
//! # 計算量
//!
//! 経路圧縮を行わない代わりに union by size のみで木の高さが $O(\log n)$ に収まる。
//!
//! - [`new`](PartiallyPersistentUnionFind::new): $O(n)$
//! - [`union`](PartiallyPersistentUnionFind::union), [`find`](PartiallyPersistentUnionFind::find),
//!   [`same`](PartiallyPersistentUnionFind::same), [`time`](PartiallyPersistentUnionFind::time): $O(\log n)$
//! - [`size`](PartiallyPersistentUnionFind::size): $O(\log n)$（`size_history` の二分探索）

use std::mem::swap;

/// 部分永続化された素集合を表す型。詳細は[クレートのドキュメント](self)を参照。
#[derive(Clone, Debug)]
pub struct PartiallyPersistentUnionFind {
    parent: Vec<isize>,
    time_stamp: Vec<usize>,
    size_history: Vec<Vec<[usize; 2]>>,
    last_stamp: usize,
}

impl PartiallyPersistentUnionFind {
    /// 頂点数 $n$（$n < \mathrm{isize::MAX}$）で、すべて孤立した状態を構築する。
    ///
    /// # 例
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let uf = PartiallyPersistentUnionFind::new(5);
    /// ```
    pub fn new(n: usize) -> Self {
        assert!(n < isize::MAX as usize);
        Self {
            parent: vec![-1; n],
            time_stamp: vec![usize::MAX; n],
            size_history: vec![Vec::new(); n],
            last_stamp: 0,
        }
    }

    /// 時刻 `time` における頂点 `index` の代表元を返す。
    ///
    /// `find(i, t) == find(j, t)` であることと、時刻 `t` に `i`, `j` が同じ成分に属することは同値。
    ///
    /// # 例
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert_ne!(uf.find(0, 9), uf.find(1, 9)); // 時刻 9 ではまだ未結合
    /// ```
    pub fn find(&self, index: usize, time: usize) -> usize {
        if time < self.time_stamp[index] || self.parent[index] < 0 {
            index
        } else {
            self.find(self.parent[index] as usize, time)
        }
    }

    /// 時刻 `time` に `i`, `j` が同じ成分に属するか判定する。
    ///
    /// # 例
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert!(!uf.same(0, 1, 9));
    /// assert!(uf.same(0, 1, 10));
    /// ```
    pub fn same(&self, i: usize, j: usize, time: usize) -> bool {
        self.find(i, time) == self.find(j, time)
    }

    /// `i`, `j` が結合された時刻を返す。未結合なら `None`、`i == j` なら `Some(0)`。
    ///
    /// # 例
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert_eq!(uf.time(0, 1), Some(10));
    /// assert_eq!(uf.time(0, 2), None);
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

    /// 時刻 `time` における `index` の属する成分の要素数を返す。
    ///
    /// # 例
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// uf.union(0, 1, 10);
    /// assert_eq!(uf.size(0, 9), 1);
    /// assert_eq!(uf.size(0, 10), 2);
    /// ```
    pub fn size(&self, mut index: usize, time: usize) -> usize {
        index = self.find(index, time);
        let size_history = &self.size_history[index];
        if size_history.first().is_none_or(|&[s, _]| time < s) {
            return 1;
        }
        let mut l = 0;
        let mut r = size_history.len();
        while 1 < r - l {
            let c = l + (r - l) / 2;
            *if size_history[c][0] <= time { &mut l } else { &mut r } = c;
        }
        size_history[l][1]
    }

    /// 時刻 `time` に頂点 `i`, `j` を結合する。既に同じ成分なら `false`。
    ///
    /// # Panics
    ///
    /// `time` が `0` のとき、または過去の `union` 呼び出しの `time` 以下のとき
    /// （`time` は呼び出しごとに狭義単調増加する必要がある）。
    ///
    /// # 例
    ///
    /// ```
    /// # use partially_persistent_union_find::PartiallyPersistentUnionFind;
    /// let mut uf = PartiallyPersistentUnionFind::new(5);
    /// assert!(uf.union(0, 1, 10));
    /// assert!(!uf.union(0, 1, 20)); // 既に同じ成分
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
    use super::PartiallyPersistentUnionFind;
    use itertools::Itertools;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use randtools::DistinctTwo;

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
                        let t = rng.gen_range(0..=history.len());
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
        let mut right = usize::MAX;
        if uf.find(u, usize::MAX) != uf.find(v, usize::MAX) {
            return None;
        }
        if u == v {
            return Some(0);
        }
        while 1 < right - left {
            let center = left + (right - left) / 2;
            *if uf.find(u, center) == uf.find(v, center) { &mut right } else { &mut left } = center;
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
