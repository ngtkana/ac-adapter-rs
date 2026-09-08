//! 両端優先度キュー（interval heap）
//!
//! 要素を 2 個ずつ組にしてノードとし、各ノードが区間 $[\min, \max]$ を表す完全二分木として実装する。
//! 偶数位置の列全体は最小値についての二分ヒープ、奇数位置の列全体は最大値についての二分ヒープをなし、
//! さらに同じノード内では偶数位置の値が奇数位置の値以下に保たれる。この 3 つの不変量により、
//! 最小値・最大値の両方を根の近くに保ったまま $O(\log n)$ で挿入・削除できる。
//!
//! # 仕様
//!
//! 多重集合 $S$ を管理する。
//!
//! - [`IntervalHeap::new`]: 空の $S$ を構築
//! - [`IntervalHeap::push`]: $x$ を挿入（$S \leftarrow S \uplus \{x\}$）
//! - [`IntervalHeap::peek_min`], [`IntervalHeap::peek_max`]: $\min(S)$, $\max(S)$ を参照
//! - [`IntervalHeap::pop_min`], [`IntervalHeap::pop_max`]: $\min(S)$, $\max(S)$ を削除して返す
//! - `From<Vec<T>>`: 任意の列から $S$ を構築
//! - `Extend`, `FromIterator`, `IntoIterator` も実装する
//!
//! # 例
//!
//! ```
//! use interval_heap::IntervalHeap;
//!
//! let mut heap = IntervalHeap::from(vec![3, 1, 4, 1, 5]);
//! assert_eq!(heap.peek_min(), Some(&1));
//! assert_eq!(heap.peek_max(), Some(&5));
//! assert_eq!(heap.pop_min(), Some(1));
//! assert_eq!(heap.pop_max(), Some(5));
//! ```
//!
//! # 計算量
//!
//! - 構築（`From<Vec<T>>`）: $O(n)$
//! - [`IntervalHeap::push`], [`IntervalHeap::pop_min`], [`IntervalHeap::pop_max`]: $O(\log n)$
//! - [`IntervalHeap::peek_min`], [`IntervalHeap::peek_max`]: $O(1)$
//!
//! # 出典
//!
//! van Leeuwen, Jan, and Derick Wood. "Interval heaps." The Computer Journal 36.3 (1993): 209-216.

/// 両端優先度キュー（interval heap）。多重集合 $S$ を管理する。
///
/// 要素を 2 個ずつ組にしたノードからなる完全二分木として内部に保持する。詳細はモジュールの説明を参照。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalHeap<T: Ord> {
    values: Vec<T>,
}
impl<T: Ord> IntervalHeap<T> {
    /// 空の $S$ を構築する。
    pub fn new() -> Self {
        Self::default()
    }

    /// $\min(S)$ を返す。$S$ が空なら `None`。
    pub fn peek_min(&self) -> Option<&T> {
        self.values.first()
    }

    /// $\max(S)$ を返す。$S$ が空なら `None`。
    pub fn peek_max(&self) -> Option<&T> {
        self.values.get(1).or_else(|| self.values.first())
    }

    /// $\min(S)$ を削除して返す。$S$ が空なら `None`。
    pub fn pop_min(&mut self) -> Option<T> {
        (!self.values.is_empty()).then_some(())?;
        let ret = self.values.swap_remove(0);
        min_heapify_down(&mut self.values, 0);
        Some(ret)
    }

    /// $\max(S)$ を削除して返す。$S$ が空なら `None`。
    pub fn pop_max(&mut self) -> Option<T> {
        if self.values.len() <= 2 {
            return self.values.pop();
        }
        let ret = self.values.swap_remove(1);
        max_heapify_down(&mut self.values, 1);
        Some(ret)
    }

    /// $x$ を挿入する（$S \leftarrow S \uplus \{x\}$）。
    pub fn push(&mut self, x: T) {
        self.values.push(x);
        let n = self.values.len();
        match n % 2 {
            0 => {
                if self.values[n - 2] > self.values[n - 1] {
                    self.values.swap(n - 2, n - 1);
                    min_heapify_up(&mut self.values, n - 2);
                } else {
                    max_heapify_up(&mut self.values, n - 1);
                }
            }
            1 => {
                if n == 1 {
                    return;
                }
                let end = (n / 2 - 1) | 1;
                if self.values[end] < self.values[n - 1] {
                    self.values.swap(end, n - 1);
                    max_heapify_up(&mut self.values, end);
                } else {
                    min_heapify_up(&mut self.values, n - 1);
                }
            }
            _ => unreachable!(),
        }
    }
}
/// 空の $S$ を構築する。[`IntervalHeap::new`] と同じ。
impl<T: Ord> Default for IntervalHeap<T> {
    fn default() -> Self {
        Self { values: Vec::new() }
    }
}
/// `values` の要素からなる $S$ を $O(n)$ で構築する（ボトムアップに heapify）。
impl<T: Ord> From<Vec<T>> for IntervalHeap<T> {
    fn from(mut values: Vec<T>) -> Self {
        for i in (0..values.len()).rev() {
            match i % 2 {
                0 => min_heapify_down(&mut values, i),
                1 => max_heapify_down(&mut values, i),
                _ => unreachable!(),
            }
        }
        Self { values }
    }
}
/// `iter` の要素を順に [`IntervalHeap::push`] する。
impl<T: Ord> Extend<T> for IntervalHeap<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for x in iter {
            self.push(x);
        }
    }
}
/// $S$ の要素を（順序を保証せず）走査するイテレータを返す。
impl<T: Ord> IntoIterator for IntervalHeap<T> {
    type IntoIter = std::vec::IntoIter<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter()
    }
}
/// `iter` の要素からなる $S$ を構築する。
impl<T: Ord> std::iter::FromIterator<T> for IntervalHeap<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut ret = Self::new();
        ret.extend(iter);
        ret
    }
}

fn min_heapify_up<T: Ord>(values: &mut [T], mut start: usize) {
    while start != 0 {
        let p = (start / 2 - 1) & !1;
        if values[p] <= values[start] {
            break;
        }
        values.swap(p, start);
        start = p;
    }
}

fn max_heapify_up<T: Ord>(values: &mut [T], mut end: usize) {
    while end != 1 {
        let p = (end / 2 - 1) | 1;
        if values[p] >= values[end] {
            break;
        }
        values.swap(p, end);
        end = p;
    }
}

fn min_heapify_down<T: Ord>(values: &mut [T], mut start: usize) {
    let n = values.len();
    loop {
        let end = start + 1;
        if end >= n {
            break;
        }
        if values[start] > values[end] {
            values.swap(start, end);
        }
        let mut next = 2 * start + 4;
        if next >= n || values[next - 2] < values[next] {
            next -= 2;
        }
        if next >= n || values[start] <= values[next] {
            break;
        }
        values.swap(start, next);
        start = next;
    }
}

fn max_heapify_down<T: Ord>(values: &mut [T], mut end: usize) {
    let n = values.len();
    loop {
        let start = end - 1;
        if values[start] > values[end] {
            values.swap(start, end);
        }
        let mut next = 2 * end + 3;
        if next >= n || values[next - 2] > values[next] {
            next -= 2;
        }
        if next >= n || values[end] >= values[next] {
            break;
        }
        values.swap(end, next);
        end = next;
    }
    if n % 2 == 1 && 1 < n && values[n - 1] > values[(n / 2 - 1) | 1] {
        values.swap(n - 1, (n / 2 - 1) | 1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use rstest::rstest;

    fn validate_interval_heap(heap: &IntervalHeap<usize>) {
        let n = heap.values.len();
        // even is min-heap
        {
            for i in (0..n / 2).step_by(2) {
                let left = 2 * i + 2;
                if left < n {
                    assert!(heap.values[i] <= heap.values[left]);
                }
                let right = 2 * i + 4;
                if right < n {
                    assert!(heap.values[i] <= heap.values[right]);
                }
            }
        }
        // odd is max-heap
        {
            for i in (1..n / 2).step_by(2) {
                let left = 2 * i + 1;
                if left < n {
                    assert!(heap.values[i] >= heap.values[left]);
                }
                let right = 2 * i + 3;
                if right < n {
                    assert!(heap.values[i] >= heap.values[right]);
                }
            }
        }
        // even <= odd
        {
            for i in (0..n).step_by(2) {
                if i + 1 < n {
                    assert!(heap.values[i] <= heap.values[i + 1]);
                }
            }
        }
        // trailing single element
        if n % 2 == 1 && n > 1 {
            assert!(heap.values[n - 1] <= heap.values[(n / 2 - 1) | 1]);
        }
    }

    #[test]
    fn test_interval_heap_init() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(0..=3);
            let vec = (0..n).map(|_| rng.gen_range(0..16)).collect::<Vec<_>>();
            let interval_heap = IntervalHeap::from(vec.clone());
            validate_interval_heap(&interval_heap);
        }
    }

    #[rstest]
    #[case(3000, 0, 10)]
    #[case(100, 100, 100)]
    fn test_interval_heap(#[case] test_cases: usize, #[case] nmax: usize, #[case] qmax: usize) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..test_cases {
            let n = rng.gen_range(0..=nmax);
            let q = rng.gen_range(0..=qmax);
            let lim = rng.gen_range(1..=n + q + 10);
            let mut vec = (0..n).map(|_| rng.gen_range(0..lim)).collect::<Vec<_>>();
            let mut interval_heap = IntervalHeap::from(vec.clone());
            vec.sort_unstable();
            for _ in 0..q {
                match rng.gen_range(0..3) {
                    // push
                    0 => {
                        let x = rng.gen_range(0..lim);
                        interval_heap.push(x);
                        let i = vec.binary_search(&x).unwrap_or_else(|x| x);
                        vec.insert(i, x);
                        validate_interval_heap(&interval_heap);
                    }
                    // pop_min
                    1 => {
                        if let Some(x) = interval_heap.pop_min() {
                            assert_eq!(x, vec.remove(0));
                            validate_interval_heap(&interval_heap);
                        } else {
                            assert!(vec.is_empty());
                        }
                    }
                    // pop_max
                    2 => {
                        if let Some(x) = interval_heap.pop_max() {
                            assert_eq!(x, vec.pop().unwrap());
                            validate_interval_heap(&interval_heap);
                        } else {
                            assert!(vec.is_empty());
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
