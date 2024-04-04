//! # Interval Heaps
//!
//! van Leeuwen, Jan, and Derick Wood. "Interval heaps." The Computer Journal 36.3 (1993): 209-216.
//!
//!
//! * Double-ended priority queue: [`IntervalHeap`]

/// Interval heap (double-ended priority queue)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntervalHeap<T: Ord> {
    values: Vec<T>,
}
impl<T: Ord> IntervalHeap<T> {
    /// Constructs a new, empty interval heap.
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns $\min(S)$.
    pub fn peek_min(&self) -> Option<&T> {
        self.values.first()
    }

    /// Returns $\max(S)$.
    pub fn peek_max(&self) -> Option<&T> {
        self.values.get(1).or_else(|| self.values.first())
    }

    /// Removes and returns $\min(S)$.
    pub fn pop_min(&mut self) -> Option<T> {
        (!self.values.is_empty()).then_some(())?;
        let ret = self.values.swap_remove(0);
        if self.values.len() >= 2 {
            min_heapify_down(&mut self.values, 0);
        }
        Some(ret)
    }

    /// Removes and returns $\max(S)$.
    pub fn pop_max(&mut self) -> Option<T> {
        if self.values.len() <= 1 {
            return self.values.pop();
        }
        let ret = self.values.swap_remove(1);
        if self.values.len() >= 3 {
            max_heapify_down(&mut self.values, 1);
        }
        Some(ret)
    }

    /// $S \leftarrow S \cup \\{\\!\\{x\\}\\!\\}$.
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
        };
    }
}
impl<T: Ord> Default for IntervalHeap<T> {
    fn default() -> Self {
        Self { values: Vec::new() }
    }
}
impl<T: Ord + std::fmt::Debug> From<Vec<T>> for IntervalHeap<T> {
    fn from(values: Vec<T>) -> Self {
        let mut result = Self::new();
        for x in values {
            result.push(x);
        }
        result
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
        let mut swp = 2 * start + 4;
        if swp >= n || values[swp - 2] < values[swp] {
            swp -= 2;
        }
        if swp >= n || values[start] <= values[swp] {
            break;
        }
        values.swap(start, swp);
        start = swp;
    }
}

fn max_heapify_down<T: Ord>(values: &mut [T], mut end: usize) {
    let n = values.len();
    loop {
        let start = end - 1;
        if values[start] > values[end] {
            values.swap(start, end);
        }
        let mut swp = 2 * end + 3;
        if swp >= n || values[swp - 2] > values[swp] {
            swp -= 2;
        }
        if swp >= n || values[end] >= values[swp] {
            break;
        }
        values.swap(end, swp);
        end = swp;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::rngs::StdRng;
    use rand::Rng;
    use rand::SeedableRng;

    fn validate_interval_heap(heap: &IntervalHeap<i32>) {
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
            // even <= odd
            {
                for i in (0..n).step_by(2) {
                    if i + 1 < n {
                        assert!(heap.values[i] <= heap.values[i + 1]);
                    }
                }
            }
        }
    }

    #[test]
    fn test_interval_heap() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(0..4);
            let q = rng.gen_range(10..100);
            let lim = rng.gen_range(1..=n + q + 10);
            let mut vec = (0..n).map(|_| rng.gen_range(0..lim)).collect::<Vec<_>>();
            let mut interval_heap = IntervalHeap::from(vec.clone());
            vec.sort_unstable();
            eprintln!("vec = {:?}", vec);
            for _ in 0..q {
                match rng.gen_range(0..3) {
                    // push
                    0 => {
                        let x = rng.gen_range(0..lim);
                        eprintln!("push {}", x);
                        interval_heap.push(x);
                        let i = vec.binary_search(&x).unwrap_or_else(|x| x);
                        vec.insert(i, x);
                        validate_interval_heap(&interval_heap);
                    }
                    // pop_min
                    1 => {
                        eprintln!("pop_min");
                        if let Some(x) = interval_heap.pop_min() {
                            assert_eq!(x, vec.remove(0));
                            validate_interval_heap(&interval_heap);
                        } else {
                            assert!(vec.is_empty());
                        }
                    }
                    // pop_max
                    2 => {
                        eprintln!("pop_max");
                        if let Some(x) = interval_heap.pop_max() {
                            assert_eq!(x, vec.pop().unwrap());
                            validate_interval_heap(&interval_heap);
                        } else {
                            assert!(vec.is_empty());
                        }
                    }
                    _ => unreachable!(),
                }
                eprintln!("vec = {:?}", &vec);
            }
            eprintln!("---");
        }
    }
}
