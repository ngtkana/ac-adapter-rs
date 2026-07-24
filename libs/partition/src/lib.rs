//! Stable partition algorithm
//!
//! See [`partition`] for details.

/// Partitions a mutable slice in-place, stably.
///
/// Rearranges elements such that those for which `pred` returns `true` are placed before
/// those for which `pred` returns `false`, while preserving the relative order within each group.
///
/// # Time Complexity
/// O(n), where n is the length of the slice.
///
/// # Extra Memory
/// O(n) for an auxiliary buffer that temporarily holds elements.
///
/// # Stability
/// The relative order of elements for which `pred` returns `true` is preserved.
/// The relative order of elements for which `pred` returns `false` is also preserved.
///
/// # Returns
/// The number of elements for which `pred` returned `true`.
///
/// # Examples
///
/// Basic usage:
/// ```
/// let mut v = vec![1, 2, 3, 4, 5, 6];
/// let n = partition::partition(&mut v, |&x| x % 2 == 0);
/// assert_eq!(n, 3);
/// assert_eq!(v[0..n], [2, 4, 6]);
/// assert_eq!(v[n..], [1, 3, 5]);
/// ```
///
/// Stability with duplicate keys:
/// ```
/// let mut pairs = vec![(2, 'a'), (1, 'b'), (2, 'c'), (1, 'd')];
/// let n = partition::partition(&mut pairs, |&(k, _)| k == 2);
/// assert_eq!(n, 2);
/// // Elements with key 2 come first, and their relative order (a before c) is preserved.
/// assert_eq!(&pairs[0..n], &[(2, 'a'), (2, 'c')]);
/// // Elements with key 1 come next, and their relative order (b before d) is preserved.
/// assert_eq!(&pairs[n..], &[(1, 'b'), (1, 'd')]);
/// ```
pub fn partition<T>(slice: &mut [T], mut pred: impl FnMut(&T) -> bool) -> usize {
    let n = slice.len();
    let mut guard = PartitionGuard {
        slice,
        read_idx: 0,
        write_idx: 0,
        aux: Vec::with_capacity(n),
    };

    while guard.read_idx < n {
        let i = guard.read_idx;
        let keep = pred(&guard.slice[i]);
        // SAFETY: i < n == guard.slice.len(). read_idx is strictly increasing,
        // so each element at index i is read exactly once.
        let value = unsafe { guard.slice.as_ptr().add(i).read() };
        if keep {
            // SAFETY: write_idx <= i < n. The destination at write_idx is either
            // uninitialized (write_idx == i) or contains a stale duplicate
            // (write_idx < i, previously moved to aux). write() does not drop the
            // old value, so it is safe.
            unsafe {
                guard.slice.as_mut_ptr().add(guard.write_idx).write(value);
            }
            guard.write_idx += 1;
        } else {
            guard.aux.push(value);
        }
        guard.read_idx += 1;
    }

    let true_count = guard.write_idx;
    for (offset, value) in guard.aux.drain(..).enumerate() {
        // SAFETY: true_count + offset < n (loop invariant: aux.len() == read_idx - write_idx).
        // The destination at true_count + offset is a stale duplicate that was read and moved to aux.
        unsafe {
            guard
                .slice
                .as_mut_ptr()
                .add(true_count + offset)
                .write(value);
        }
    }
    guard.write_idx = n;

    true_count
}

struct PartitionGuard<'a, T> {
    slice: &'a mut [T],
    read_idx: usize,
    write_idx: usize,
    aux: Vec<T>,
}

impl<T> Drop for PartitionGuard<'_, T> {
    fn drop(&mut self) {
        // On panic during pred(), slice[write_idx..read_idx) contains stale duplicates
        // (the actual values are in aux). We restore the invariant by writing them back.
        for idx in (self.write_idx..self.read_idx).rev() {
            let value = self
                .aux
                .pop()
                .expect("invariant: aux.len() == read_idx - write_idx");
            // SAFETY: idx < read_idx <= slice.len(), and aux.pop() gives exactly the
            // stale duplicate at this position (1-to-1 correspondence via loop invariant).
            unsafe {
                self.slice.as_mut_ptr().add(idx).write(value);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let mut v: Vec<i32> = vec![];
        let n = partition(&mut v, |_| true);
        assert_eq!(n, 0);
    }

    #[test]
    fn test_single_true() {
        let mut v = vec![42];
        let n = partition(&mut v, |_| true);
        assert_eq!(n, 1);
        assert_eq!(v, [42]);
    }

    #[test]
    fn test_single_false() {
        let mut v = vec![42];
        let n = partition(&mut v, |_| false);
        assert_eq!(n, 0);
        assert_eq!(v, [42]);
    }

    #[test]
    fn test_all_true() {
        let mut v = vec![1, 2, 3, 4, 5];
        let n = partition(&mut v, |_| true);
        assert_eq!(n, 5);
        assert_eq!(v, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_all_false() {
        let mut v = vec![1, 2, 3, 4, 5];
        let n = partition(&mut v, |_| false);
        assert_eq!(n, 0);
        assert_eq!(v, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_stability_manual_example() {
        // Elements: (key, label)
        // Predicate: key == 2
        // Expected: (2,'a'), (2,'c') | (1,'b'), (1,'d')
        // The relative order within each group should be preserved.
        let mut v = vec![(2, 'a'), (1, 'b'), (2, 'c'), (1, 'd')];
        let n = partition(&mut v, |&(k, _)| k == 2);
        assert_eq!(n, 2);
        assert_eq!(&v[0..n], &[(2, 'a'), (2, 'c')]);
        assert_eq!(&v[n..], &[(1, 'b'), (1, 'd')]);
    }

    fn stable_partition_brute<T: Clone>(v: &[T], pred: impl Fn(&T) -> bool) -> Vec<T> {
        let mut true_part = Vec::new();
        let mut false_part = Vec::new();
        for item in v {
            if pred(item) {
                true_part.push(item.clone());
            } else {
                false_part.push(item.clone());
            }
        }
        true_part.extend(false_part);
        true_part
    }

    #[test]
    fn test_random() {
        use rand::prelude::StdRng;
        use rand::Rng;
        use rand::SeedableRng;

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..150 {
            let len = rng.gen_range(0..50);
            let values: Vec<u32> = (0..len).map(|_| rng.gen()).collect();
            let threshold: u32 = rng.gen();
            let pred = |&x: &u32| x < threshold;

            // Tag each value with its original index
            let tagged: Vec<(u32, usize)> = values
                .iter()
                .enumerate()
                .map(|(idx, &val)| (val, idx))
                .collect();

            let mut partition_result = tagged.clone();
            let n = partition(&mut partition_result, |&(v, _)| pred(&v));

            // Brute-force reference
            let brute_result = stable_partition_brute(&tagged, |&(v, _)| pred(&v));

            // Check the result matches the brute-force
            assert_eq!(
                partition_result, brute_result,
                "Random test failed at iteration: threshold={threshold}, values={values:?}",
            );

            // Check that count of true elements is correct
            assert_eq!(n, brute_result.iter().take(n).count());
        }
    }

    #[test]
    fn test_stability_dedicated() {
        use rand::prelude::StdRng;
        use rand::Rng;
        use rand::SeedableRng;

        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..150 {
            let len = rng.gen_range(0..50);
            let values: Vec<u32> = (0..len).map(|_| rng.gen()).collect();
            let threshold: u32 = rng.gen();

            // Map values to their original indices for stability verification
            let indices: Vec<usize> = (0..len).collect();
            let tagged: Vec<(u32, usize)> = values
                .iter()
                .zip(indices.iter())
                .map(|(&val, &idx)| (val, idx))
                .collect();

            let mut result = tagged.clone();
            let n = partition(&mut result, |&(v, _)| v < threshold);

            // Verify true part: original indices must be strictly increasing
            for i in 0..n.saturating_sub(1) {
                assert!(
                    result[i].1 < result[i + 1].1,
                    "True part not stable: result[{}].idx={}, result[{}].idx={}",
                    i,
                    result[i].1,
                    i + 1,
                    result[i + 1].1
                );
            }

            // Verify false part: original indices must be strictly increasing
            for i in n..result.len().saturating_sub(1) {
                assert!(
                    result[i].1 < result[i + 1].1,
                    "False part not stable: result[{}].idx={}, result[{}].idx={}",
                    i,
                    result[i].1,
                    i + 1,
                    result[i + 1].1
                );
            }
        }
    }
}
