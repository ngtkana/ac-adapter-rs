//! A library to enumerate permutations, shuffles, and partitions.

/// Returns the next permutation of `a` in lexicographic order.
pub fn next_permutation<T: Ord>(a: &mut [T]) -> bool {
    if a.is_empty() {
        return false;
    }
    let Some(i) = (0..a.len() - 1).rfind(|&i| a[i] < a[i + 1]) else {
        return false;
    };
    let j = a.iter().rposition(|x| x > &a[i]).unwrap();
    a.swap(i, j);
    a[i + 1..].reverse();
    true
}
/// Calls `f` for each permutation of `a` in lexicographic order.
pub fn for_each_permutation<T: Ord, F: FnMut(&[T])>(a: &mut [T], mut f: F) {
    a.sort();
    while {
        f(a);
        next_permutation(a)
    } {}
}
/// Returns all permutations of `a` in lexicographic order.
pub fn permutations<T: Ord + Clone>(a: Vec<T>) -> Vec<Vec<T>> {
    let mut a = a;
    let mut result = Vec::new();
    for_each_permutation(&mut a, |a| result.push(a.to_vec()));
    result
}
/// Returns the next $(K, N - K)$-shuffle of `a` in lexicographic order.
pub fn next_shuffle<T: Ord>(a: &mut [T], k: usize) -> bool {
    let n = a.len();
    if n == k {
        return false;
    }
    let (left, right) = a.split_at_mut(k);
    let Some(mut i) = left.iter().rposition(|x| x < right.last().unwrap()) else {
        return false;
    };
    let mut j = right.iter().position(|x| &left[i] < x).unwrap();
    std::mem::swap(&mut left[i], &mut right[j]);
    i += 1;
    j += 1;
    let swap_len = (k - i).min(n - k - j);
    left[k - swap_len..].swap_with_slice(&mut right[j..j + swap_len]);
    left[i..].rotate_left(k.saturating_sub(i + swap_len));
    right[j..].rotate_right((n - k).saturating_sub(j + swap_len));
    true
}
/// Calls `f` for each $(K, N - K)$-shuffle of `a` in lexicographic order.
pub fn for_each_shuffle<T: Ord, F: FnMut(&[T])>(a: &mut [T], k: usize, mut f: F) {
    a.sort();
    while {
        f(&a[..k]);
        next_shuffle(a, k)
    } {}
}
/// Returns all $(K, N - K)$-shuffles of `a` in lexicographic order.
pub fn shuffles<T: Ord + Clone>(a: Vec<T>, k: usize) -> Vec<Vec<T>> {
    let mut a = a;
    let mut result = Vec::new();
    for_each_shuffle(&mut a, k, |a| result.push(a.to_vec()));
    result
}
/// Returns the next pairing (ascending $(2,2,\dots,2)$-shuffle) of `a` in lexicographic order.
pub fn next_pairing(a: &mut [usize]) -> bool {
    assert!(a.len() % 2 == 0);
    assert!(a.len() <= 32);
    let n = a.len();
    let mut used = 0_u32;
    for i in (0..n).rev() {
        used |= 1 << a[i];
        if i % 2 == 1 && a[i] + 1 < (used + 1).next_power_of_two().trailing_zeros() as usize {
            a[i] = (used >> (a[i] + 1)).trailing_zeros() as usize + a[i] + 1;
            used ^= 1 << a[i];
            for i in i + 1..n {
                a[i] = used.trailing_zeros() as usize;
                used ^= 1 << a[i];
            }
            return true;
        }
    }
    false
}
/// Calls `f` for each pairing (ascending $(2,2,\dots,2)$-shuffle) of `a` in lexicographic order.
pub fn for_each_pairing<F: FnMut(&[usize])>(n: usize, mut f: F) {
    let mut a = (0..n).collect::<Vec<_>>();
    while {
        f(&a);
        next_pairing(&mut a)
    } {}
}
/// Returns all pairings (ascending $(2,2,\dots,2)$-shuffles) of `a` in lexicographic order.
pub fn pairings(n: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for_each_pairing(n, |a| result.push(a.to_vec()));
    result
}
/// Returns the next partition of `a` in lexicographic order.
pub fn next_partition(a: &mut Vec<usize>) -> bool {
    let Some(mut sum) = a.pop() else { return false };
    if a.is_empty() {
        return false;
    }
    while let Some(x) = a.pop() {
        sum += x;
        if a.last().map_or(true, |&last| last > x) {
            a.push(x + 1);
            a.extend(std::iter::repeat(1).take(sum - x - 1));
            break;
        }
    }
    true
}
/// Calls `f` for each partition of `n` in lexicographic order.
pub fn for_each_partition<F: FnMut(&[usize])>(n: usize, mut f: F) {
    let mut a = vec![1; n];
    while {
        f(&a);
        next_partition(&mut a)
    } {}
}
/// Returns all partitions of `n` in lexicographic order.
pub fn partitions(n: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for_each_partition(n, |a| result.push(a.to_vec()));
    result
}
/// Returns the previous partition of `a` in lexicographic order.
pub fn prev_partition(a: &mut Vec<usize>) -> bool {
    let Some(i) = a.iter().rposition(|&x| x != 1) else { return false };
    let max = a[i] - 1;
    let mut sum = a.split_off(i).into_iter().sum::<usize>();
    while sum >= max {
        a.push(max);
        sum -= max;
    }
    if sum > 0 {
        a.push(sum);
    }
    true
}
/// Calls `f` for each partition of `n` in the reverse of the lexicographic order.
pub fn for_each_partition_rev<F: FnMut(&[usize])>(n: usize, mut f: F) {
    if n == 0 {
        f(&[]);
        return;
    }
    let mut a = vec![n];
    while {
        f(&a);
        prev_partition(&mut a)
    } {}
}
/// Returns all partitions of `n` in the reverse of the lexicographic order.
pub fn partitions_rev(n: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    for_each_partition_rev(n, |a| result.push(a.to_vec()));
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use itertools::Itertools;

    #[test]
    fn test_permutations() {
        for n in 0..=5 {
            let result = permutations((0..n).collect::<Vec<_>>());
            assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
            assert_eq!(result.len(), (1..=n).product());
        }
    }

    #[test]
    fn test_shuffles() {
        for n in 0..=5 {
            for k in 0..=n {
                let result = shuffles((0..n).collect::<Vec<_>>(), k);
                for result in &result {
                    assert!(result[..k].iter().tuple_windows().all(|(a, b)| a < b));
                    assert!(result[k..].iter().tuple_windows().all(|(a, b)| a < b));
                }
                assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
                assert_eq!(
                    result.len(),
                    (1..=n).product::<usize>()
                        / (1..=k).product::<usize>()
                        / (1..=(n - k)).product::<usize>()
                );
            }
        }
    }

    #[test]
    fn test_pairings() {
        for n in (0..=10).step_by(2) {
            let result = pairings(n);
            assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
            for result in &result {
                assert!(result.chunks_exact(2).all(|x| x[0] < x[1]));
                assert!(result.iter().step_by(2).tuple_windows().all(|(a, b)| a < b));
            }
            assert_eq!(result.len(), (1..=n).step_by(2).product::<usize>());
        }
    }

    #[test]
    fn test_partitions() {
        let n = 10;
        let mut p = vec![1; n];
        for step in 2..n {
            for i in 0..n - step {
                p[i + step] += p[i];
            }
        }
        for n in 0..10 {
            let result = partitions(n);
            assert!(result.iter().tuple_windows().all(|(a, b)| a < b));
            assert_eq!(result.len(), p[n]);
            assert_eq!(result, partitions_rev(n).into_iter().rev().collect_vec());
        }
    }
}
