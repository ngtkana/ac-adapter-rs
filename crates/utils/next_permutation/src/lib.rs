use std::cmp::Ordering;

pub fn next_permutation<T: Ord>(a: &mut [T]) -> bool {
    next_permutation_by(a, Ord::cmp)
}

pub fn next_permutation_by<T>(a: &mut [T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> bool {
    if a.is_empty() {
        true
    } else {
        if let Some(i) = (0..a.len() - 1).rfind(|&i| cmp(&a[i], &a[i + 1]) == Ordering::Less) {
            a[i + 1..].reverse();
            let j = i
                + 1
                + a[i + 1..]
                    .iter()
                    .position(|x| cmp(&a[i], x) == (Ordering::Less))
                    .unwrap();
            a.swap(i, j);
            true
        } else {
            false
        }
    }
}

pub fn next_permutation_by_key<T, U, F>(a: &mut [T], mut f: F) -> bool
where
    F: FnMut(&T) -> U,
    U: Ord,
{
    next_permutation_by(a, |x, y| f(x).cmp(&f(y)))
}

#[cfg(test)]
mod tests {
    use super::{next_permutation, next_permutation_by_key};
    use std::cmp::Reverse;

    fn collect_permutations<T: Ord + Clone>(a: &[T]) -> Vec<Vec<T>> {
        let mut a = a.to_vec();
        let mut res = Vec::new();
        while {
            res.push(a.clone());
            next_permutation(&mut a)
        } {}
        res
    }

    fn collect_permutations_reverse<T: Ord + Clone>(a: &[T]) -> Vec<Vec<T>> {
        let mut a = a.to_vec();
        let mut res = Vec::new();
        while {
            res.push(a.clone());
            next_permutation_by_key(&mut a, |x| Reverse(x.clone()))
        } {}
        res
    }

    #[test]
    fn test_perm() {
        let result = collect_permutations(&[0, 1, 2]);
        let expected = vec![
            vec![0, 1, 2],
            vec![0, 2, 1],
            vec![1, 0, 2],
            vec![1, 2, 0],
            vec![2, 0, 1],
            vec![2, 1, 0],
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_with_repetition() {
        let result = collect_permutations(&[0, 0, 1, 1]);
        let expected = vec![
            vec![0, 0, 1, 1],
            vec![0, 1, 0, 1],
            vec![0, 1, 1, 0],
            vec![1, 0, 0, 1],
            vec![1, 0, 1, 0],
            vec![1, 1, 0, 0],
        ];
        assert_eq!(result, expected);
    }

    #[test]
    fn test_pred_permutation() {
        let result = collect_permutations_reverse(&[2, 1, 0]);
        let expected = vec![
            vec![2, 1, 0],
            vec![2, 0, 1],
            vec![1, 2, 0],
            vec![1, 0, 2],
            vec![0, 2, 1],
            vec![0, 1, 2],
        ];
        assert_eq!(result, expected);
    }
}
