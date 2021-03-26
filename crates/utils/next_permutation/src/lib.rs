use std::cmp::Ordering;

pub fn next_permutation<T: Ord>(a: &mut [T]) -> bool {
    next_permutation_by(a, Ord::cmp)
}

pub fn next_permutation_by<T>(a: &mut [T], mut cmp: impl FnMut(&T, &T) -> Ordering) -> bool {
    if a.is_empty() {
        true
    } else {
        (0..a.len() - 1)
            .rfind(|&i| cmp(&a[i], &a[i + 1]) == Ordering::Less)
            .map_or(false, |i| {
                a[i + 1..].reverse();
                let j = i
                    + 1
                    + a[i + 1..]
                        .iter()
                        .position(|x| cmp(&a[i], x) == (Ordering::Less))
                        .unwrap();
                a.swap(i, j);
                true
            })
    }
}

pub fn next_permutation_by_key<T, U, F>(a: &mut [T], mut f: F) -> bool
where
    F: FnMut(&T) -> U,
    U: Ord,
{
    next_permutation_by(a, |x, y| f(x).cmp(&f(y)))
}

#[derive(Debug, Clone, PartialEq)]
pub struct PermutationsMap<T, U, F>
where
    T: Ord,
    F: FnMut(&[T]) -> U,
{
    state: Box<[T]>,
    f: F,
    exhausted: bool,
}

impl<T, U, F> Iterator for PermutationsMap<T, U, F>
where
    T: Ord,
    F: FnMut(&[T]) -> U,
{
    type Item = U;
    fn next(&mut self) -> Option<U> {
        if self.exhausted {
            None
        } else {
            let res = (self.f)(&self.state);
            self.exhausted |= !next_permutation(&mut self.state);
            Some(res)
        }
    }
}

/// Takes an initial state of a slice and closure and creates an iterator which calls that closure
/// on each succeeding permutations of it.
///
/// # Examples
/// Basic usage:
/// ```
/// use next_permutation::permutations_map;
///
/// let mut iter = permutations_map(vec![0, 1, 2], |v| v[1]);
///
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(2));
/// assert_eq!(iter.next(), Some(0));
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), None);
/// ```
pub fn permutations_map<T, U, F>(state: impl Into<Box<[T]>>, f: F) -> PermutationsMap<T, U, F>
where
    T: Ord,
    F: FnMut(&[T]) -> U,
{
    let state = state.into();
    let exhausted = state.is_empty();
    PermutationsMap {
        state,
        f,
        exhausted,
    }
}

/// Takes an initial state of a slice and calls a closure on each permutations of an slice.
///
/// # Examples
/// Basic usage:
/// ```
/// use next_permutation::permutations_for_each;
///
/// let mut vec = Vec::new();
/// permutations_for_each(vec![0, 1, 2], |v| vec.push(v[1]));
/// assert_eq!(vec, vec![1, 2, 0, 2, 0, 1]);
/// ```
pub fn permutations_for_each<T, F>(state: impl Into<Box<[T]>>, mut f: F)
where
    T: Ord,
    F: FnMut(&[T]),
{
    let mut state = state.into();
    while {
        f(&state);
        next_permutation(&mut state)
    } {}
}

#[cfg(test)]
mod tests {
    use crate::permutations_map;
    use itertools::assert_equal;

    #[test]
    fn test_permutations_map() {
        assert_equal(
            permutations_map(vec![0, 0, 0], <[u32]>::to_vec),
            vec![vec![0, 0, 0]],
        );
        assert_equal(
            permutations_map(vec![0, 0, 1], <[u32]>::to_vec),
            vec![vec![0, 0, 1], vec![0, 1, 0], vec![1, 0, 0]],
        );
        assert_equal(
            permutations_map(vec![0, 1, 2], <[u32]>::to_vec),
            vec![
                vec![0, 1, 2],
                vec![0, 2, 1],
                vec![1, 0, 2],
                vec![1, 2, 0],
                vec![2, 0, 1],
                vec![2, 1, 0],
            ],
        );
    }
}
