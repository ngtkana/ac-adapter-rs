use std::collections::BinaryHeap;

/// Conditional `pop` function.
pub trait PopIf {
    type Value;

    fn pop_if<F>(&mut self, f: F) -> Option<Self::Value>
    where
        F: FnOnce(&mut Self::Value) -> bool;
}

impl<T> PopIf for Vec<T> {
    type Value = T;

    fn pop_if<F>(&mut self, f: F) -> Option<Self::Value>
    where
        F: FnOnce(&mut Self::Value) -> bool,
    {
        if f(self.last_mut()?) {
            self.pop()
        } else {
            None
        }
    }
}

impl<T: Ord> PopIf for BinaryHeap<T> {
    type Value = T;

    fn pop_if<F>(&mut self, f: F) -> Option<Self::Value>
    where
        F: FnOnce(&mut Self::Value) -> bool,
    {
        if f(&mut *self.peek_mut()?) {
            self.pop()
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vec_pop_if() {
        fn is_even(x: &mut u32) -> bool {
            *x % 2 == 0
        }
        fn run(mut vec: Vec<u32>) -> (Vec<u32>, Option<u32>) {
            let result = vec.pop_if(is_even);
            (vec, result)
        }
        assert_eq!(run(vec![]), (vec![], None));
        assert_eq!(run(vec![0]), (vec![], Some(0)));
        assert_eq!(run(vec![1]), (vec![1], None));
        assert_eq!(run(vec![0, 2]), (vec![0], Some(2)));
        assert_eq!(run(vec![0, 3]), (vec![0, 3], None));
        assert_eq!(run(vec![1, 2]), (vec![1], Some(2)));
        assert_eq!(run(vec![1, 3]), (vec![1, 3], None));
    }

    #[test]
    fn test_heap_pop_if() {
        fn is_even(x: &mut u32) -> bool {
            *x % 2 == 0
        }
        fn run(vec: Vec<u32>) -> (Vec<u32>, Option<u32>) {
            let mut heap = vec.into_iter().collect::<BinaryHeap<_>>();
            let result = heap.pop_if(is_even);
            let mut vec = heap.into_vec();
            vec.sort_unstable();
            (vec, result)
        }
        assert_eq!(run(vec![]), (vec![], None));
        assert_eq!(run(vec![0]), (vec![], Some(0)));
        assert_eq!(run(vec![1]), (vec![1], None));
        assert_eq!(run(vec![0, 2]), (vec![0], Some(2)));
        assert_eq!(run(vec![0, 3]), (vec![0, 3], None));
        assert_eq!(run(vec![1, 2]), (vec![1], Some(2)));
        assert_eq!(run(vec![1, 3]), (vec![1, 3], None));
    }
}
