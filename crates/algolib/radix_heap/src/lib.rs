use std::fmt::{self, Debug};

const RADIX_HEAP_LEN: usize = 32;

#[derive(Clone, PartialEq)]
pub struct RadixHeap<T> {
    stacks: [Vec<(u32, T)>; RADIX_HEAP_LEN],
    last: u32,
    len: u32,
}
impl<T> RadixHeap<T> {
    pub fn new() -> Self {
        Self {
            stacks: <[Vec<(u32, T)>; RADIX_HEAP_LEN]>::default(),
            last: 0,
            len: 0,
        }
    }
    pub fn push(&mut self, key: u32, value: T) {
        assert!(self.last <= key);
        self.len += 1;
        self.stacks[Self::index(key ^ self.last)].push((key, value));
    }
    pub fn pop(&mut self) -> Option<(u32, T)> {
        if self.len == 0 {
            None
        } else {
            if self.stacks[0].is_empty() {
                let stack = std::mem::replace(
                    self.stacks
                        .iter_mut()
                        .find(|stack| !stack.is_empty())
                        .unwrap(),
                    Vec::new(),
                );
                let new_last = stack.iter().map(|&(key, _)| key).min().unwrap();
                for (key, value) in stack {
                    self.stacks[Self::index(key ^ new_last)].push((key, value));
                }
            }
            self.len -= 1;
            Some(self.stacks[0].pop().unwrap())
        }
    }
    fn index(x: u32) -> usize {
        RADIX_HEAP_LEN - x.leading_zeros() as usize
    }
}

impl<T: Debug> Default for RadixHeap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Debug> Debug for RadixHeap<T> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        w.debug_list()
            .entries(self.stacks.iter().flatten())
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use {
        rand::prelude::*,
        std::{cmp::Reverse, collections::BinaryHeap},
    };

    #[test]
    fn test_heap() {
        let mut rng = StdRng::seed_from_u64(42);
        let mut binary = BinaryHeap::new();
        let mut radix = super::RadixHeap::new();
        for _ in 0..30 {
            match rng.gen_range(0..2) {
                0 => {
                    let key =
                        binary.peek().map_or(0, |&(Reverse(key), _)| key) + rng.gen_range(0..128);
                    let value = rng.gen_range(0..30);
                    binary.push((Reverse(key), value));
                    radix.push(key, value);
                }
                1 => {
                    let expected = binary.pop();
                    let result = radix.pop();
                    if let Some((Reverse(expected), _)) = expected {
                        let (result, _) = result.unwrap();
                        assert_eq!(result, expected);
                    } else {
                        assert!(result.is_none());
                    }
                }
                _ => unreachable!(),
            }
        }
    }
}
