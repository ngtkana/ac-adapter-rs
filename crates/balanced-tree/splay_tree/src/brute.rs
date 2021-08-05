use std::ops::Range;

#[derive(Clone, Debug, Default, Hash, PartialEq)]
pub struct Brute {
    pub vec: Vec<char>,
}
impl Brute {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.vec.len()
    }
    pub fn get(&self, index: usize) -> Option<&char> {
        self.vec.get(index)
    }
    pub fn fold_all_unwrap(&self) -> String {
        self.vec.iter().collect::<String>()
    }
    pub fn fold(&self, range: Range<usize>) -> Option<String> {
        let s = self.vec[range].iter().collect::<String>();
        if s.is_empty() {
            None
        } else {
            Some(s)
        }
    }
    pub fn push_back(&mut self, c: char) {
        self.vec.push(c);
    }
    pub fn push_front(&mut self, c: char) {
        self.vec.insert(0, c);
    }
    pub fn insert(&mut self, i: usize, c: char) {
        self.vec.insert(i, c);
    }
    pub fn pop_back(&mut self) -> Option<char> {
        self.vec.pop()
    }
    pub fn pop_front(&mut self) -> Option<char> {
        if self.vec.is_empty() {
            None
        } else {
            Some(self.vec.remove(0))
        }
    }
    pub fn delete(&mut self, i: usize) -> char {
        self.vec.remove(i)
    }
}
