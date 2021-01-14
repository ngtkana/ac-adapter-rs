/// `on_stack` が線形でできるスタックができます。
#[derive(Debug, Clone)]
pub struct WhiteStack {
    pub on_stack: Vec<bool>,
    pub stack: Vec<usize>,
}

impl WhiteStack {
    pub fn new(len: usize) -> Self {
        Self {
            on_stack: vec![false; len],
            stack: Vec::with_capacity(len),
        }
    }

    pub fn push(&mut self, i: usize) {
        assert!(i < self.on_stack.len());
        assert!(!self.on_stack[i]);
        self.on_stack[i] = true;
        self.stack.push(i);
    }

    pub fn pop(&mut self) -> Option<usize> {
        if let Some(i) = self.stack.pop() {
            assert!(self.on_stack[i]);
            Some(i)
        } else {
            None
        }
    }

    pub fn peek(&self) -> Option<&usize> {
        self.stack.last()
    }
}
