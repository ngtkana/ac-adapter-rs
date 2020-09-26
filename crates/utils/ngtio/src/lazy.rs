use std::{cell::Cell, sync::Once};

pub struct Lazy<T: Sync>(Cell<Option<T>>, Once);

impl<T: Sync> Lazy<T> {
    pub const INIT: Self = Lazy(Cell::new(None), Once::new());

    pub fn get<F>(&self, f: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.1.call_once(|| {
            self.0.set(Some(f()));
        });
        unsafe {
            match *self.0.as_ptr() {
                Some(ref x) => x,
                None => unreachable!(),
            }
        }
    }
}

unsafe impl<T: Sync> Sync for Lazy<T> {}

impl<T: Sync> Default for Lazy<T> {
    fn default() -> Self {
        Self::INIT
    }
}
