/// Chunk by predicate.
pub trait SliceChunks {
    type Item;
    /// Groups adjacent elements by a predicate.
    /// (Rust 1.77.0)
    fn chunk_by<F>(&self, f: F) -> SliceChunkBy<'_, Self::Item, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> bool;
}
impl<T> SliceChunks for [T] {
    type Item = T;

    fn chunk_by<F>(&self, f: F) -> SliceChunkBy<'_, Self::Item, F>
    where
        F: FnMut(&Self::Item, &Self::Item) -> bool,
    {
        SliceChunkBy { a: self, f }
    }
}

pub struct SliceChunkBy<'a, T, F> {
    a: &'a [T],
    f: F,
}
impl<'a, T, F> Iterator for SliceChunkBy<'a, T, F>
where
    F: FnMut(&T, &T) -> bool,
{
    type Item = &'a [T];

    fn next(&mut self) -> Option<Self::Item> {
        let Self { a, f } = self;
        if a.is_empty() {
            return None;
        }
        let mut end = 1;
        while end < a.len() && f(&a[end - 1], &a[end]) {
            end += 1;
        }
        let (prefix, rest) = a.split_at(end);
        self.a = rest;
        Some(prefix)
    }
}
