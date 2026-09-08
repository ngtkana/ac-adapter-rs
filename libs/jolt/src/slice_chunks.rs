/// 述語で隣接要素をグループ化（chunk 化）するトレイト。
pub trait SliceChunks {
    /// スライスの要素型。
    type Item;
    /// 隣接する要素対が述語 $f$ を満たす限り、まとめて 1 つのチャンクにする。
    ///
    /// 標準ライブラリの `slice::chunk_by`（Rust 1.77.0 で安定化）と同じ仕様。
    ///
    /// # 例
    ///
    /// ```
    /// use riff::SliceChunks;
    /// let a = [1, 1, 2, 2, 2, 3];
    /// let chunks: Vec<&[i32]> = a.chunk_by(|x, y| x == y).collect();
    /// assert_eq!(chunks, vec![&[1, 1][..], &[2, 2, 2][..], &[3][..]]);
    /// ```
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

/// [`SliceChunks::chunk_by`] が返すイテレータ。
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
