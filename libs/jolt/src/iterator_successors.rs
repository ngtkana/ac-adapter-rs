/// `Iterator` に `successors` 風の逐次計算を追加するトレイト。
pub trait IteratorSuccessors: Iterator {
    /// `self` の要素を使って次の値を計算する、[`std::iter::successors`] 風のイテレータを作る。
    ///
    /// `std::iter::successors` は直前の値だけから次の値を計算するが、こちらは加えて
    /// `self` から 1 つずつ要素を取り出して計算に使う。
    ///
    /// # 仕様
    ///
    /// `self` を $a_0, a_1, \ldots, a_{n-1}$、`first` を $b_0$ とし、
    /// $b_{i+1} = \mathrm{succ}(a_i, b_i)$ で定まる列 $b_0, b_1, \ldots$ を返す
    /// （`succ` が `None` を返すか `self` が尽きたら終了）。
    ///
    /// # 例
    ///
    /// ```
    /// # use jolt::IteratorSuccessors;
    /// let a = (1..=3)
    ///     .successors(Some([0]), |x, &[y]| Some([x + y]))
    ///     .collect::<Vec<_>>();
    /// assert_eq!(a.as_slice(), &[[0], [1], [3], [6]]);
    /// ```
    fn successors<T, F>(self, first: Option<T>, succ: F) -> IterSuccessors<Self, T, F>
    where
        Self: Sized,
        F: FnMut(Self::Item, &T) -> Option<T>,
    {
        IterSuccessors {
            iter: self,
            next: first,
            succ,
        }
    }
}
impl<I: Iterator> IteratorSuccessors for I {}

/// [`IteratorSuccessors::successors`] が返すイテレータ。
pub struct IterSuccessors<I, T, F> {
    iter: I,
    next: Option<T>,
    succ: F,
}
impl<I, T, F> Iterator for IterSuccessors<I, T, F>
where
    I: Iterator,
    F: FnMut(I::Item, &T) -> Option<T>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.next.take()?;
        let next2 = self.iter.next().and_then(|x| (self.succ)(x, &item));
        self.next = next2;
        Some(item)
    }
}
