/// 比較のみで最小値・最大値に更新するトレイト。
///
/// `PartialOrd` を実装する全ての型に自動実装される。
pub trait ChangeMinMax: PartialOrd + Sized {
    /// $\mathrm{self} \gets \min(\mathrm{self}, \mathrm{rhs})$ に更新する。
    ///
    /// # 例
    ///
    /// ```
    /// use jolt::ChangeMinMax;
    /// let mut x = 5;
    /// x.change_min(3);
    /// assert_eq!(x, 3);
    /// x.change_min(10);
    /// assert_eq!(x, 3);
    /// ```
    fn change_min(&mut self, rhs: Self) {
        if *self > rhs {
            *self = rhs;
        }
    }

    /// $\mathrm{self} \gets \max(\mathrm{self}, \mathrm{rhs})$ に更新する。
    ///
    /// # 例
    ///
    /// ```
    /// use jolt::ChangeMinMax;
    /// let mut x = 5;
    /// x.change_max(10);
    /// assert_eq!(x, 10);
    /// x.change_max(3);
    /// assert_eq!(x, 10);
    /// ```
    fn change_max(&mut self, rhs: Self) {
        if *self < rhs {
            *self = rhs;
        }
    }
}

impl<T: PartialOrd + Sized> ChangeMinMax for T {}
