use std::{
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
};

/// Formats a two-dimensional slice in table style.
///
/// [See `Table` to customize the format](Table).
///
/// # Example
///
/// Basic usage:
/// ```
/// use dbg::table;
///
/// assert_eq!(
///     format!("{:?}", table(&[vec![0, 1], vec![2, 3333, 4]])),
///     "00| 0 1\n\
///      01| 2 3333 4\n"
/// );
/// ```
pub fn table<'a, T, U>(table: &'a [U]) -> Table<'a, T, U> {
    Table {
        _marker: PhantomData,
        table,
    }
}

/// An object created by a function [`table`](`self::table`).
pub struct Table<'a, T, U> {
    table: &'a [U],
    _marker: PhantomData<T>,
}
impl<'a, T, U> Clone for Table<'a, T, U> {
    fn clone(&self) -> Self {
        Self {
            table: self.table,
            _marker: PhantomData,
        }
    }
}
impl<'a, T, U> Copy for Table<'a, T, U> {}
impl<'a, T, U> Debug for Table<'a, T, U>
where
    T: Debug,
    U: AsRef<[T]>,
{
    fn fmt(&self, w: &mut Formatter) -> fmt::Result {
        write!(w, "{:?}", self.by(|cell| format!("{:?}", cell)))
    }
}
impl<'a, T, U> Table<'a, T, U> {
    /// Customize the format of cells.
    ///
    /// # Example
    ///
    /// Basic usage:
    /// ```
    /// use dbg::table;
    ///
    /// assert_eq!(
    ///     format!("{:?}", table(&[vec![0, 1], vec![2, 3333, 4]]).by(|cell| format!("{:4}", cell))),
    ///     "00|    0    1\n\
    ///      01|    2 3333    4\n"
    /// );
    /// ```
    pub fn by<F>(self, f: F) -> TableF<'a, T, U, F>
    where
        T: Debug,
        U: AsRef<[T]>,
        F: Fn(&T) -> String,
    {
        TableF {
            _marker: PhantomData,
            table: self.table,
            f,
        }
    }
}

pub struct TableF<'a, T, U, F> {
    pub _marker: PhantomData<T>,
    pub table: &'a [U],
    pub f: F,
}
impl<'a, T, U, F: Clone> Clone for TableF<'a, T, U, F> {
    fn clone(&self) -> Self {
        Self {
            table: self.table,
            _marker: PhantomData,
            f: self.f.clone(),
        }
    }
}
impl<'a, T, U, F: Copy> Copy for TableF<'a, T, U, F> {}
impl<'a, T, U, F> Debug for TableF<'a, T, U, F>
where
    T: Debug,
    U: AsRef<[T]>,
    F: Fn(&T) -> String,
{
    fn fmt(&self, w: &mut Formatter) -> fmt::Result {
        self.table
            .iter()
            .enumerate()
            .map(|(row_index, row)| {
                writeln!(
                    w,
                    "{:02}|{}",
                    row_index,
                    row.as_ref()
                        .iter()
                        .map(|cell| format!(" {}", (&self.f)(cell)))
                        .collect::<String>()
                )
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use {super::table, test_case::test_case};

    #[test_case(&[] => "")]
    #[test_case(&[Vec::new()] => "00|\n")]
    #[test_case(&[vec![0]] => "00| 0\n")]
    #[test_case(&[vec![0, 1]] => "00| 0 1\n")]
    #[test_case(&[vec![0, 1], Vec::new()] => "00| 0 1\n01|\n")]
    #[test_case(&[vec![0, 1], vec![2, 3], vec![4]] => "00| 0 1\n01| 2 3\n02| 4\n")]
    fn test_table(slice: &[Vec<i32>]) -> String {
        format!("{:?}", table(slice))
    }

    #[test_case(&[], 4 => "")]
    #[test_case(&[Vec::new()], 4 => "00|\n")]
    #[test_case(&[vec![0]], 4 => "00|    0\n")]
    #[test_case(&[vec![0, 1]], 4 => "00|    0    1\n")]
    #[test_case(&[vec![0, 1], Vec::new()], 4 => "00|    0    1\n01|\n")]
    #[test_case(&[vec![0, 1], vec![2, 3], vec![4]], 4 => "00|    0    1\n01|    2    3\n02|    4\n")]
    fn test_table_by_width(slice: &[Vec<i32>], width: usize) -> String {
        format!(
            "{:?}",
            table(slice).by(|cell| format!("{:1$}", cell, width))
        )
    }
}
