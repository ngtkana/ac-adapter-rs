//! Provides a macro [`lg`] and formatting utils.
use std::borrow::Borrow;
use std::{fmt::Debug, marker::PhantomData};

#[macro_export]
macro_rules! lg {
    (@contents $head:expr $(, $tail:expr)*) => {{
        $crate::__lg_variable!($head);
        $(
            eprint!(",");
            $crate::__lg_variable!($tail);
        )*
        eprintln!();
    }};
    ($($expr:expr),* $(,)?) => {{
        eprint!("[{}:{}]", file!(), line!());
        $crate::lg!(@contents $($expr),*)
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! __lg_variable {
    ($value:expr) => {{
        match $value {
            head => {
                eprint!(
                    " {} = {}",
                    stringify!($value),
                    $crate::__quiet(format!("{:?}", &head))
                );
            }
        }
    }};
}

#[doc(hidden)]
pub fn __quiet(s: impl AsRef<str>) -> String {
    s.as_ref()
        .replace("18446744073709551615", "*") // u64
        .replace("9223372036854775807", "*") // i64
        .replace("-9223372036854775808", "*") // i64
        .replace("4294967295", "*") // u32
        .replace("2147483647", "*") // i32
        .replace("-2147483648", "*") // i32
        .replace("None", "*")
        .replace("Some", "")
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Table<T, Row, Storage> {
    __marker: PhantomData<(T, Row)>,
    storage: Storage,
    index_width: usize,
    column_width: usize,
    heading_newlines: usize,
}

/// Format a two dimensional container in a table style.
///
///
/// # Example
///
/// ```
/// # use lg::{table, Table};
/// let a = vec![
///     vec![0, 1, 2],
///     vec![3, 4, 5],
/// ];
///
/// let result = format!(
///     "{:?}",
///     table(&a) // Either a or &a is ok.
///         .heading_newlines(1) // Default: 1
///         .index_width(1) // Default: 2
///         .column_width(2), // Default: 3
/// );
///
/// let expected = r#"
///  | 0 1 2
/// --------
/// 0| 0 1 2
/// 1| 3 4 5
/// "#;
///
/// assert_eq!(result, expected);
/// ```
///
///
/// # Automatic quieting
///
/// ```
/// # use lg::{table, Table};
/// let result = format!(
///     "{:?}",
///     table(&[
///         [0, 2147483647, 2],
///         [3, 4, 5],
///     ]),
/// );
///
/// let expected = r#"
///   |  0  1  2
/// ------------
///  0|  0  *  2
///  1|  3  4  5
/// "#;
///
/// assert_eq!(result, expected);
/// ```
pub fn table<T: Clone + Debug, Row: AsRef<[T]>, Storage: AsRef<[Row]>>(
    storage: Storage,
) -> Table<T, Row, Storage> {
    Table::new(storage)
}
impl<T, Row, Storage> Table<T, Row, Storage>
where
    T: Clone + Debug,
    Row: AsRef<[T]>,
    Storage: AsRef<[Row]>,
{
    pub fn new(storage: Storage) -> Self {
        Self {
            __marker: PhantomData,
            storage,
            column_width: 3,
            index_width: 2,
            heading_newlines: 1,
        }
    }
    pub fn index_width(&mut self, index_width: usize) -> &mut Self {
        self.index_width = index_width;
        self
    }
    pub fn column_width(&mut self, column_width: usize) -> &mut Self {
        self.column_width = column_width;
        self
    }
    pub fn heading_newlines(&mut self, heading_newlines: usize) -> &mut Self {
        self.heading_newlines = heading_newlines;
        self
    }
}
impl<T, Row, Storage> Debug for Table<T, Row, Storage>
where
    T: Clone + Debug,
    Row: AsRef<[T]>,
    Storage: AsRef<[Row]>,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self {
            __marker: _,
            ref storage,
            index_width,
            column_width,
            heading_newlines,
        } = *self;
        for _ in 0..heading_newlines {
            writeln!(f)?;
        }
        let ncols = storage.as_ref()[0].as_ref().len();
        write!(f, "{}|", " ".repeat(index_width))?;
        for j in 0..ncols {
            write!(f, "{:column_width$}", j, column_width = column_width)?;
        }
        writeln!(f)?;
        writeln!(f, "{}", "-".repeat(index_width + 1 + column_width * ncols))?;
        for (i, row) in storage.as_ref().iter().enumerate() {
            write!(f, "{:index_width$}|", i, index_width = index_width)?;
            for value in row.as_ref() {
                write!(
                    f,
                    "{:>column_width$}",
                    __quiet(format!("{:?}", value)),
                    column_width = column_width,
                )?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

/// Format a iterator of [`bool`]s.
pub fn bools<B, I>(iter: I) -> String
where
    B: Borrow<bool>,
    I: IntoIterator<Item = B>,
{
    format!(
        "[{}]",
        iter.into_iter()
            .map(|b| ['.', '#'][usize::from(*(b.borrow()))])
            .collect::<String>(),
    )
}

#[cfg(test)]
mod test {
    use super::*;
    use std::{collections::BTreeSet, iter::empty};

    #[test]
    fn test_invoke_lg() {
        let x = 42;
        let y = 43;
        lg!(x);
        lg!(x, y);
        lg!(42, x, 43, y);
    }

    #[test]
    fn test_quiet() {
        assert_eq!(__quiet(std::u32::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i32::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i32::MIN.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::u64::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i64::MAX.to_string()).as_str(), "*");
        assert_eq!(__quiet(std::i64::MIN.to_string()).as_str(), "*");
        assert_eq!(__quiet(format!("{:?}", Some(42))).as_str(), "(42)");
        assert_eq!(__quiet(format!("{:?}", None::<i32>)).as_str(), "*");
    }

    #[test]
    fn test_table() {
        fn format<const H: usize, const W: usize>(a: [[i32; W]; H]) -> String {
            format!(
                "{:?}",
                table(a).heading_newlines(1).index_width(2).column_width(3)
            )
        }
        assert_eq!(
            format([[0, std::i32::MIN, 2], [3, 4, 5]]),
            r#"
  |  0  1  2
------------
 0|  0  *  2
 1|  3  4  5
"#
        );
    }

    #[test]
    fn test_bools_format() {
        assert_eq!(bools([false]).as_str(), "[.]");
        assert_eq!(bools([true]).as_str(), "[#]");
        assert_eq!(bools([false, true]).as_str(), "[.#]");
        assert_eq!(bools([true, false]).as_str(), "[#.]");
    }

    #[test]
    fn test_bools_generics() {
        assert_eq!(bools(<[bool; 0]>::default()).as_str(), "[]");
        assert_eq!(bools(<[bool; 0]>::default()).as_str(), "[]");
        assert_eq!(bools(<[&bool; 0]>::default()).as_str(), "[]");
        assert_eq!(bools(<[bool; 0]>::default().as_slice()).as_str(), "[]");
        assert_eq!(bools(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<&bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<&mut bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(Vec::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(BTreeSet::<bool>::new()).as_str(), "[]");
        assert_eq!(bools(empty::<bool>()).as_str(), "[]");
        assert_eq!(bools(empty::<bool>()).as_str(), "[]");
        assert_eq!(bools(empty::<&bool>()).as_str(), "[]");
        assert_eq!(bools(empty::<&bool>()).as_str(), "[]");
    }
}
