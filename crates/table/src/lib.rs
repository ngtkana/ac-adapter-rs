//! Format `Vec<Vec<T>>` etc. in a table style.
//!
//!
//! # Example
//!
//! ```
//! # use table::{table, Table};
//! let a = vec![
//!     vec![0, 1, 2],
//!     vec![3, 4, 5],
//! ];
//!
//! let result = format!(
//!     "{:?}",
//!     table(&a) // Either a or &a is ok.
//!         .heading_newlines(1) // Default: 1
//!         .index_width(1) // Default: 2
//!         .column_width(2), // Default: 3
//! );
//!
//! let expected = r#"
//!  | 0 1 2
//! --------
//! 0| 0 1 2
//! 1| 3 4 5
//! "#;
//!
//! assert_eq!(result, expected);
//! ```
//!
//!
//! # Automatic quieting
//!
//! ```
//! # use table::{table, Table};
//! let result = format!(
//!     "{:?}",
//!     table(&[
//!         [0, 2147483647, 2],
//!         [3, 4, 5],
//!     ]),
//! );
//!
//! let expected = r#"
//!   |  0  1  2
//! ------------
//!  0|  0  *  2
//!  1|  3  4  5
//! "#;
//!
//! assert_eq!(result, expected);
//! ```
//!

use std::{fmt::Debug, marker::PhantomData};

/// A builder type.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Table<T, Row, Storage> {
    __marker: PhantomData<(T, Row)>,
    storage: Storage,
    index_width: usize,
    column_width: usize,
    heading_newlines: usize,
}
/// A fuctory function.
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
    /// Create a new table. You also can use [`table()`]
    pub fn new(storage: Storage) -> Self {
        Self {
            __marker: PhantomData,
            storage,
            column_width: 3,
            index_width: 2,
            heading_newlines: 1,
        }
    }
    /// Change the width of the index column.
    pub fn index_width(&mut self, index_width: usize) -> &mut Self {
        self.index_width = index_width;
        self
    }
    /// Change the width of value columns.
    pub fn column_width(&mut self, column_width: usize) -> &mut Self {
        self.column_width = column_width;
        self
    }
    /// Change the number of newlines on the head.
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
            storage,
            index_width,
            column_width,
            heading_newlines,
        } = self;
        for _ in 0..*heading_newlines {
            writeln!(f)?;
        }
        let ncols = storage.as_ref()[0].as_ref().len();
        writeln!(
            f,
            "{:index_width$}|{}",
            "",
            (0..ncols)
                .map(|j| format!("{:column_width$}", j))
                .collect::<String>()
        )?;
        writeln!(f, "{}", "-".repeat(index_width + 1 + column_width * ncols))?;
        for (i, row) in storage.as_ref().iter().enumerate() {
            writeln!(
                f,
                "{:index_width$}|{}",
                i,
                row.as_ref()
                    .iter()
                    .map(|value| {
                        let s = format!("{:column_width$?}", value);
                        if matches!(
                            s.as_str(),
                            "18446744073709551615"
                                | "9223372036854775807"
                                | "-9223372036854775808"
                                | "4294967295"
                                | "-4294967296"
                                | "2147483647"
                        ) {
                            format!("{:>column_width$}", '*')
                        } else {
                            s
                        }
                    })
                    .collect::<String>()
            )?;
        }
        Ok(())
    }
}
