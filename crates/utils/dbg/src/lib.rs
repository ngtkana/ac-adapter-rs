//! Provides print-debugging utilities.
//!
//! # Macros
//!
//! Prints arguments to STDERR with code position information.
//!
//! - [`lg`]
//! - [`msg`]
//!
//!
//! # Structs
//!
//! * [`BitSlice`] to format a slice of Boolean vales. Implements both `Debug` and `Display`.
//!
//!
//! # Functions
//!
//! * [`table()`] to format a two-dimensional table. Returns [`Table`], which implements `Debug`, and
//! allows customization of formats via [`by`](Table::by) method.
//!

mod bitslice;
mod table;

pub use {
    bitslice::BitSlice,
    table::{table, Table},
};

#[macro_export]
macro_rules! lg {
    (@nl $value:expr) => {
        eprintln!("[{}:{}]", file!(), line!());
        match $value {
            value => {
                eprint!("{:?}", &value);
            }
        }
    };
    (@contents $head:expr $(,)?) => {
        match $head {
            head => {
                eprintln!(" {} = {:?}", stringify!($head), &head);
            }
        }
    };
    (@contents $head:expr $(,$tail:expr)+ $(,)?) => {
        match $head {
            head => {
                eprint!(" {} = {:?},", stringify!($head), &head);
            }
        }
        $crate::lg!(@contents $($tail),*);
    };
    ($($expr:expr),* $(,)?) => {
        eprint!("[{}:{}]", file!(), line!());
        $crate::lg!(@contents $($expr),*)
    };
}
