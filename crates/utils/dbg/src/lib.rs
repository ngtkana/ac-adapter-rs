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
    () => {
        $crate::eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
    };
    ($val:expr) => {
        match $val {
            tmp => {
                eprintln!("[{}:{}] {} = {:?}",
                    file!(), line!(), stringify!($val), &tmp);
                tmp
            }
        }
    };
    ($val:expr,) => { $crate::lg!($val) };
    ($($val:expr),+ $(,)?) => {
        ($($crate::lg!($val)),+,)
    };
}

#[macro_export]
macro_rules! msg {
    () => {
        compile_error!();
    };
    ($msg:expr) => {
        $crate::eprintln!("[{}:{}][{}]", $crate::file!(), $crate::line!(), $msg);
    };
    ($msg:expr, $val:expr) => {
        match $val {
            tmp => {
                eprintln!("[{}:{}][{}] {} = {:?}",
                    file!(), line!(), $msg, stringify!($val), &tmp);
                tmp
            }
        }
    };
    ($msg:expr, $val:expr,) => { msg!($msg, $val) };
    ($msg:expr, $($val:expr),+ $(,)?) => {
        ($(msg!($msg, $val)),+,)
    };
}
