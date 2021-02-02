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
//! # Wrappers
//!
//! Provides various formats via `Display` trait.
//!
//! - [`BitSlice`]

mod bitslice;

pub use bitslice::BitSlice;

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
