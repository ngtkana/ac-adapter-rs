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
macro_rules! lg_nl {
    () => {
        eprintln!("[{}:{}]", $crate::file!(), $crate::line!());
    };
    ($val:expr) => {
        match $val {
            tmp => {
                eprintln!("[{}:{}] {}:\n{:?}", file!(), line!(), stringify!($val), tmp);
                tmp
            }
        };
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

#[macro_export]
macro_rules! tabular {
    ($val:expr) => {
        $crate::lg_nl!(crate::dbg::Tabular($val))
    };
}

#[macro_export]
macro_rules! boolean_table {
    ($val:expr) => {
        $crate::lg_nl!(crate::dbg::BooleanTable($val));
    };
}

#[macro_export]
macro_rules! boolean_slice {
    ($val:expr) => {
        $crate::lg!(crate::dbg::BooleanSlice($val));
    };
}

use std::fmt::{Debug, Formatter};

#[derive(Clone)]
pub struct Tabular<'a, T: Debug>(pub &'a [T]);
impl<'a, T: Debug> Debug for Tabular<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for i in 0..self.0.len() {
            writeln!(f, "{:2} | {:?}", i, &self.0[i])?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct BooleanTable<'a>(pub &'a [Vec<bool>]);
impl<'a> Debug for BooleanTable<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        for i in 0..self.0.len() {
            writeln!(f, "{:2} | {:?}", i, BooleanSlice(&self.0[i]))?;
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct BooleanSlice<'a>(pub &'a [bool]);
impl<'a> Debug for BooleanSlice<'a> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.0
                .iter()
                .map(|&b| if b { "1 " } else { "0 " })
                .collect::<String>()
        )?;
        Ok(())
    }
}
