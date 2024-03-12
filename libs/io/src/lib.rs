//! Read input from stdin and parse it.
//!
//! # Example
//!
//! ```[no_run]
//! # use io::input;
//! let (a, b): (i32, i32) = input();
//! let a: Vec<i32> = input();
//! ```
//!
//! # Types that can be parsed
//! - primitive integer types ([`u8`], [`u16`], [`u32`], [`u64`], [`u128`], [`usize`], [`i8`], [`i16`], [`i32`], [`i64`], [`i128`], [`isize`])
//! - [`String`], [`char`]
//! - tuples (up to 10 elements)
//! - vectors

use std::cell::Cell;
use std::io::stdin;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Lines;
use std::io::Stdin;
use std::sync::Mutex;
use std::sync::Once;

/// Read input from stdin and parse it.
pub fn input<T: ParseLine>() -> T {
    ParseLine::parse_line(&line())
}

/// Trait for types that can be parsed.
pub trait ParseLine {
    fn parse_line(s: &str) -> Self;
}

macro_rules! impl_parse_line {
    ($($t:ty),*) => {
        $(impl ParseLine for $t {
            fn parse_line(s: &str) -> Self {
                s.parse().unwrap()
            }
        })*
    };
}
impl_parse_line!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, String, char);
macro_rules! impl_parse_line_tuple {
    ($($t:ident),*) => {
        impl<$($t: ParseLine),*> ParseLine for ($($t,)*) {
            fn parse_line(s: &str) -> Self {
                let mut s = s.split_whitespace();
                ($($t::parse_line(s.next().unwrap()),)*)
            }
        }
    };
}
impl_parse_line_tuple!(T0, T1);
impl_parse_line_tuple!(T0, T1, T2);
impl_parse_line_tuple!(T0, T1, T2, T3);
impl_parse_line_tuple!(T0, T1, T2, T3, T4);
impl_parse_line_tuple!(T0, T1, T2, T3, T4, T5);
impl_parse_line_tuple!(T0, T1, T2, T3, T4, T5, T6);
impl_parse_line_tuple!(T0, T1, T2, T3, T4, T5, T6, T7);
impl_parse_line_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8);
impl_parse_line_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);
impl<T: ParseLine> ParseLine for Vec<T> {
    fn parse_line(s: &str) -> Self {
        s.split_whitespace().map(T::parse_line).collect()
    }
}

static ONCE: Once = Once::new();
type Server = Mutex<Lines<BufReader<Stdin>>>;
struct Lazy(Cell<Option<Server>>);
unsafe impl Sync for Lazy {}
fn line() -> String {
    static SYNCER: Lazy = Lazy(Cell::new(None));
    ONCE.call_once(|| {
        SYNCER
            .0
            .set(Some(Mutex::new(BufReader::new(stdin()).lines())));
    });
    unsafe {
        (*SYNCER.0.as_ptr())
            .as_ref()
            .unwrap()
            .lock()
            .unwrap()
            .next()
            .unwrap()
            .unwrap()
    }
}
