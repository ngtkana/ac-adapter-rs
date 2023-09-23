/// Provids utility on stdin.
use std::{
    cell::Cell,
    convert::TryFrom,
    io::{stdin, BufRead, BufReader, Lines, Stdin},
    str::FromStr,
    sync::{Mutex, Once},
};

type Server = Mutex<Lines<BufReader<Stdin>>>;
static ONCE: Once = Once::new();
pub struct Lazy(Cell<Option<Server>>);
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
pub trait ForceFromStr: FromStr {
    fn force_from_str(s: &str) -> Self;
}
impl<T, E> ForceFromStr for T
where
    T: FromStr<Err = E>,
    E: std::fmt::Debug,
{
    fn force_from_str(s: &str) -> Self {
        s.parse().unwrap()
    }
}
/// Read a line from stdin and from_str to [T; N].
pub fn input_array<T: ForceFromStr, const N: usize>() -> [T; N]
where
    T: std::fmt::Debug,
{
    <[_; N]>::try_from(input_vec()).unwrap()
}
/// Read a line from stdin and from_str to Vec<T>.
pub fn input_vec<T: ForceFromStr>() -> Vec<T> {
    line()
        .split_whitespace()
        .map(T::force_from_str)
        .collect::<Vec<_>>()
}
/// Read a line from stdin and from_str to T.
pub fn input<T: ForceFromStr>() -> T {
    T::force_from_str(&line())
}
