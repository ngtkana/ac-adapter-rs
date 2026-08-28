use std::{
    fmt::Debug,
    io::{BufRead, BufReader, Stdin, stdin},
    marker::PhantomData,
    str::{FromStr, SplitWhitespace},
    sync::{Mutex, MutexGuard, OnceLock},
};

pub fn read<T: Parser>(parser: T) -> T::Output {
    parser.read(&mut source())
}

fn source() -> MutexGuard<'static, Source<BufReader<Stdin>>> {
    SOURCE
        .get_or_init(|| Mutex::new(Source::new(BufReader::new(stdin()))))
        .lock()
        .unwrap()
}

static SOURCE: OnceLock<Mutex<Source<BufReader<Stdin>>>> = OnceLock::new();

pub struct Source<R: BufRead> {
    reader: R,
    line: String,
    tokens: SplitWhitespace<'static>,
}

impl<R: BufRead> Source<R> {
    pub fn new(reader: R) -> Self {
        let line = String::new();
        let tokens = unsafe {
            std::mem::transmute::<std::str::SplitWhitespace<'_>, std::str::SplitWhitespace<'_>>(
                line.split_whitespace(),
            )
        };
        Self {
            reader,
            line,
            tokens,
        }
    }

    pub fn next_token(&mut self) -> Option<&str> {
        loop {
            if let Some(result) = self.tokens.next() {
                return Some(result);
            }
            let mut line = String::new();
            if self.reader.read_line(&mut line).unwrap() == 0 {
                return None;
            }
            self.line = line;
            self.tokens = unsafe {
                std::mem::transmute::<std::str::SplitWhitespace<'_>, std::str::SplitWhitespace<'_>>(
                    self.line.split_whitespace(),
                )
            };
        }
    }

    pub fn next_token_unwrap(&mut self) -> &str {
        self.next_token()
            .unwrap_or_else(|| panic!("unexpected end of input."))
    }
}

impl<'a> From<&'a str> for Source<BufReader<&'a [u8]>> {
    fn from(value: &'a str) -> Self {
        Self::new(BufReader::new(value.as_bytes()))
    }
}

pub trait Parser: Copy {
    type Output;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output;
}

pub struct Canonical<T>(PhantomData<fn(T)>);
impl<T> Clone for Canonical<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Canonical<T> {}

pub const fn canonical<T>() -> Canonical<T> {
    Canonical(PhantomData)
}

macro_rules! define_cannonical_parser {
    ($($prim:ty => $cann:ident),+$(,)?) => {$(
        /// Cannonical parser for [`
        #[doc = stringify!($prim)]
        /// `].
        #[allow(non_upper_case_globals)]
        pub const $cann: Canonical<$prim> = canonical::<$prim>();
    )+}
}

define_cannonical_parser! {
    char => Char,
    String => Str,
    u8 => U8,
    u16 => U16,
    u32 => U32,
    u64 => U64,
    u128 => U128,
    usize => Usize,
    i8 => I8,
    i16 => I16,
    i32 => I32,
    i64 => I64,
    i128 => I128,
    isize => Isize,
}

impl<T: FromStr> Parser for Canonical<T>
where
    T::Err: Debug,
{
    type Output = T;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        let token = source.next_token_unwrap();
        token.parse().unwrap_or_else(|e| {
            panic!(
                "failed to parse the token `{token}` to the value of type `{ty}`: {e:?}.",
                ty = std::any::type_name::<T>()
            )
        })
    }
}

#[derive(Clone, Copy)]
pub struct Usize1;
impl Parser for Usize1 {
    type Output = usize;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        Canonical::<usize>(PhantomData)
            .read(source)
            .checked_sub(1)
            .unwrap_or_else(|| panic!("expected `Usize1` but got 0"))
    }
}

#[derive(Clone, Copy)]
pub struct Vector<T>(pub T, pub usize);
impl<T: Parser> Parser for Vector<T> {
    type Output = std::vec::Vec<T::Output>;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        std::iter::repeat_with(|| self.0.read(source))
            .take(self.1)
            .collect()
    }
}

#[derive(Clone, Copy)]
pub struct Array<const N: usize, T>(pub T);
impl<const N: usize, T: Parser> Parser for Array<N, T> {
    type Output = [T::Output; N];

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        std::array::from_fn(|_| self.0.read(source))
    }
}

#[derive(Clone, Copy)]
pub struct Tuple2<T0, T1>(pub T0, pub T1);
impl<T0: Parser, T1: Parser> Parser for Tuple2<T0, T1> {
    type Output = (T0::Output, T1::Output);

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        (self.0.read(&mut *source), self.1.read(&mut *source))
    }
}

/// Parser for `Vec<bool>` that specified characters `Z` and `O`, each of which corresponding to 0 and 1.
///
/// # Example
///
/// ```
/// use io_reader::{Bools, Source, Parser, read};
///
/// let mut source = Source::from("..#.");
/// let result = Bools::<'.', '#'>.read(&mut source);
///
/// assert_eq!(result, [false, false, true, false]);
/// ```
#[derive(Clone, Copy)]
pub struct Bools<const Z: char, const O: char>;
impl<const Z: char, const O: char> Parser for Bools<Z, O> {
    type Output = Vec<bool>;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        source
            .next_token_unwrap()
            .chars()
            .map(|c| {
                if c == Z {
                    false
                } else if c == O {
                    true
                } else {
                    panic!("unexpected charactor {c} in parsing `Bools<{Z}, {O}>`");
                }
            })
            .collect()
    }
}
