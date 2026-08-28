//! 標準入力から型安全に構造化データを読み取るパーサーライブラリ。
//!
//! # 概要
//!
//! トークン単位での字句解析と、パーサーコンビネータを用いた型安全な解析を提供します。
//! 競技プログラミング向けに、$1$ つの `read()` 関数で複数の型を同時に読み取れます。
//!
//! # 例
//!
//! ```
//! use io_reader::{read, Usize, I32, Vector};
//!
//! // 入力："2 3 10 20 30"
//! // let n: usize = read(Usize);
//! // let m: usize = read(Usize);
//! // let v: Vec<i32> = read(Vector(I32, 3));
//! ```
//!
//! # パーサーの種類
//!
//! - **基本型**: `Char`, `Str`, `I32`, `U64`, など（`Canonical<T>` による）
//! - **列**: `Vector<P>` で $n$ 個の要素
//! - **配列**: `Array<N, P>` で長さ $N$ の配列
//! - **ペア**: `Tuple2<P0, P1>` で 2-tuple
//! - **特殊**: `Usize1` で 1-indexed usize、`Bools<Z, O>` で 0/1 文字列

use std::{
    fmt::Debug,
    io::{BufRead, BufReader, Stdin, stdin},
    marker::PhantomData,
    str::{FromStr, SplitWhitespace},
    sync::{Mutex, MutexGuard, OnceLock},
};

/// パーサーを用いて標準入力から値を読み取る。
///
/// # 例
///
/// ```
/// use io_reader::{read, I32};
/// // let x = read(I32);  // 標準入力から i32 を読む
/// ```
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

/// 入力ソースから行・トークン単位で読み取るリーダー。
///
/// 行単位で読み込み、空白で分割したトークンを提供します。
#[derive(Debug)]
pub struct Source<R: BufRead> {
    reader: R,
    line: String,
    tokens: SplitWhitespace<'static>,
}

impl<R: BufRead> Source<R> {
    /// 新しいソースを作成する。
    ///
    /// # 例
    ///
    /// ```
    /// use io_reader::Source;
    /// let source = Source::from("1 2 3");
    /// ```
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

    /// 次のトークンを読み取る。
    ///
    /// トークンが存在しなければ `None` を返す。
    ///
    /// # 例
    ///
    /// ```
    /// use io_reader::Source;
    /// let mut source = Source::from("hello world");
    /// assert_eq!(source.next_token(), Some("hello"));
    /// assert_eq!(source.next_token(), Some("world"));
    /// assert_eq!(source.next_token(), None);
    /// ```
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

    /// 次のトークンを読み取る。トークンが存在しなければパニックする。
    ///
    /// # 例
    ///
    /// ```
    /// use io_reader::Source;
    /// let mut source = Source::from("hello world");
    /// assert_eq!(source.next_token_unwrap(), "hello");
    /// assert_eq!(source.next_token_unwrap(), "world");
    /// // panic!("unexpected end of input.")
    /// ```
    pub fn next_token_unwrap(&mut self) -> &str {
        self.next_token()
            .unwrap_or_else(|| panic!("unexpected end of input."))
    }
}

impl<'a> From<&'a str> for Source<BufReader<&'a [u8]>> {
    /// 文字列から `Source` を構成する。
    fn from(value: &'a str) -> Self {
        Self::new(BufReader::new(value.as_bytes()))
    }
}

/// 入力ソースから値を解析するパーサー。
///
/// `Copy` 型であり、`read()` 関数から渡されます。
pub trait Parser: Copy {
    /// パーサーが解析する値の型。
    type Output;

    /// ソースから値を読み取り解析する。
    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output;
}

/// `FromStr` を実装する型の標準パーサー。
///
/// 次のトークンを文字列として取得し、`parse()` で型 `T` に変換します。
pub struct Canonical<T>(PhantomData<fn(T)>);
impl<T> Clone for Canonical<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for Canonical<T> {}

/// 型 `T` の標準パーサーを構成する。
///
/// # 例
///
/// ```
/// use io_reader::{canonical, Parser, Source};
/// let parser: _ = canonical::<i32>();
/// let mut source = Source::from("42");
/// assert_eq!(parser.read(&mut source), 42);
/// ```
pub const fn canonical<T>() -> Canonical<T> {
    Canonical(PhantomData)
}

macro_rules! define_cannonical_parser {
    ($($prim:ty => $cann:ident),+$(,)?) => {$(
        /// 型 [`
        #[doc = stringify!($prim)]
        /// `] の標準パーサー定数。
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

/// 1-indexed usize のパーサー。
///
/// 入力値から 1 を減じて返す。0 を入力したらパニックする。
///
/// # 例
///
/// ```
/// use io_reader::{Usize1, Parser, Source};
/// let mut source = Source::from("3");
/// assert_eq!(Usize1.read(&mut source), 2);
/// ```
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

/// パーサーを $n$ 回繰り返す。
///
/// `Vector(parser, n)` は `parser` を $n$ 回実行した結果を `Vec` で返す。
///
/// # 例
///
/// ```
/// use io_reader::{Vector, I32, Parser, Source};
/// let mut source = Source::from("1 2 3");
/// let v: Vec<i32> = Vector(I32, 3).read(&mut source);
/// assert_eq!(v, vec![1, 2, 3]);
/// ```
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

/// パーサーを $N$ 回繰り返し、長さ $N$ の配列を生成する。
///
/// `Array::<N, P>(parser)` は `parser` を $N$ 回実行した結果を配列で返す。
///
/// # 例
///
/// ```
/// use io_reader::{Array, I32, Parser, Source};
/// let mut source = Source::from("1 2 3");
/// let arr: [i32; 3] = Array::<3, _>(I32).read(&mut source);
/// assert_eq!(arr, [1, 2, 3]);
/// ```
#[derive(Clone, Copy)]
pub struct Array<const N: usize, T>(pub T);
impl<const N: usize, T: Parser> Parser for Array<N, T> {
    type Output = [T::Output; N];

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        std::array::from_fn(|_| self.0.read(source))
    }
}

/// 2 つのパーサーから 2-tuple を構成する。
///
/// `Tuple2(parser0, parser1)` は順に `parser0` と `parser1` を実行し、結果をペアで返す。
///
/// # 例
///
/// ```
/// use io_reader::{Tuple2, I32, Parser, Source};
/// let mut source = Source::from("10 20");
/// let (x, y): (i32, i32) = Tuple2(I32, I32).read(&mut source);
/// assert_eq!((x, y), (10, 20));
/// ```
#[derive(Clone, Copy)]
pub struct Tuple2<T0, T1>(pub T0, pub T1);
impl<T0: Parser, T1: Parser> Parser for Tuple2<T0, T1> {
    type Output = (T0::Output, T1::Output);

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        (self.0.read(&mut *source), self.1.read(&mut *source))
    }
}

/// 2 つの指定文字で bool 列を解析する。
///
/// `Bools<Z, O>` は、文字 `Z` を false、`O` を true にマップして bool ベクトルに変換します。
///
/// # 例
///
/// ```
/// use io_reader::{Bools, Source, Parser};
///
/// let mut source = Source::from("..#.");
/// let result: Vec<bool> = Bools::<'.', '#'>.read(&mut source);
/// assert_eq!(result, vec![false, false, true, false]);
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
