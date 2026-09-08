//! 空白区切りの標準入力・文字列を型安全にパースする。
//!
//! `input!` マクロの右辺には型ではなく [`Parser`] trait を実装した**値**を書き、それらを組み合わせて
//! 複合的なパーサーを作る。入力元は [`BufRead`] を実装した型を [`Source`] でラップして与え、
//! 省略時は標準入力（[`stdin_source`]）、テストでは文字列（[`Source::from`]）を使うのが典型的。
//!
//! # 仕様
//!
//! - `input! { pat = parser, ... }`: 標準入力から読み取り `pat` に束縛
//! - `input! { from expr, pat = parser, ... }`: `expr`（[`Source`] に変換可能な値）から読み取り
//! - パーサーの種類:
//!   - 基本型: [`Char`], [`Str`], [`I32`], [`U64`] など（`Canonical<P>` により [`FromStr`] へ委譲）
//!   - 列: [`Vector<P>`] で長さ $n$ の `Vec`
//!   - 配列: [`Array<N, P>`] で長さ $N$ の配列
//!   - タプル: `(P0, P1, ...)` で複数要素をまとめて読み取り
//!   - 特殊: [`Usize1`]（1-indexed → 0-indexed）、[`Bools<Z, O>`]（0/1 文字列）、[`Bytes`]（バイト列）、[`Expect`]（固定トークンの検証）
//!
//! # 例
//!
//! ```
//! use io_reader::{input, Usize, I32, Vector};
//!
//! input! {
//! #   from "2 3 10 20 30",
//!     n = Usize,
//!     m = Usize,
//!     a = Vector(I32, 3),
//! }
//! # assert_eq!(n, 2);
//! # assert_eq!(m, 3);
//! # assert_eq!(a, [10, 20, 30]);
//! ```

use std::{
    fmt::Debug,
    io::{BufRead, BufReader, Stdin, stdin},
    marker::PhantomData,
    str::{FromStr, SplitWhitespace},
    sync::{Mutex, MutexGuard, OnceLock},
};

static STDIN_SOURCE: OnceLock<Mutex<Source<BufReader<Stdin>>>> = OnceLock::new();

/// プロセス全体で共有する標準入力の [`Source`] を取得する。
///
/// 実体は [`OnceLock<Mutex<_>>`] に包まれた `static` で、初回呼び出し時に遅延初期化する。
/// 返り値は [`MutexGuard`] なので、drop されるまでロックを保持する。
pub fn stdin_source() -> MutexGuard<'static, Source<BufReader<Stdin>>> {
    STDIN_SOURCE
        .get_or_init(|| Mutex::new(Source::new(BufReader::new(stdin()))))
        .lock()
        .unwrap()
}

/// 入力をパースして変数に束縛する。
///
/// 右辺には型ではなく [`Parser`] の値を書く。`pat = parser` をコンマ区切りで並べると、書いた順に
/// 読み取って束縛する。`from` 節を省略すると標準入力（[`stdin_source`]）から読み取る。
///
/// # 仕様
///
/// - `input! { pat = parser, ... }`: 標準入力から読み取り
/// - `input! { from expr, pat = parser, ... }`: `expr`（[`Source`] に変換可能な値）から読み取り
///
/// # 例
///
/// ```
/// use io_reader::{input, U32, Str};
///
/// input! {
///     from "42 abc",
///     x = U32,
///     s = Str,
/// }
/// assert_eq!(x, 42);
/// assert_eq!(s, "abc");
/// ```
#[macro_export]
macro_rules! input {
    (@from [$source:expr] @rest $($pat:pat = $parser:expr),* $(,)?) => {
        $(
            let $pat = $crate::read_value!(@from [$source] @rest $parser);
        )*
    };

    (from $str:expr, $($rest:tt)*) => {
        let mut source = $crate::Source::from($str);
        $crate::input! {
            @from [&mut source]
            @rest $($rest)*
        }
    };
    ($($rest:tt)*) => {
        let mut source = $crate::stdin_source();
        $crate::input! {
            @from [&mut *source]
            @rest $($rest)*
        }
        drop(source)
    };
}

/// 単一の値を 1 回だけパースする。
///
/// `input!` マクロが内部で使う 1 回分の読み取り処理だが、単発の読み取りにも直接使える。
///
/// # 仕様
///
/// - `read_value! { @from [source_expr] parser }`: 指定した [`Source`] から読み取り
/// - `read_value! { parser }`: 標準入力（[`stdin_source`]）から読み取り
///
/// # 例
///
/// ```
/// use io_reader::{read_value, Source, U32};
///
/// let mut source = Source::from("12");
/// let x = read_value! { @from [&mut source] U32 };
/// assert_eq!(x, 12);
/// ```
#[macro_export]
macro_rules! read_value {
    (@from [$source:expr] $(,)? @rest $parser:expr) => {
        $crate::Parser::read(&$parser, $source)
    };

    // interface
    {
        @from [$source:expr] $(,)?
        $parser:expr
    } => {
        read_value!(@from [$source] @rest $parser)
    };
    {
        $parser:expr
    } => {
        {
            let mut source = $crate::stdin_source();
            read_value!(@from [&mut source] @rest $parser)
        }
    };
}

/// [`BufRead`] をラップし、空白区切りの token を順に取り出す。
///
/// 内部で行を読み込みながら `split_whitespace` するため、改行をまたいでも連続した token 列として扱う。
///
/// # 例
///
/// ```
/// use io_reader::Source;
///
/// let mut source = Source::from("0120 444 444");
///
/// assert_eq!(source.next_token_unwrap(), "0120");
/// assert_eq!(source.next_token_unwrap(), "444");
/// assert_eq!(source.next_token_unwrap(), "444");
/// assert_eq!(source.next_token(), None);
/// ```
#[derive(Debug)]
pub struct Source<R: BufRead> {
    reader: R,
    line: String,
    tokens: SplitWhitespace<'static>,
}

impl<R: BufRead> Source<R> {
    /// [`BufRead`] から [`Source`] を構築する。
    ///
    /// # 例
    ///
    /// ```
    /// use io_reader::Source;
    /// let mut source = Source::from("hello world");
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

    /// 空白区切りで次の token を取得する。入力の終端では `None` を返す。
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

    /// [`next_token`](Self::next_token) の panic 版。終端に達すると panic する。
    pub fn next_token_unwrap(&mut self) -> &str {
        self.next_token()
            .unwrap_or_else(|| panic!("unexpected end of input."))
    }
}

impl<'a> From<&'a str> for Source<BufReader<&'a [u8]>> {
    /// 文字列から [`Source`] を構築する。テストでの入力構築に使う。
    fn from(value: &'a str) -> Self {
        Self::new(BufReader::new(value.as_bytes()))
    }
}

/// [`Source`] から 0 個以上の token を読み取り、値へ変換するアルゴリズムを表す。
///
/// `input!` マクロの右辺に書く値の型は、すべてこの trait を実装する。
pub trait Parser: Copy {
    /// 変換後の値の型。
    type Output;

    /// [`Source`] から token を読み取り、[`Output`](Self::Output) 型の値に変換する。
    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output;
}

/// [`FromStr`] へ委譲して 1 token を parse する [`Parser`]。
///
/// [`Char`], [`Str`], [`I32`] などの基本型パーサーは、すべてこの型のインスタンスとして定義される。
pub struct Canonical<P>(PhantomData<fn(P)>);
impl<P> Clone for Canonical<P> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<P> Copy for Canonical<P> {}

macro_rules! define_cannonical_parser {
    ($($prim:ty => $cann:ident),+$(,)?) => {$(
        /// [`
        #[doc = stringify!($prim)]
        /// `] を [`FromStr`] 経由で parse する [`Parser`]。
        #[allow(non_upper_case_globals)]
        pub const $cann: Canonical<$prim> = Canonical::<$prim>(PhantomData);
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

impl<P: FromStr> Parser for Canonical<P>
where
    P::Err: Debug,
{
    type Output = P;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        let token = source.next_token_unwrap();
        token.parse().unwrap_or_else(|e| {
            panic!(
                "failed to parse the token `{token}` to the value of type `{ty}`: {e:?}.",
                ty = std::any::type_name::<P>()
            )
        })
    }
}

/// 固定の token を期待して読み取る [`Parser`]。
///
/// [`Source`] から token をちょうど 1 個読み、指定した文字列と一致するかを検証する。
/// 一致しない場合は panic する。区切り文字や固定フォーマットの検証に使う。
///
/// # 例
///
/// ```
/// use io_reader::{input, Expect, U32, Source};
///
/// let mut source = Source::from("0 1 -1 2");
///
/// input! {
///     @from [&mut source] @rest
///     a = U32,
///     b = U32,
///     _ = Expect("-1"),
///     c = U32,
/// }
/// ```
#[derive(Clone, Copy)]
pub struct Expect(pub &'static str);
impl Parser for Expect {
    type Output = ();

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        let token = source.next_token_unwrap();
        assert_eq!(
            self.0,
            token,
            "Expected a fixed token `{expected}`, but got `{token}`",
            expected = self.0
        );
    }
}

/// 1-indexed の `usize` を読み取り、0-indexed に変換する [`Parser`]。
///
/// 読み取った値を $x$ とすると $x - 1$ を返す。$x = 0$ の場合は panic する。
///
/// # 例
///
/// ```
/// use io_reader::{Usize1, Source, Parser};
/// # let mut source = Source::from("5");
/// let result = Usize1.read(&mut source);
/// assert_eq!(result, 4);  // 5 - 1 = 4
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

/// 長さ $n$ を指定して `Vec<P::Output>` を parse する [`Parser`]。
///
/// `P` を $n$ 回連続で適用して集める。
///
/// # 例
///
/// ```
/// use io_reader::{input, Vector, I32, Source, Parser};
///
/// let mut source = Source::from("1 2 3");
///
/// input! {
///    @from [&mut source] @rest
///     v = Vector(I32, 3),
/// }
///
/// assert_eq!(v, vec![1, 2, 3]);
/// ```
#[derive(Clone, Copy)]
pub struct Vector<P>(pub P, pub usize);
impl<P: Parser> Parser for Vector<P> {
    type Output = std::vec::Vec<P::Output>;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        std::iter::repeat_with(|| self.0.read(source))
            .take(self.1)
            .collect()
    }
}

/// 長さ $N$ の `[P::Output; N]` を parse する [`Parser`]。
///
/// `N` はコンパイル時に固定する定数で、`P` を $N$ 回連続で適用する。
///
/// # 例
///
/// ```
/// use io_reader::{input, Array, I32, Source, Parser};
///
/// let mut source = Source::from("10 20 30");
///
/// input! {
///     @from [&mut source] @rest
///     arr = Array::<3, _>(I32),
/// }
///
/// assert_eq!(arr, [10, 20, 30]);
/// ```
#[derive(Clone, Copy)]
pub struct Array<const N: usize, P>(pub P);
impl<const N: usize, P: Parser> Parser for Array<N, P> {
    type Output = [P::Output; N];

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        std::array::from_fn(|_| self.0.read(source))
    }
}

macro_rules! impl_parser_for_tuples {
    ($head:ident, $($tail:ident,)*) => {
        impl<$head: Parser, $($tail: Parser,)*> Parser for ($head, $($tail,)*) {
            type Output = ($head::Output, $($tail::Output,)*);

            fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
                #[allow(non_snake_case)]
                let ($head, $($tail,)*) = self;
                ($head.read(source), $($tail.read(source),)*)
            }
        }
        impl_parser_for_tuples!{$($tail,)*}
    };
    {} => {};
}

impl_parser_for_tuples! {
    P0, P1, P2, P3, P4, P5,
    P6, P7, P8, P9, P10, P11,
    P12, P13, P14, P15, P16,
}

/// 1 token を文字ごとに解釈し `Vec<bool>` として parse する [`Parser`]。
///
/// 文字 $Z$ を `false`、文字 $O$ を `true` に対応させる。それ以外の文字が現れると panic する。
///
/// # 例
///
/// ```
/// use io_reader::{input, Bools, Source, Parser};
///
/// let mut source = Source::from("001101");
///
/// input! {
///     @from [&mut source] @rest
///     bits = Bools::<'0', '1'>,
/// }
///
/// assert_eq!(bits, vec![false, false, true, true, false, true]);
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

/// 1 token をそのまま `Vec<u8>` として parse する [`Parser`]。
///
/// # 例
///
/// ```
/// use io_reader::{input, Bytes, Source, Parser};
///
/// let mut source = Source::from("hello");
///
/// input! {
///     @from [&mut source] @rest
///     bytes = Bytes,
/// }
///
/// assert_eq!(bytes, [104, 101, 108, 108, 111]);
/// ```
#[derive(Clone, Copy)]
pub struct Bytes;
impl Parser for Bytes {
    type Output = Vec<u8>;

    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output {
        source.next_token_unwrap().as_bytes().to_vec()
    }
}
