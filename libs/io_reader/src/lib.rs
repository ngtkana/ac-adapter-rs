//! 競技プログラミング用の入力ライブラリです。
//!
//! # Examples
//!
//! ```
//! use io_reader::{input, Usize, I32, Vector};
//! # let mut source = io_reader::Source::from("2 3 10 20 30");
//!
//! input! {
//! #   @from [source]
//!     n: Usize,
//!     m: Usize,
//!     a: Vector(I32, 3),
//! }
//! # assert_eq!(n, 2);
//! # assert_eq!(m, 3);
//! # assert_eq!(a, [10, 20, 30]);
//! ```
//!
//! # Parser
//!
//! `input` macro において、右辺に書いてあるのは型ではなく値です。
//!
//! パーサー [`Parser`] trait を実装した型の**値**であり、これを組み合わせて新しい parser を作ります。
//!
//!
//! # Source
//!
//! 入力源は [`BufRead`] trait を実装した型をラップした、[`Source`] 型を使えます。
//!
//! 代表的な用法は標準入力 [`Stdin`] と、テスト用に文字列 `&'static str` です。
//!
//!
//! ## 標準入力
//!
//! 何も記載せず `input!` マクロを使えば使えます。
//!
//! 明示的に [`Source`] を取得したければ [`stdin_source`] 関数が使えます。[`MutexGuard`] で wrap
//! したものが返ってきます。実体は [`OnceLock<Mutex<_>>`] に包まれて `static` に置かれています。
//!
//! ## 文字列
//!
//! [`Source::from`] を使って `&str` から変換することで構築できます。
//!
//! # パーサーの種類
//!
//! - **基本型**: [`Char`], [`Str`], [`I32`], [`U64`], など（`Canonical<P>` による）
//! - **列**: [`Vector<P>`] で $n$ 個の要素
//! - **配列**: [`Array<N, P>`] で長さ $N$ の配列
//! - **タプル**: `(P0, P1)` 等でタプル
//! - **特殊**: [`Usize1`] で 1-indexed usize、[`Bools<Z, O>`] で 0/1 文字列、[`Bytes`] でバイト列

use std::{
    fmt::Debug,
    io::{BufRead, BufReader, Stdin, stdin},
    marker::PhantomData,
    str::{FromStr, SplitWhitespace},
    sync::{Mutex, MutexGuard, OnceLock},
};

static STDIN_SOURCE: OnceLock<Mutex<Source<BufReader<Stdin>>>> = OnceLock::new();

/// Static に置かれた stdin source にアクセスします。
///
/// 実体は [`OnceLock<Mutex<_>>`] に包まれていて、遅延初期化され、mutex 管理されます。
pub fn stdin_source() -> MutexGuard<'static, Source<BufReader<Stdin>>> {
    STDIN_SOURCE
        .get_or_init(|| Mutex::new(Source::new(BufReader::new(stdin()))))
        .lock()
        .unwrap()
}

/// Parser を複数用いて、複数の変数を定義・初期化する macro です。
///
/// # Examples
///
/// ```
/// use io_reader::{input, I32, Usize};
/// # let mut source = io_reader::Source::from("10\n3");
/// input! {
/// #   @from [source]
///     x: I32,
///     n: Usize,
/// }
/// # assert_eq!(x, 10);
/// # assert_eq!(n, 3);
/// ```
///
/// ## 文字列版 (`@from` の使い方)
///
/// ```
/// use io_reader::{input, I32, Usize, Source};
/// input! {
///     @from [Source::from("10\n3")]
///     x: I32,
///     n: Usize,
/// }
/// assert_eq!(x, 10);
/// assert_eq!(n, 3);
/// ```
///
#[macro_export]
macro_rules! input {
    {
        @from [$source:expr] $(,)?
        $($name:tt: $parser:expr),* $(,)?
    } => {
        let source = &mut $source;
        $(
            #[allow(ignored_unit_patterns)]
            let $name = $crate::Parser::read(&$parser, &mut *source);
        )*
    };
    {
        $rest:tt
    } => {
        let mut source = $crate::source();
        input! {
            @from [source]
            $rest
        }
    };
}

/// [`BufRead`] を wrap し、token を返す型です。
///
/// # Examples
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
    /// [`BufReader`] から新しい [`Source`] を構築します。
    ///
    /// # Examples
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

    /// whitespace 区切りで、次の token を取得します。
    ///
    /// 入力の終端に達した場合は `None` を返します。
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

    /// Panic 版の [`next_token`](Self::next_token) です。
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

/// 文字列(0個以上のtoken)を parse するアルゴリズムと、その戻り値型の情報を提要する trait です。
pub trait Parser: Copy {
    /// 戻り値型
    type Output;

    /// [`Source`] から token を 0 個以上受け取って、目的の型に parse します。
    fn read<R: BufRead>(&self, source: &mut Source<R>) -> Self::Output;
}

/// [`FromStr`] 経由で $P$ を parse する [`Parser`] です。
pub struct Canonical<P>(PhantomData<fn(P)>);
impl<P> Clone for Canonical<P> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<P> Copy for Canonical<P> {}

macro_rules! define_cannonical_parser {
    ($($prim:ty => $cann:ident),+$(,)?) => {$(
        /// [`FromStr`] 経由で [`
        #[doc = stringify!($prim)]
        /// `] を parse する [`Parser`] です。
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

/// 固定の token string を期待して読み取る [`Parser`] です。
///
/// [`Source`] から token をちょうど 1 個読んで、それが指定の文字列と一致していることを確認します。
/// 一致しない場合は panic します。
///
/// # Examples
///
/// ```
/// use io_reader::{input, Expect, U32, Source};
///
/// input! {
///     @from [Source::from("0 1 -1 2")]
///     a: U32,
///     b: U32,
///     _: Expect("-1"),
///     c: U32,
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

/// 1-indexed の `usize` を読み取り、0-indexed に変換する [`Parser`] です。
///
/// 0 が入力された場合は panic します。
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

/// 長さを指定して [`Vec<P::Output>`] を parse します。
///
/// # Examples
///
/// ```
/// use io_reader::{Vector, I32, Source, Parser, input};
///
/// input! {
///    @from [Source::from("1 2 3")]
///     v: Vector(I32, 3)
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

/// Array `[P::Output; N]` の [`Parser`] です。
///
/// Parser は順序通り実行されます。
///
/// # Examples
///
/// ```
/// use io_reader::{input, Array, I32, Source, Parser};
///
/// input! {
///     @from [Source::from("10 20 30")]
///     arr: Array::<3, _>(I32),
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

/// `Vec<bool>` の [`Parser`] です。
///
/// `Bools::<Z, O>` で、次のトークンの各文字を解析します。
/// 文字 $Z$ は `false`, 文字 $O$ は `true` に対応します。
///
/// # Examples
///
/// ```
/// use io_reader::{Bools, Source, Parser, input};
///
/// input! {
///     @from [Source::from("001101")]
///     bits: Bools::<'0', '1'>,
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

/// `Vec<u8>` の [`Parser`] です。
///
/// # Examples
///
/// ```
/// use io_reader::{Bytes, Source, Parser, input};
///
/// input! {
///     @from [Source::from("hello")]
///     bytes: Bytes,
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
