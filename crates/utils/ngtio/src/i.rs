//! 標準入出力を支援します。
//!
//! TODO: lazy_static から自由になります。
//!
//! # 基本的な使い方
//!
//! 必要なものは次の 2 つです。
//!
//! - [`Scanner`] を実装した型 ([`LockDisposing`], [`LockKeeping`], [`StringBuf`]) のオブジェクト（を
//! [`Tokenizer`] で包んだもの）
//! - [`Parser`] を実装した型の ([`Leaf`], [`VecLen`], [`Tuple`]) のオブジェクト
//!
//! TODO: `Vec` の代わりに [`FromIterator`] を実装した任意の型のオブジェクトにパースしたいです。
//!
//! 使い方は主に 2 とおりです。
//!
//! - [`Parser`] を実装した型を全力で構築して、[`Parser::parse`] を呼びます。
//! - [`Tokenizer`] に実装された便利なメソッド群を使います。
//!
//! 前者は冗長ですが、すべての機能を使えます。後者は短いですが、より限定的な機能しか使えません。
//!
//! 汎用性の観点から、最初の例ではすべて前者の方式で紹介していこうと思います。
//! また doc tests の都合上、すべて [`StringBuf`]
//! を使用しているため、見た目上やや長そうなのですが、実際には [`LockKeeping`]
//! 等を使うと、コードは短くなるかとです。
//!
//! # Examples
//!
//! まずはプリミティブ型です。
//!
//! ```
//! use ngtio::{prelude::*, i::StringBuf};
//!
//! assert_eq!(u8::leaf().parse(&mut StringBuf::new("4\n").tokenizer()), 4);
//! ```
//!
//! タプルは [`<(T, U, ..)>::tuple()`](i/trait.ParserTuple.html#method.tuple) か
//! [`<(T, U, ..)>::leaf_tuple()`](i/trait.RawTuple.html#medhot.leaf_tuple) を使いましょう。
//!
//! ```
//! use ngtio::{prelude::*, i::StringBuf};
//! assert_eq!(
//!     (u8::leaf(), char::leaf())
//!         .tuple()
//!         .parse(&mut StringBuf::new("4 c\n").tokenizer()),
//!     (4, 'c')
//! );
//! assert_eq!(
//!     <(u8, char)>::leaf_tuple().parse(&mut StringBuf::new("4 c\n").tokenizer()),
//!     (4, 'c')
//! );
//! ```
//!
//! ベクターは [`Parser::vec(len)`](i/trait.Parser.html#method.vec) を使うと良いです。
//!
//! ```
//! use ngtio::{prelude::*, i::StringBuf};
//! assert_eq!(
//!     u8::leaf()
//!         .vec(3)
//!         .parse(&mut StringBuf::new("0 1 2\n").tokenizer()),
//!     vec![0, 1, 2]
//! );
//! ```
//!
//! これらを組み合わせると、任意の順番でネストすることができます。
//!
//! ```
//! use ngtio::{prelude::*, i::StringBuf};
//! assert_eq!(
//!     (
//!         (
//!             Usize1::leaf(),
//!             u8::leaf().vec(2),
//!             <()>::leaf_tuple(),
//!             (<()>::leaf_tuple(),).tuple().vec(2).vec(1),
//!         )
//!             .tuple()
//!             .vec(2),
//!         char::leaf(),
//!     )
//!         .tuple()
//!         .parse(&mut StringBuf::new("10 20 30 40 50 60 c\n").tokenizer()),
//!     (
//!         vec![
//!             (9, vec![20, 30], (), vec![vec![((),), ((),)]],),
//!             (39, vec![50, 60], (), vec![vec![((),), ((),)]],),
//!         ],
//!         'c'
//!     )
//! );
//! ```
//!
//! # [`Tokenizer`] 型の便利なメソッド群
//!
//! もちろんプリミティブはパースできます。
//!
//! ```
//! use ngtio::{prelude::*, i::StringBuf};
//! assert_eq!(StringBuf::new("42\n").tokenizer().parse::<u8>(), 42);
//! ```
//!
//! 各種複合型はこうのように、パーサの構造ごとに専用のメソッドがあります。
//!
//! ```
//! use ngtio::{prelude::*, i::StringBuf};
//!
//! // タプル
//! assert_eq!(StringBuf::new("42 c\n").tokenizer().tuple::<(u8, char)>(), (42, 'c'));
//!
//! // ベクター
//! assert_eq!(StringBuf::new("10 20\n").tokenizer().vec::<u8>(2), vec![10, 20]);
//!
//! // 複雑
//! assert_eq!(StringBuf::new("42 c\n").tokenizer().vec_tuple::<(u8, char)>(1), vec![(42, 'c')]);
//! assert_eq!(
//!     StringBuf::new("0 1 2 3\n").tokenizer().vec2::<u8>(2, 2),
//!     vec![vec![0, 1], vec![2, 3]]
//! );
//! assert_eq!(
//!     StringBuf::new("0 1 2 3\n").tokenizer().vec2_tuple::<(u8,)>(2, 2),
//!     vec![vec![(0,), (1,)], vec![(2,), (3,)]]
//! );
//! ```
//!
//! [`FromIterator`]: http://doc.rust-lang.org/std/iter/trait.FromIterator.html
//!
//! [`Parser::parse`]: i/trait.Parser.html#method.parse
//!
//! [`Parser`]: i/trait.Parser.html
//! [`Scanner`]: i/trait.Scanner.html
//! [`LockDisposing`]: i/struct.LockDisposing.html
//! [`LockKeeping`]: i/struct.LockKeeping.html
//! [`Leaf`]: i/struct.Leaf.html
//! [`VecLen`]: i/struct.VecLen.html
//! [`Tuple`]: i/struct.Tuple.html
//! [`Tokenizer`]: i/struct.Tokenizer.html
//! [`Usize1`]: i/struct.Usize1.html
//! [`StringBuf`]: i/struct.StringBuf.html
use std::{io, iter};

pub use multi_token::{Leaf, Parser, ParserTuple, RawTuple, Tuple, VecLen};
pub use token::{Token, Usize1};

/// [`Scanner`](traits.Scanner.html) トレイトを実装した型をラップして、トークンサーバーをします。
pub struct Tokenizer<S: Scanner> {
    queue: Vec<String>, // FIXME: String のみにすると速そうです。
    scanner: S,
}
impl<S: Scanner> Tokenizer<S> {
    ///
    /// # Panics
    ///
    /// トークンを補充してもトークンキューがからなとき、パニックします。
    pub fn token(&mut self) -> String {
        self.load();
        self.queue.pop().expect("入力が終了したのですが。")
    }
    /// 新しく作ります。
    pub fn new(scanner: S) -> Self {
        Self {
            queue: Vec::new(),
            scanner,
        }
    }
    fn load(&mut self) {
        while self.queue.is_empty() {
            let mut s = String::new();
            let length = self.scanner.read_line(&mut s);
            if length == 0 {
                break;
            }
            self.queue = s.split_whitespace().rev().map(str::to_owned).collect();
        }
    }

    /// 空行を読み飛ばします。
    ///
    /// # Panics
    ///
    /// 行の途中で呼ぶ、もしくは次が空行でないときパニックです。
    ///
    pub fn skip_line(&mut self) {
        assert!(
            self.queue.is_empty(),
            "行の途中で呼ばないでいただきたいです。現在のトークンキュー: {:?}",
            &self.queue
        );
        self.load();
    }

    /// 入力が終了していること（正確には、次が空行であること）を宣言します。
    ///
    /// # Panics
    ///
    /// 入力が終了していなければ、パニックです。
    ///
    pub fn end(&mut self) {
        self.load();
        assert!(self.queue.is_empty(), "入力はまだあります！");
    }

    /// 指定された型にパースします。
    pub fn parse<T: Token>(&mut self) -> T::Output {
        T::parse(&self.token())
    }

    /// 指定された型を `n` 回パースして集めます。
    pub fn parse_collect<T: Token, B>(&mut self, n: usize) -> B
    where
        B: iter::FromIterator<T::Output>,
    {
        iter::repeat_with(|| self.parse::<T>()).take(n).collect()
    }

    /// `(..)` をパースします。
    pub fn tuple<T: RawTuple>(&mut self) -> <T::LeafTuple as Parser>::Output {
        T::leaf_tuple().parse(self)
    }

    /// `Vec<_>` をパースします。
    pub fn vec<T: Token>(&mut self, len: usize) -> Vec<T::Output> {
        T::leaf().vec(len).parse(self)
    }

    /// `Vec<(..)>` をパースします。
    pub fn vec_tuple<T: RawTuple>(&mut self, len: usize) -> Vec<<T::LeafTuple as Parser>::Output> {
        T::leaf_tuple().vec(len).parse(self)
    }

    /// `Vec<Vec<_>>` をパースします。
    pub fn vec2<T: Token>(&mut self, height: usize, width: usize) -> Vec<Vec<T::Output>> {
        T::leaf().vec(width).vec(height).parse(self)
    }

    /// `Vec<Vec<(..)>>` をパースします。
    pub fn vec2_tuple<T>(
        &mut self,
        height: usize,
        width: usize,
    ) -> Vec<Vec<<T::LeafTuple as Parser>::Output>>
    where
        T: RawTuple,
    {
        T::leaf_tuple().vec(width).vec(height).parse(self)
    }
}

mod token {
    use super::multi_token::Leaf;
    use std::{any, fmt, marker, str};

    /// 主にプリミティブ型のパースをします。[`FromStr`](https://doc.rust-lang.org/std/str/trait.FromStr)
    /// とは異なり、戻り値型が `Self` である必要はありません。
    pub trait Token: Sized {
        /// パース結果の型です。
        type Output;
        /// パースをします。
        fn parse(s: &str) -> Self::Output;
        /// 複合型のパースができるように、[`Leaf`](i/struct.Leaf.html) に包みます。
        fn leaf() -> Leaf<Self> {
            Leaf(marker::PhantomData)
        }
    }

    impl<T> Token for T
    where
        T: str::FromStr,
        <T as str::FromStr>::Err: fmt::Debug,
    {
        type Output = T;
        fn parse(s: &str) -> Self::Output {
            s.parse()
                .unwrap_or_else(|_| panic!("Parse error!: ({}: {})", s, any::type_name::<T>(),))
        }
    }

    /// `usize` 型にパースしたあとで `1` を引きます。
    ///
    /// # Panics
    ///
    /// `usize` のパースに成功したとしても、パース結果が `0` のときにはパニックします。
    pub struct Usize1 {}
    impl Token for Usize1 {
        type Output = usize;
        fn parse(s: &str) -> Self::Output {
            usize::parse(s)
                .checked_sub(1)
                .expect("Parse error! (Zero substruction error of Usize1)")
        }
    }
}

mod multi_token {
    use super::{Scanner, Token, Tokenizer};
    use std::{iter, marker};

    /// 複合型を含め、いろいろとパースをします。
    pub trait Parser: Sized {
        /// パース結果の型です。
        type Output;
        /// パースをします。
        fn parse<S: Scanner + ?Sized>(&self, server: &mut Tokenizer<S>) -> Self::Output;
        /// `Vec` のパースのために、[`VecLen`](i/struct.VecLen.html) に包みます。
        fn vec(self, len: usize) -> VecLen<Self> {
            VecLen { len, elem: self }
        }
    }
    /// [`Token`](i/traits.Token.html)
    /// トレイトを実装した型をラップして、[`Parser`](i/traits.Parser.html) を実装します。
    pub struct Leaf<T>(pub(super) marker::PhantomData<T>);
    impl<T: Token> Parser for Leaf<T> {
        type Output = T::Output;
        fn parse<S: Scanner + ?Sized>(&self, server: &mut Tokenizer<S>) -> T::Output {
            server.parse::<T>()
        }
    }

    /// `Vec` のパーサです。
    pub struct VecLen<T> {
        /// 作る `Vec` の長さです。
        pub len: usize,
        /// 要素のパーサです。
        pub elem: T,
    }
    impl<T: Parser> Parser for VecLen<T> {
        type Output = Vec<T::Output>;
        fn parse<S: Scanner + ?Sized>(&self, server: &mut Tokenizer<S>) -> Self::Output {
            iter::repeat_with(|| self.elem.parse(server))
                .take(self.len)
                .collect()
        }
    }

    /// [`Token`] を実装した型の生タプルに実装されるトレイトです。
    ///
    /// このトレイトを実装した型は [`Parser`] トレイトを実装していない中間型ですから、
    /// 即座に [`leaf_tuple`] メソッドで [`Parser`]
    /// トレイトを実装した型に変換されることを想定ています。
    ///
    /// # Examples
    ///
    /// ```
    /// use ngtio::prelude::*;
    /// <(u8, u8)>::leaf_tuple();
    /// ```
    ///
    /// [`Token`]: i/trait.Token.html
    /// [`Parser`]: i/trait.Parser.html
    /// [`leaf_tuple`]: i/trait.RawTuple.html#method.leaf_tuple
    pub trait RawTuple {
        /// [`Parser`](i/trait.Parser.html) トレイトを実装した型です。
        type LeafTuple: Parser;
        /// [`Parser`](i/trait.Parser.html) トレイトを実装した型に変換します。
        fn leaf_tuple() -> Self::LeafTuple;
    }
    /// [`Parser`] を実装した型の生タプルに実装されるトレイトです。
    ///
    /// このトレイトを実装した型は [`Parser`] トレイトを実装していない中間型ですから、
    /// 即座に [`tuple`] メソッドで [`Parser`]
    /// トレイトを実装した型に変換されることを想定ています。
    ///
    /// [`Parser`]: i/trait.Parser.html
    /// [`tuple`]: i/trait.Parn.html#method.tuple
    ///
    /// # Examples
    ///
    /// ```
    /// use ngtio::prelude::*;
    /// (u8::leaf(), u8::leaf().vec(3)).tuple();
    /// ```
    pub trait ParserTuple {
        /// [`Parser`](i/trait.Parser.html) トレイトを実装した型です。
        type Tuple: Parser;
        /// [`Parser`](i/trait.Parser.html) トレイトを実装した型に変換します。
        fn tuple(self) -> Self::Tuple;
    }
    /// タプルのパーサです。
    pub struct Tuple<T>(pub T);
    macro_rules! impl_tuple {
        ($($t:ident: $T:ident),*) => {
            impl<$($T),*> Parser for Tuple<($($T,)*)>
            where
                $($T: Parser,)*
            {
                type Output = ($($T::Output,)*);
                #[allow(unused_variables)]
                fn parse<S: Scanner + ?Sized>(&self, server: &mut Tokenizer<S>) -> Self::Output {
                    match self {
                        Tuple(($($t,)*)) => {
                            ($($t.parse(server),)*)
                        }
                    }
                }
            }
            impl<$($T: Token),*> RawTuple for ($($T,)*) {
                type LeafTuple = Tuple<($(Leaf<$T>,)*)>;
                fn leaf_tuple() -> Self::LeafTuple {
                    Tuple(($($T::leaf(),)*))
                }
            }
            impl<$($T: Parser),*> ParserTuple for ($($T,)*) {
                type Tuple = Tuple<($($T,)*)>;
                fn tuple(self) -> Self::Tuple {
                    Tuple(self)
                }
            }
        };
    }
    impl_tuple!();
    impl_tuple!(t1: T1);
    impl_tuple!(t1: T1, t2: T2);
    impl_tuple!(t1: T1, t2: T2, t3: T3);
    impl_tuple!(t1: T1, t2: T2, t3: T3, t4: T4);
    impl_tuple!(t1: T1, t2: T2, t3: T3, t4: T4, t5: T5);
    impl_tuple!(t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6);
    impl_tuple!(t1: T1, t2: T2, t3: T3, t4: T4, t5: T5, t6: T6, t7: T7);
    impl_tuple!(
        t1: T1,
        t2: T2,
        t3: T3,
        t4: T4,
        t5: T5,
        t6: T6,
        t7: T7,
        t8: T8
    );
}

/// 一行補充する関数 [`read_line`](trait.Scanner.html#method.read_line) を持つ型の抽象化です。
pub trait Scanner: Sized {
    /// 一行補充します。
    fn read_line(&mut self, s: &mut String) -> usize;
    /// [`Tokenizer`](struct.Tokenizer.html) に包みます。
    fn tokenizer(self) -> Tokenizer<Self> {
        Tokenizer::new(self)
    }
}

/// 標準入力を 1 行ずつ読み込み、毎回ロックを取得・破棄します。
pub struct LockDisposing {}

impl Scanner for LockDisposing {
    fn read_line(&mut self, s: &mut String) -> usize {
        io::stdin()
            .read_line(s)
            .expect("標準入力の読み取りに失敗です。")
    }
}

lazy_static::lazy_static! {
    static ref STDIN: io::Stdin = io::stdin();
}

/// 標準入力のロックを保持して、1 行ずつ読み込みます。
pub struct LockKeeping<'a> {
    lock: io::StdinLock<'a>,
}
impl<'a> LockKeeping<'a> {
    /// 標準入力のロックを新たに取得して構築します。
    pub fn new() -> Self {
        Self { lock: STDIN.lock() }
    }
}
impl<'a> Default for LockKeeping<'a> {
    fn default() -> Self {
        Self::new()
    }
}
impl<'a> Scanner for LockKeeping<'a> {
    fn read_line(&mut self, s: &mut String) -> usize {
        use io::BufRead;
        self.lock
            .read_line(s)
            .expect("標準入力の読み取りに失敗です。")
    }
}

/// 全文を [`String`](https://doc.rust-lang.org/std/string/struct.String.html) 型で保持します。
pub struct StringBuf(pub String);
impl StringBuf {
    /// 構築します。
    pub fn new(s: &str) -> Self {
        StringBuf(s.to_owned())
    }
}
impl Scanner for StringBuf {
    fn read_line(&mut self, s: &mut String) -> usize {
        if let Some(length) = self.0.find('\n') {
            *s = self.0.drain(..length).collect();
            self.0.drain(0..1);
            s.len()
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_buf(s: &str) -> Tokenizer<StringBuf> {
        StringBuf(s.to_owned()).tokenizer()
    }

    #[test]
    fn test_token() {
        let mut s = make_buf(
            r"ABC DEF

GHI
  MNO    PQR	STU  
",
        );

        assert_eq!(&s.token(), "ABC");
        assert_eq!(&s.token(), "DEF");
        s.skip_line();
        assert_eq!(&s.token(), "GHI");
        assert_eq!(&s.token(), "MNO");
        assert_eq!(&s.token(), "PQR");
        assert_eq!(&s.token(), "STU");
        s.end();
    }

    #[test]
    #[should_panic]
    fn test_require_endl() {
        let mut s = make_buf("0");
        s.token();
    }

    #[test]
    fn test_parse() {
        let mut s = make_buf("0 4\n");
        assert_eq!(s.parse::<u32>(), 0);
        assert_eq!(s.parse::<Usize1>(), 3);
        s.end();
    }

    #[test]
    fn test_parse_collect() {
        use std::collections::BinaryHeap;
        let mut s = make_buf("0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(s.parse_collect::<u32, Vec<u32>>(3), vec![0, 1, 2]);
        assert_eq!(s.parse_collect::<Usize1, Vec<usize>>(3), vec![2, 3, 4]);
        assert_eq!(
            s.parse_collect::<u8, BinaryHeap<u8>>(3)
                .iter()
                .copied()
                .collect::<Vec<u8>>(),
            vec![8, 7, 6]
        );
        assert_eq!(s.parse_collect::<char, Vec<char>>(1), vec!['9']);
        s.end();
    }

    #[test]
    fn test_tuple() {
        let mut s = make_buf("0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(s.tuple::<(u8, char)>(), (0, '1'));
        assert_eq!(s.tuple::<(u8,)>(), (2,));
        assert_eq!(s.tuple::<()>(), ());
        assert_eq!(
            s.tuple::<(u8, u8, u8, u8, u8, u8, u8,)>(),
            (3, 4, 5, 6, 7, 8, 9)
        );
        s.end();
    }

    #[test]
    fn test_vec() {
        let mut s = make_buf("0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(s.vec::<u8>(2), vec![0, 1]);
        assert_eq!(s.vec::<char>(1), vec!['2']);
        assert_eq!(s.vec::<u8>(0), Vec::new());
        assert_eq!(s.vec::<u8>(7), vec![3, 4, 5, 6, 7, 8, 9]);
        s.end();
    }

    #[test]
    fn test_vec_tuple() {
        let mut s = make_buf("0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(s.vec_tuple::<(char, Usize1)>(2), vec![('0', 0), ('2', 2)]);
        assert_eq!(s.vec_tuple::<()>(2), vec![(), ()]);
        assert_eq!(s.vec_tuple::<(u8,)>(2), vec![(4,), (5,)]);
        assert_eq!(s.vec_tuple::<(u8, u8, u8, u8)>(1), vec![(6, 7, 8, 9)]);
        s.end();
    }

    #[test]
    fn test_vec2() {
        let mut s = make_buf("0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(s.vec2::<u8>(2, 3), vec![vec![0, 1, 2], vec![3, 4, 5]]);
        assert_eq!(s.vec2::<char>(100, 0), vec![Vec::new(); 100]);
        assert_eq!(s.vec2::<i32>(0, 100), Vec::<Vec<i32>>::new());
        assert_eq!(s.vec2::<Usize1>(1, 4), vec![vec![5, 6, 7, 8]]);
        s.end();
    }

    #[test]
    fn test_vec2_tuple() {
        let mut s = make_buf("0 1 2 3 4 5 6 7 8 9 10 11\n");
        assert_eq!(
            s.vec2_tuple::<(char, u8, Usize1)>(1, 4),
            vec![vec![('0', 1, 1), ('3', 4, 4), ('6', 7, 7), ('9', 10, 10)]]
        );
        s.end();
    }

    #[test]
    fn test_ad_hoc() {
        let mut s = make_buf("0 1 2 3 4 5 6 7 8 9\n");
        assert_eq!(
            (u8::leaf(), u8::leaf().vec(4)).tuple().vec(2).parse(&mut s),
            vec![(0, vec![1, 2, 3, 4]), (5, vec![6, 7, 8, 9])]
        );
        s.end();
    }
}
