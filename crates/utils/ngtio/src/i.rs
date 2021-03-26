use std::{
    io::{self, BufRead},
    iter,
};

pub use self::{
    multi_token::{Leaf, Parser, ParserTuple, RawTuple, Tuple, VecLen},
    token::{Token, Usize1},
};

/// 標準入力を受け取る [`Tokenizer`] を構築します。
///
/// [`Tokenizer`]: i/struct.Tokenizer.html
pub fn with_stdin() -> Tokenizer<io::BufReader<io::Stdin>> {
    io::BufReader::new(io::stdin()).tokenizer()
}

/// 文字列スライスを管理する [`Tokenizer`] を構築します。
///
/// [`Tokenizer`]: i/struct.Tokenizer.html
pub fn with_str(src: &str) -> Tokenizer<&[u8]> {
    src.as_bytes().tokenizer()
}

/// [`Scanner`](traits.Scanner.html) トレイトを実装した型をラップして、トークンサーバーをします。
pub struct Tokenizer<S: BufRead> {
    queue: Vec<String>, // FIXME: String のみにすると速そうです。
    scanner: S,
}
macro_rules! prim_method {
    ($name:ident: $T:ty) => {
        pub fn $name(&mut self) -> $T {
            <$T>::leaf().parse(self)
        }
    };
    ($name:ident) => {
        prim_method!($name: $name);
    };
}
macro_rules! prim_methods {
    ($name:ident: $T:ty; $($rest:tt)*) => {
        prim_method!($name:$T);
        prim_methods!($($rest)*);
    };
    ($name:ident; $($rest:tt)*) => {
        prim_method!($name);
        prim_methods!($($rest)*);
    };
    () => ()
}
impl<S: BufRead> Tokenizer<S> {
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
            let length = self.scanner.read_line(&mut s).unwrap(); // 入力が UTF-8 でないときにエラーだそうです。
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
    prim_methods! {
        u8; u16; u32; u64; u128; usize;
        i8; i16; i32; i64; i128; isize;
        f32; f64;
        char; string: String;
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
        <Self as str::FromStr>::Err: fmt::Debug,
    {
        type Output = Self;
        fn parse(s: &str) -> Self::Output {
            s.parse()
                .unwrap_or_else(|_| panic!("Parse error!: ({}: {})", s, any::type_name::<Self>(),))
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
    use super::{Token, Tokenizer};
    use std::{io::BufRead, iter, marker};

    /// 複合型を含め、いろいろとパースをします。
    pub trait Parser: Sized {
        /// パース結果の型です。
        type Output;
        /// パースをします。
        fn parse<S: BufRead>(&self, server: &mut Tokenizer<S>) -> Self::Output;
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
        fn parse<S: BufRead>(&self, server: &mut Tokenizer<S>) -> T::Output {
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
        fn parse<S: BufRead>(&self, server: &mut Tokenizer<S>) -> Self::Output {
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
                fn parse<S: BufRead >(&self, server: &mut Tokenizer<S>) -> Self::Output {
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

trait Scanner: BufRead + Sized {
    fn tokenizer(self) -> Tokenizer<Self> {
        Tokenizer::new(self)
    }
}
impl<R: BufRead> Scanner for R {}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_buf(s: &'static str) -> Tokenizer<&'static [u8]> {
        s.as_bytes().tokenizer()
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
    fn test_not_require_endl() {
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
        s.tuple::<()>();
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
