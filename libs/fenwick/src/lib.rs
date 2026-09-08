//! 結合的な演算を載せたFenwick木（Binary Indexed Tree）。
//!
//! 長さ$n$の配列を添字の最下位ビットで木構造化し、添字$i$のノードに区間
//! $[i - (i \mathbin{\&} (-i)), i)$（1-indexed）の総積を持たせる。この構造により、
//! 1点更新も前計算和の取得も、木の根から葉までの経路上高々$O(\log n)$個の
//! ノードを辿るだけで完了する。
//!
//! # 仕様
//!
//! [`Op`]トレイトで結合律を満たす二項演算 $(S, \oplus, e)$ を定義する。
//!
//! * [`Op::identity`][]: 単位元 $e$
//! * [`Op::add`][]: 演算 $a \oplus b$（結合律を満たすこと）
//!
//! 逆演算 $\ominus$ を持つ場合は[`OpSub`]も実装すると、任意区間 $[l, r)$ の
//! 畳み込みを $\mathrm{fold\_to}(r) \ominus \mathrm{fold\_to}(l)$ で計算できる。
//!
//! # 例
//!
//! ```
//! use fenwick::Fenwick;
//! use fenwick::Op;
//! use fenwick::OpSub;
//!
//! struct Sum;
//! impl Op for Sum {
//!     type Value = i64;
//!
//!     fn identity() -> i64 {
//!         0
//!     }
//!
//!     fn add(a: &i64, b: &i64) -> i64 {
//!         a + b
//!     }
//! }
//! impl OpSub for Sum {
//!     fn sub(a: &i64, b: &i64) -> i64 {
//!         a - b
//!     }
//! }
//!
//! let mut tree = Fenwick::<Sum>::new(5);
//! tree.add(1, &10);
//! tree.add(3, &20);
//! assert_eq!(tree.fold(1..4), 30); // 10 + 0 + 20
//! ```
//!
//! # 計算量
//!
//! - 構築（[`Fenwick::new`]）: $O(n)$
//! - 1点更新（[`Fenwick::add`], [`Fenwick::sub`]）: $O(\log n)$
//! - 畳み込み（[`Fenwick::fold_to`], [`Fenwick::fold`]）: $O(\log n)$

use std::fmt::Debug;
use std::marker::PhantomData;
use std::ops::Range;
use std::ops::RangeTo;

/// 結合律を満たす二項演算 $(S, \oplus, e)$。
///
/// Fenwick木が正しく動作するには、任意の $a, b, c$ に対し
/// $(a \oplus b) \oplus c = a \oplus (b \oplus c)$ を満たす必要がある。
///
/// # 例
///
/// ```
/// # use fenwick::Op;
/// struct AddOp;
/// impl Op for AddOp {
///     type Value = i64;
///
///     fn identity() -> Self::Value {
///         0
///     }
///
///     fn add(a: &Self::Value, b: &Self::Value) -> Self::Value {
///         a + b
///     }
/// }
/// ```
pub trait Op {
    /// 演算の値の型。
    type Value;

    /// 単位元 $e$ を返す。
    fn identity() -> Self::Value;

    /// 演算 $a \oplus b$ を計算する。
    fn add(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

/// 逆演算 $\ominus$ を追加する[`Op`]の拡張。
///
/// `add`だけでは前計算 $[0, i)$ の畳み込みしか求まらない。`sub`を実装すると、
/// 任意区間 $[l, r)$ の畳み込みを $\mathrm{fold\_to}(r) \ominus \mathrm{fold\_to}(l)$
/// で計算できるようになる。
///
/// # 例
///
/// ```
/// # use fenwick::Op;
/// use fenwick::OpSub;
/// struct AddOp;
/// impl OpSub for AddOp {
///     fn sub(a: &i64, b: &i64) -> i64 {
///         a - b
///     }
/// }
/// # impl Op for AddOp {
/// #     type Value = i64;
/// #     fn identity() -> i64 { 0 }
/// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
/// # }
/// ```
pub trait OpSub: Op {
    /// 逆演算 $a \ominus b$ を計算する。
    fn sub(a: &Self::Value, b: &Self::Value) -> Self::Value;
}

/// Fenwick木（Binary Indexed Tree）。
///
/// 長さ$n$の配列 $x_0, \ldots, x_{n-1}$ を管理し、1点更新と前計算和
/// $x_0 \oplus \cdots \oplus x_{i-1}$ の取得をともに $O(\log n)$ で行う。
/// 内部では長さ$n+1$の配列を持ち、添字$i$のノードが区間
/// $[i - (i \mathbin{\&} (-i)), i)$ の総積を保持する。
///
/// # 例
///
/// ```
/// # use fenwick::{Fenwick, Op};
/// # struct AddOp;
/// # impl Op for AddOp {
/// #     type Value = i64;
/// #     fn identity() -> i64 { 0 }
/// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
/// # }
/// let mut tree = Fenwick::<AddOp>::new(5);
/// tree.add(2, &10);
/// tree.add(4, &5);
/// assert_eq!(tree.fold_to(..5), 15);
/// ```
pub struct Fenwick<O: Op> {
    items: Vec<O::Value>,
    __maker: PhantomData<O>,
}
impl<T: Debug, O: Op<Value = T>> Debug for Fenwick<O> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(
                (1usize..self.items.len()).map(|i| (i - (i & i.wrapping_neg())..i, &self.items[i])),
            )
            .finish()
    }
}

impl<O: Op> Default for Fenwick<O> {
    /// 長さ$0$の空のFenwick木を生成する。
    ///
    /// # 例
    ///
    /// ```
    /// # use fenwick::Fenwick;
    /// # struct AddOp;
    /// # impl fenwick::Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let tree: Fenwick<AddOp> = Default::default();
    /// ```
    fn default() -> Self {
        Self {
            items: vec![],
            __maker: PhantomData,
        }
    }
}
impl<T, O: Op<Value = T>> Fenwick<O> {
    /// 長さ$n$のFenwick木を生成する。全要素は単位元 $e$ に初期化される。$O(n)$。
    ///
    /// # 例
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let tree = Fenwick::<AddOp>::new(10);
    /// ```
    pub fn new(len: usize) -> Self
    where
        T: Clone,
    {
        Self {
            items: vec![O::identity(); len + 1],
            __maker: PhantomData,
        }
    }

    /// $x_i \mathrel{\oplus}= v$、$O(\log n)$。
    ///
    /// 前提：$i < n$。
    ///
    /// # 例
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(2, &10);
    /// assert_eq!(tree.fold_to(..3), 10);
    /// ```
    pub fn add(&mut self, mut index: usize, value: &T) {
        assert!(index + 1 < self.items.len(), "index out of bounds");
        index += 1;
        while index < self.items.len() {
            self.items[index] = O::add(&self.items[index], value);
            index += index & index.wrapping_neg();
        }
    }

    /// $x_0 \oplus x_1 \oplus \cdots \oplus x_{\mathrm{end} - 1}$ を返す。$O(\log n)$。
    ///
    /// # 例
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(0, &1);
    /// tree.add(1, &2);
    /// tree.add(2, &3);
    /// assert_eq!(tree.fold_to(..3), 6);
    /// ```
    pub fn fold_to(&self, range: RangeTo<usize>) -> T {
        let mut end = range.end;
        let mut result = O::identity();
        while end != 0 {
            result = O::add(&result, &self.items[end]);
            end -= end & end.wrapping_neg();
        }
        result
    }
}

impl<T, O: OpSub<Value = T>> Fenwick<O> {
    /// $x_i \mathrel{\ominus}= v$、$O(\log n)$。[`OpSub`]を要求する。
    ///
    /// 前提：$i < n$。
    ///
    /// # 例
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op, OpSub};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// # impl OpSub for AddOp {
    /// #     fn sub(a: &i64, b: &i64) -> i64 { a - b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(2, &10);
    /// tree.sub(2, &3);
    /// assert_eq!(tree.fold_to(..3), 7);
    /// ```
    pub fn sub(&mut self, mut index: usize, value: &T) {
        assert!(index + 1 < self.items.len(), "index out of bounds");
        index += 1;
        while index < self.items.len() {
            self.items[index] = O::sub(&self.items[index], value);
            index += index & index.wrapping_neg();
        }
    }

    /// $x_{\mathrm{start}} \oplus \cdots \oplus x_{\mathrm{end} - 1}$ を
    /// $\mathrm{fold\_to}(\mathrm{end}) \ominus \mathrm{fold\_to}(\mathrm{start})$ で計算する。
    /// $O(\log n)$。[`OpSub`]を要求する。
    ///
    /// # 例
    ///
    /// ```
    /// # use fenwick::{Fenwick, Op, OpSub};
    /// # struct AddOp;
    /// # impl Op for AddOp {
    /// #     type Value = i64;
    /// #     fn identity() -> i64 { 0 }
    /// #     fn add(a: &i64, b: &i64) -> i64 { a + b }
    /// # }
    /// # impl OpSub for AddOp {
    /// #     fn sub(a: &i64, b: &i64) -> i64 { a - b }
    /// # }
    /// let mut tree = Fenwick::<AddOp>::new(5);
    /// tree.add(0, &1);
    /// tree.add(1, &2);
    /// tree.add(2, &3);
    /// tree.add(3, &4);
    /// assert_eq!(tree.fold(1..3), 5); // 2 + 3
    /// ```
    pub fn fold(&self, range: Range<usize>) -> T {
        let mut result = self.fold_to(..range.end);
        result = O::sub(&result, &self.fold_to(..range.start));
        result
    }
}
