//! 行列の積・べき乗、線形漸化式の行列表現（コンパニオン行列）。
//!
//! 要素の型は加減乗算そのものではなく、積和代入 $a \leftarrow a + bc$（[`Scalar::fma_assign`]）のみで
//! 抽象化している。通常の数値環だけでなく、（最小, +）などの半環でも「積和代入」を適切に定義すれば
//! 同じコードで行列積・べき乗が計算できる。行列積は積和代入を $O(hwp)$ 回適用して計算し、
//! べき乗は繰り返し二乗法により $O(\log n)$ 回の行列積に帰着する。
//!
//! # 仕様
//!
//! - 型: `Matrix<T>`（`items: Vec<T>` を行優先（row-major）で格納、`width: usize` は列数）
//! - [`Scalar`][]: 零元 `ZERO`、単位元 `ONE`、積和代入 `fma_assign(a, b, c)`（$a \leftarrow a + bc$）
//! - 生成: [`Matrix::zeros`]、[`Matrix::identity`]、[`Matrix::companion`]
//! - 演算: `&Matrix * &Matrix`（行列積）、[`Matrix::pow`]、[`Matrix::mul_pow_assign`]
//! - 添字アクセス: `matrix[i]`（$i$ 行目のスライス）、`matrix[(i, j)]`（成分）
//!
//! # 例
//!
//! ```
//! use matrix::Matrix;
//! use matrix::Scalar;
//!
//! #[derive(Clone)]
//! struct Int(i64);
//! impl Scalar for Int {
//!     const ZERO: Self = Self(0);
//!     const ONE: Self = Self(1);
//!     fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
//!         a.0 += b.0 * c.0;
//!     }
//! }
//!
//! let a = Matrix {
//!     items: vec![Int(1), Int(2), Int(3), Int(4)],
//!     width: 2,
//! };
//! let a2 = a.clone().pow(2); // [[1,2],[3,4]]^2
//! assert_eq!(a2.items.iter().map(|x| x.0).collect::<Vec<_>>(), vec![7, 10, 15, 22]);
//! ```
//!
//! # 計算量
//!
//! $h, w, p$ を行列の行数・共通次元・列数、$n$ をべき指数とする。
//!
//! - 行列積: $O(hwp)$
//! - [`Matrix::pow`]、[`Matrix::mul_pow_assign`][]: $O(w^3 \log n)$（正方行列の場合）
//! - [`Matrix::companion`][]: $O(k)$（$k$ は次数）

use std::ops::Mul;

/// 行列の要素が満たすべき演算：零元・単位元・積和代入。
///
/// 加算・乗算を個別に要求せず、積和代入 $a \leftarrow a + bc$（[`fma_assign`](Self::fma_assign)）のみを
/// 要求する。これにより通常の数値環だけでなく、（最小, +）などの半環にも適用できる。
pub trait Scalar {
    /// 零元 $0$（加算の単位元）。
    const ZERO: Self;
    /// 単位元 $1$（乗算の単位元）。単位行列の対角成分に使う。
    const ONE: Self;

    /// 積和代入 $a \leftarrow a + bc$ を行う。
    fn fma_assign(a: &mut Self, b: &Self, c: &Self);
}

/// 行優先（row-major）で格納した行列。
///
/// `items[i * width + j]` が $(i, j)$ 成分を表す。
///
/// # 例
///
/// ```
/// use matrix::Matrix;
/// let m = Matrix {
///     items: vec![1, 2, 3, 4, 5, 6],
///     width: 3,
/// };
/// assert_eq!(m.height(), 2);
/// assert_eq!(m[(1, 2)], 6);
/// ```
#[derive(Clone)]
pub struct Matrix<T> {
    /// 成分（行優先）。長さは `width` の倍数。
    pub items: Vec<T>,
    /// 列数 $w$。
    pub width: usize,
}

impl<T> Matrix<T> {
    /// 行数 $h$ を返す（$h = $ `items.len() / width`）。
    ///
    /// # 例
    ///
    /// ```
    /// use matrix::Matrix;
    /// let m = Matrix {
    ///     items: vec![0; 6],
    ///     width: 3,
    /// };
    /// assert_eq!(m.height(), 2);
    /// ```
    pub fn height(&self) -> usize {
        self.items.len() / self.width
    }
}

impl<T: Scalar> Matrix<T> {
    /// 零行列 $O_{h \times w}$（全成分が [`Scalar::ZERO`]）を生成する。
    ///
    /// # 例
    ///
    /// ```
    /// # use matrix::Scalar;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct N(i64);
    /// # impl Scalar for N {
    /// #     const ZERO: Self = Self(0);
    /// #     const ONE: Self = Self(1);
    /// #     fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
    /// #         a.0 += b.0 * c.0;
    /// #     }
    /// # }
    /// use matrix::Matrix;
    /// let m = Matrix::<N>::zeros(2, 3);
    /// assert_eq!(m.items, vec![N(0); 6]);
    /// assert_eq!(m.width, 3);
    /// ```
    pub fn zeros(height: usize, width: usize) -> Self {
        Self {
            items: (0..height * width).map(|_| T::ZERO).collect::<Vec<_>>(),
            width,
        }
    }

    /// $n \times n$ の単位行列 $I_n$ を生成する。対角成分が [`Scalar::ONE`]、それ以外が
    /// [`Scalar::ZERO`]。
    ///
    /// # 例
    ///
    /// ```
    /// # use matrix::Scalar;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct N(i64);
    /// # impl Scalar for N {
    /// #     const ZERO: Self = Self(0);
    /// #     const ONE: Self = Self(1);
    /// #     fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
    /// #         a.0 += b.0 * c.0;
    /// #     }
    /// # }
    /// use matrix::Matrix;
    /// let m = Matrix::<N>::identity(2);
    /// assert_eq!(m.items, vec![N(1), N(0), N(0), N(1)]);
    /// ```
    pub fn identity(size: usize) -> Self {
        let mut result = Self::zeros(size, size);
        for i in 0..size {
            result[(i, i)] = T::ONE;
        }
        result
    }

    /// 行列のべき乗 $A^n$ を繰り返し二乗法で計算する。
    ///
    /// `self` は正方行列（`width == height()`）である必要がある。
    ///
    /// # 例
    ///
    /// ```
    /// # use matrix::Scalar;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct N(i64);
    /// # impl Scalar for N {
    /// #     const ZERO: Self = Self(0);
    /// #     const ONE: Self = Self(1);
    /// #     fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
    /// #         a.0 += b.0 * c.0;
    /// #     }
    /// # }
    /// use matrix::Matrix;
    /// let a = Matrix {
    ///     items: vec![N(1), N(2), N(3), N(4)],
    ///     width: 2,
    /// };
    /// let a2 = a.pow(2); // [[1,2],[3,4]]^2
    /// assert_eq!(a2.items, vec![N(7), N(10), N(15), N(22)]);
    /// ```
    ///
    /// # 計算量
    ///
    /// $O(w^3 \log n)$（$w$ は行列の幅、$n$ は指数）
    pub fn pow(self, exp: u64) -> Self {
        let mut result = Self::identity(self.width);
        result.mul_pow_assign(self, exp);
        result
    }

    /// $\mathit{self} \leftarrow \mathit{self} \times \mathit{other}^n$ を繰り返し二乗法で計算する。
    ///
    /// `other` を $n$ 乗する過程で二乗した中間結果を `self` へ左から掛けていくことで、
    /// `other` の明示的なべき乗計算を経ずに済ませる（[`pow`](Self::pow) は本メソッドを単位行列に
    /// 適用したもの）。$n = 0$ のとき `self` は変化しない。
    ///
    /// # 例
    ///
    /// ```
    /// # use matrix::Scalar;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct N(i64);
    /// # impl Scalar for N {
    /// #     const ZERO: Self = Self(0);
    /// #     const ONE: Self = Self(1);
    /// #     fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
    /// #         a.0 += b.0 * c.0;
    /// #     }
    /// # }
    /// use matrix::Matrix;
    /// let mut m = Matrix::<N>::identity(2);
    /// let a = Matrix {
    ///     items: vec![N(1), N(2), N(3), N(4)],
    ///     width: 2,
    /// };
    /// m.mul_pow_assign(a, 2); // m <- I * [[1,2],[3,4]]^2
    /// assert_eq!(m.items, vec![N(7), N(10), N(15), N(22)]);
    /// ```
    pub fn mul_pow_assign(&mut self, mut other: Self, mut exp: u64) {
        if exp == 0 {
            return;
        }
        while exp != 1 {
            if exp & 1 == 1 {
                *self = &*self * &other;
            }
            other = &other * &other;
            exp >>= 1;
        }
        *self = &*self * &other;
    }

    /// 線形漸化式のコンパニオン行列を構成する。
    ///
    /// 係数 $\mathit{bottom} = (c_0, \ldots, c_{k-1})$ に対し、$k \times k$ 行列 $M$ を
    /// $M_{i, i-1} = 1$（$1 \le i < k$）、$M_{i, k-1} = c_i$（$0 \le i < k$）、それ以外を $0$ として
    /// 構成する。連続する $k$ 項からなる行ベクトル $u_n = (a_n, a_{n+1}, \ldots, a_{n+k-1})$ が
    /// 漸化式 $a_{n+k} = \sum_{i=0}^{k-1} c_i a_{n+i}$ を満たすとき $u_n M = u_{n+1}$ が成り立つため、
    /// $u_0 M^n$（[`pow`](Self::pow) 参照）の第 $0$ 成分から $a_n$ が求まる。
    ///
    /// # 例
    ///
    /// ```
    /// # use matrix::Scalar;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct N(i64);
    /// # impl Scalar for N {
    /// #     const ZERO: Self = Self(0);
    /// #     const ONE: Self = Self(1);
    /// #     fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
    /// #         a.0 += b.0 * c.0;
    /// #     }
    /// # }
    /// use matrix::Matrix;
    /// // a_{n+2} = a_n + a_{n+1}（フィボナッチ）
    /// let m = Matrix::companion(vec![N(1), N(1)]);
    /// assert_eq!(m.items, vec![N(0), N(1), N(1), N(1)]); // [[0,1],[1,1]]
    /// ```
    ///
    /// # Panics
    ///
    /// `bottom` が空のとき panic する。
    pub fn companion<I>(bottom: I) -> Self
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut iter = bottom.into_iter();
        let size = iter.len();
        assert!(size > 0);
        let mut result = Self::zeros(size, size);
        for i in 1..size {
            result[(i, i - 1)] = T::ONE;
        }
        for i in 0..size {
            result[(i, size - 1)] = iter.next().unwrap();
        }
        assert!(iter.next().is_none());
        result
    }
}

impl<T> std::ops::Index<usize> for Matrix<T> {
    type Output = [T];

    fn index(&self, i: usize) -> &Self::Output {
        &self.items[i * self.width..(i + 1) * self.width]
    }
}

impl<T> std::ops::IndexMut<usize> for Matrix<T> {
    fn index_mut(&mut self, i: usize) -> &mut Self::Output {
        &mut self.items[i * self.width..(i + 1) * self.width]
    }
}

impl<T> std::ops::Index<(usize, usize)> for Matrix<T> {
    type Output = T;

    fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
        &self.items[i * self.width + j]
    }
}

impl<T> std::ops::IndexMut<(usize, usize)> for Matrix<T> {
    fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
        &mut self.items[i * self.width + j]
    }
}

/// 行列積 $C = AB$（$C_{ik} = \sum_j A_{ij} B_{jk}$）。積和は [`Scalar::fma_assign`] で計算する。
///
/// `self.width == rhs.height()` を満たす必要がある。
///
/// # 例
///
/// ```
/// # use matrix::Scalar;
/// # #[derive(Clone, Debug, PartialEq)]
/// # struct N(i64);
/// # impl Scalar for N {
/// #     const ZERO: Self = Self(0);
/// #     const ONE: Self = Self(1);
/// #     fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
/// #         a.0 += b.0 * c.0;
/// #     }
/// # }
/// use matrix::Matrix;
/// let a = Matrix {
///     items: vec![N(1), N(2), N(3), N(4)],
///     width: 2,
/// };
/// let b = Matrix {
///     items: vec![N(5), N(6), N(7), N(8)],
///     width: 2,
/// };
/// let c = &a * &b;
/// assert_eq!(c.items, vec![N(19), N(22), N(43), N(50)]);
/// ```
///
/// # 計算量
///
/// $O(hwp)$（$h$: `self` の行数、$w$: `self.width`、$p$: `rhs.width`）
impl<'a, T: Scalar> Mul<&'a Matrix<T>> for &'a Matrix<T> {
    type Output = Matrix<T>;

    fn mul(self, rhs: &'a Matrix<T>) -> Self::Output {
        assert_eq!(self.width * rhs.width, rhs.items.len());
        let mut result = Matrix::zeros(self.height(), rhs.width);
        for i in 0..self.height() {
            for j in 0..self.width {
                for k in 0..rhs.width {
                    T::fma_assign(&mut result[(i, k)], &self[(i, j)], &rhs[(j, k)]);
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[derive(Clone, Debug)]
    struct Int(i32);
    impl Scalar for Int {
        const ZERO: Self = Self(0);
        const ONE: Self = Self(1);

        fn fma_assign(a: &mut Self, b: &Self, c: &Self) {
            a.0 += b.0 * c.0;
        }
    }
    impl PartialEq<i32> for Int {
        fn eq(&self, other: &i32) -> bool {
            self.0 == *other
        }
    }
    impl Int {
        fn vec<I>(iter: I) -> Vec<Self>
        where
            I: IntoIterator<Item = i32>,
        {
            iter.into_iter().map(Self).collect()
        }
    }

    #[test]
    fn test_matrix_mul_typed_int() {
        let a = Matrix {
            items: Int::vec([1, 2, 3, 4]),
            width: 2,
        };
        let b = Matrix {
            items: Int::vec([5, 6, 7, 8]),
            width: 2,
        };
        let c = &a * &b;
        assert_eq!(c.items, [19, 22, 43, 50]);
        assert_eq!(c.width, 2);
    }

    #[test]
    fn test_matrix_pow_typed_int() {
        let a = Matrix {
            items: Int::vec([1, 2, 3, 4]),
            width: 2,
        };

        let b = a.clone().pow(0);
        assert_eq!(b.items, [1, 0, 0, 1]);
        assert_eq!(b.width, 2);

        let b = a.clone().pow(1);
        assert_eq!(b.items, [1, 2, 3, 4]);
        assert_eq!(b.width, 2);

        let b = a.clone().pow(2);
        assert_eq!(b.items, [7, 10, 15, 22]);
        assert_eq!(b.width, 2);

        let b = a.pow(3);
        assert_eq!(b.items, [37, 54, 81, 118]);
        assert_eq!(b.width, 2);
    }
}
