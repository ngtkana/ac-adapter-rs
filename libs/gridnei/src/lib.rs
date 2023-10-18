//! グリッドの様々な隣接セルを取得するライブラリです。
//!
//! # 隣接４マス
//!
//! 問題例: [AtCoder 典型 90 問 072 - Loop Railway Plan（★4）](https://atcoder.jp/contests/typical90/tasks/typical90_bt)
//!
//! 隣接４マスの取得だけ、専用の関数を用意しています。
//!
//! ```
//! use gridnei::grid4;
//! use gridnei::grid4encode;
//!
//! let result = grid4(1, 0, 3, 10).collect::<Vec<_>>();
//! let expected = vec![(0, 0), (1, 1), (2, 0)];
//! assert_eq!(result, expected);
//!
//! let result = grid4encode(10, 3, 10).collect::<Vec<_>>();
//! let expected = vec![0, 11, 20];
//! assert_eq!(result, expected);
//! ```
//!
//! # アレンジ
//!
//! ８マス以下ならこのように作れます。
//!
//! ```
//! use gridnei::Encode;
//! use gridnei::Grid8;
//!
//! fn knight(i: isize, j: isize) -> [(isize, isize); 8] {
//!     [
//!         (i - 1, j - 2),
//!         (i + 1, j - 2),
//!         (i - 2, j - 1),
//!         (i + 2, j - 1),
//!         (i - 2, j + 1),
//!         (i + 2, j + 1),
//!         (i - 1, j + 2),
//!         (i + 1, j + 2),
//!     ]
//! }
//!
//! // x.x........
//! // ...x.......
//! // .o.........
//! // ...x.......
//! let result = Grid8::from_fn(2, 1, 4, 10, knight).collect::<Vec<_>>();
//! let expected = vec![(0, 0), (0, 2), (1, 3), (3, 3)];
//! assert_eq!(&result, &expected);
//!
//! let result = Encode::<Grid8>::from_fn(21, 4, 10, knight).collect::<Vec<_>>();
//! let expected = vec![0, 2, 13, 33];
//! assert_eq!(&result, &expected);
//! ```

/// 新しい `Grid*` を定義して、[`GridIterator`] を実装します。
///
/// # Examples
///
/// ```
/// use gridnei::grid_iter;
/// grid_iter! { 17, Grid17 }
///
/// let _ = Grid17::from_fn(10, 3, 20, 8, |i, j| {
///     [
///         (i, j),
///         (i, j + 1),
///         (i, j + 2),
///         (i, j + 3),
///         (i, j + 4),
///         (i, j + 5),
///         (i, j + 6),
///         (i, j + 7),
///         (i, j + 8),
///         (i, j + 9),
///         (i, j + 10),
///         (i, j + 11),
///         (i, j + 12),
///         (i, j + 13),
///         (i, j + 14),
///         (i, j + 15),
///         (i, j + 15),
///     ]
/// })
/// .collect::<Vec<_>>();
/// ```
#[macro_export]
macro_rules! grid_iter {
    ($len:expr, $iter:ident $(,)?) => {
        pub struct $iter {
            data: [(isize, isize); $len],
            alive: std::ops::Range<usize>,
            h: isize,
            w: isize,
        }
        impl $iter {
            pub fn new(data: [(isize, isize); $len], h: usize, w: usize) -> Self {
                Self {
                    data,
                    alive: 0..$len,
                    h: h as isize,
                    w: w as isize,
                }
            }

            pub fn from_fn(
                i: usize,
                j: usize,
                h: usize,
                w: usize,
                mut f: impl FnMut(isize, isize) -> [(isize, isize); $len],
            ) -> Self {
                Self::new(f(i as isize, j as isize), h, w)
            }

            pub fn encode(self) -> $crate::Encode<Self> { $crate::Encode::new(self) }
        }
        impl Iterator for $iter {
            type Item = (usize, usize);

            fn next(&mut self) -> Option<Self::Item> {
                for t in &mut self.alive {
                    let &(i, j) = unsafe { self.data.get_unchecked(t) };
                    if (0..self.h).contains(&i) && (0..self.w).contains(&j) {
                        return Some((i as usize, j as usize));
                    }
                }
                None
            }

            fn size_hint(&self) -> (usize, Option<usize>) { (0, Some($len)) }
        }
        impl DoubleEndedIterator for $iter {
            fn next_back(&mut self) -> Option<Self::Item> {
                for t in (&mut self.alive).rev() {
                    let &(i, j) = unsafe { self.data.get_unchecked(t) };
                    if (0..self.h).contains(&i) && (0..self.w).contains(&j) {
                        return Some((i as usize, j as usize));
                    }
                }
                None
            }
        }
        impl $crate::GridIterator for $iter {
            type Array = [(isize, isize); $len];

            const LEN: usize = $len;

            fn w(&self) -> usize { self.w as usize }

            fn from_fn<F>(i: usize, j: usize, h: usize, w: usize, f: F) -> Self
            where
                F: FnMut(isize, isize) -> Self::Array,
            {
                Self::from_fn(i, j, h, w, f)
            }
        }
    };
}
grid_iter! { 0, Grid0 }
grid_iter! { 1, Grid1 }
grid_iter! { 2, Grid2 }
grid_iter! { 3, Grid3 }
grid_iter! { 4, Grid4 }
grid_iter! { 5, Grid5 }
grid_iter! { 6, Grid6 }
grid_iter! { 7, Grid7 }
grid_iter! { 8, Grid8 }

/// [`grid_iter!`] を通じで定義した型に自動的に実装されます。
pub trait GridIterator: DoubleEndedIterator<Item = (usize, usize)> {
    const LEN: usize;
    type Array;
    fn w(&self) -> usize;
    fn from_fn<F>(i: usize, j: usize, h: usize, w: usize, f: F) -> Self
    where
        F: FnMut(isize, isize) -> Self::Array;
}
/// 座標をエンコードした形で返すイテレータです。
///
/// # 構築する方法
///
/// - [`Encode::from_fn`] メソッド
/// - [`grid4encode`] 関数
///
/// # Examples
///
/// ```
/// use gridnei::Encode;
/// use gridnei::Grid2;
///
/// let result =
///     Encode::<Grid2>::from_fn(42, 1, 100, |i, j| [(i, j - 1), (i, j + 1)]).collect::<Vec<_>>();
/// let expected = vec![41, 43];
/// assert_eq!(&result, &expected);
/// ```
pub struct Encode<I>(I);
impl<I: GridIterator> Encode<I> {
    pub fn new(i: I) -> Self { Self(i) }

    pub fn from_fn<F>(x: usize, h: usize, w: usize, f: F) -> Self
    where
        F: FnMut(isize, isize) -> I::Array,
    {
        Self(I::from_fn(x / w, x % w, h, w, f))
    }
}
impl<I: GridIterator> Iterator for Encode<I> {
    type Item = usize;

    fn next(&mut self) -> Option<Self::Item> { self.0.next().map(move |(i, j)| i * self.0.w() + j) }

    fn size_hint(&self) -> (usize, Option<usize>) { (0, Some(I::LEN)) }
}
impl<I: GridIterator> DoubleEndedIterator for Encode<I> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(i, j)| i * self.0.w() + j)
    }
}
/// 隣接４マスをエンコードして返すイテレータを構築します。
///
/// # Examples
///
/// ```
/// use gridnei::grid4encode;
///
/// let result = grid4encode(21, 4, 10).collect::<Vec<_>>();
/// let expected = vec![11, 20, 22, 31];
/// assert_eq!(&result, &expected);
/// ```
pub fn grid4encode(x: usize, h: usize, w: usize) -> Encode<Grid4> {
    assert!(x < h * w);
    let (i, j) = (x / w, x % w);
    Encode(grid4(i, j, h, w))
}
/// 隣接４マスを返すイテレータを構築します。
///
/// # Examples
///
/// ```
/// use gridnei::grid4;
///
/// let result = grid4(2, 1, 4, 10).collect::<Vec<_>>();
/// let expected = vec![(1, 1), (2, 0), (2, 2), (3, 1)];
/// assert_eq!(&result, &expected);
/// ```
pub fn grid4(i: usize, j: usize, h: usize, w: usize) -> Grid4 {
    assert!(i < h && j < w);
    Grid4::from_fn(i, j, h, w, |i, j| {
        [(i - 1, j), (i, j - 1), (i, j + 1), (i + 1, j)]
    })
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
