#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! グリッドに関する操作を提供します。
//!
//! # 鏡映・回転
//!
//! D4 の元のうち恒等写像をのぞく 7 つの操作があります。
//!
//! ## 回転
//!
//! - [`rotate_left`] 90 度
//! - [`rotate_180`] 180 度
//! - [`rotate_right`] 270 度
//!
//! ## 鏡映
//!
//! - [`transpose`] 主対角線
//! - [`anti_transpose`] 反対角線
//! - [`reflect_vertically`] 縦線
//! - [`reflect_horizontally`] 横線
//!
//! [`rotate_left`]: fn.rotate_left.html
//! [`rotate_180`]: fn.rotate_180.html
//! [`rotate_right`]: fn.rotate_right.html
//! [`transpose`]: fn.transpose.html
//! [`anti_transpose`]: fn.anti_transpose.html
//! [`reflect_vertically`]: fn.reflect_vertically.html
//! [`reflect_horizontally`]: fn.reflect_horizontally.html

/// グリッドのサイズを取ります。
///
/// # Examples
///
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![0, 2, 4], vec![1, 3, 5]];
/// assert_eq!(exact_size_of_grid(&a), (3, 2));
/// assert_eq!(exact_size_of_grid(&b), (2, 3));
/// ```
///
/// # Panics
///
/// - 高さが 0 の場合
/// - 幅が揃っていない場合
///
/// ```should_panic
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3, 4], vec![5, 6]];    // a jagged array
/// exact_size_of_grid(&a);                             // panics
/// ```
pub fn exact_size_of_grid<T>(table: &[Vec<T>]) -> (usize, usize) {
    assert!(!table.is_empty());
    let w = table.first().unwrap().len();
    assert!(table.iter().all(|v| v.len() == w));
    (table.len(), w)
}

/// 主対角線に関する鏡映を返します。
///
/// # Examples
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![0, 2, 4], vec![1, 3, 5]];
/// assert_eq!(transpose(&a), b);
/// ```
pub fn transpose<T: Clone>(table: &[Vec<T>]) -> Vec<Vec<T>> {
    let (h, w) = exact_size_of_grid(&table);
    (0..w)
        .map(|j| (0..h).map(|i| table[i][j].clone()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

/// 反対角線に関する鏡映を返します。
///
/// # Examples
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![5, 3, 1], vec![4, 2, 0]];
/// assert_eq!(anti_transpose(&a), b);
/// ```
pub fn anti_transpose<T: Clone>(table: &[Vec<T>]) -> Vec<Vec<T>> {
    let (h, w) = exact_size_of_grid(&table);
    (0..w)
        .rev()
        .map(|j| {
            (0..h)
                .rev()
                .map(|i| table[i][j].clone())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}

/// 縦線に関する鏡映を返します。
///
/// # Examples
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![4, 2, 0], vec![5, 3, 1]];
/// assert_eq!(rotate_right(&a), b);
/// ```
pub fn reflect_vertically<T: Clone>(table: &[Vec<T>]) -> Vec<Vec<T>> {
    table
        .iter()
        .map(|v| v.iter().rev().cloned().collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

/// 横線に関する鏡映を返します。
///
/// # Examples
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![4, 5], vec![2, 3], vec![0, 1]];
/// assert_eq!(reflect_horizontally(&a), b);
/// ```
pub fn reflect_horizontally<T: Clone>(table: &[Vec<T>]) -> Vec<Vec<T>> {
    table.iter().rev().cloned().collect::<Vec<_>>()
}

/// 左に 90 度回転をします。
///
/// # Examples
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![1, 3, 5], vec![0, 2, 4]];
/// assert_eq!(rotate_left(&a), b);
/// ```
pub fn rotate_right<T: Clone>(table: &[Vec<T>]) -> Vec<Vec<T>> {
    let (h, w) = exact_size_of_grid(&table);
    (0..w)
        .map(|j| {
            (0..h)
                .rev()
                .map(|i| table[i][j].clone())
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>()
}

/// 右に 90 度回転をします。
///
/// # Examples
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![4, 2, 0], vec![5, 3, 1]];
/// assert_eq!(rotate_right(&a), b);
/// ```
pub fn rotate_left<T: Clone>(table: &[Vec<T>]) -> Vec<Vec<T>> {
    let (h, w) = exact_size_of_grid(&table);
    (0..w)
        .rev()
        .map(|j| (0..h).map(|i| table[i][j].clone()).collect::<Vec<_>>())
        .collect::<Vec<_>>()
}

/// 180 度回転します。
///
/// # Examples
/// ```
/// use gridtools::*;
/// let a = [vec![0, 1], vec![2, 3], vec![4, 5]];
/// let b = [vec![5, 4], vec![3, 2], vec![1, 0]];
/// assert_eq!(rotate_180(&a), b);
/// ```
pub fn rotate_180<T: Clone>(table: &[Vec<T>]) -> Vec<Vec<T>> {
    table
        .iter()
        .rev()
        .map(|v| v.iter().rev().cloned().collect::<Vec<_>>())
        .collect::<Vec<_>>()
}
