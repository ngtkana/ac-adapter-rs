//! 多次元コンテナを固定長インデックス配列付きで列挙するイテレータ。

/// 多次元コンテナの各要素を `([usize; D], Item)` として列挙する。
///
/// `D` は次元数。インデックスは `Vec` でなく固定長配列 `[usize; D]` で返す。
/// `Self` は `Vec` に限定されず、`&'a Self` がネストした `IntoIterator` になっている型であれば実装される。
///
/// 内側の型自体が `Copy`（固定長配列など）の場合、`D` の異なる複数の実装が同時に候補となり、
/// 型推論だけでは `D` が決まらないことがある。その場合は
/// `JaggedIterator::<D>::jagged_enumerate(&x)` のようにフルパスで `D` を指定する。
///
/// `D` は 1〜8 の実装を用意している。さらに大きい `D` が必要な場合は
/// `impl_jagged_iterators!(i0, ..., i8)` の ident 列を1つ増やすだけでよい。
///
/// # Examples
///
/// 1 次元（`Vec<i32>`）:
///
/// ```
/// use jagged_iterator::JaggedIterator;
///
/// let v = vec![10, 20, 30];
/// let result = v.jagged_enumerate().collect::<Vec<_>>();
/// assert_eq!(result, vec![([0], 10), ([1], 20), ([2], 30)]);
/// ```
///
/// 2 次元（`Vec<Vec<i32>>`）:
///
/// ```
/// use jagged_iterator::JaggedIterator;
///
/// let v = vec![vec![1, 2], vec![3, 4, 5]];
/// let result = v.jagged_enumerate().collect::<Vec<_>>();
/// assert_eq!(result, vec![
///     ([0, 0], 1), ([0, 1], 2),
///     ([1, 0], 3), ([1, 1], 4), ([1, 2], 5),
/// ]);
/// ```
///
/// 3 次元（`Vec<Vec<Vec<i32>>>`）:
///
/// ```
/// use jagged_iterator::JaggedIterator;
///
/// let v = vec![vec![vec![1, 2], vec![3]], vec![vec![4, 5, 6]]];
/// let result = v.jagged_enumerate().collect::<Vec<_>>();
/// assert_eq!(result, vec![
///     ([0, 0, 0], 1), ([0, 0, 1], 2),
///     ([0, 1, 0], 3),
///     ([1, 0, 0], 4), ([1, 0, 1], 5), ([1, 0, 2], 6),
/// ]);
/// ```
pub trait JaggedIterator<'a, const D: usize> {
    /// 列挙される要素の型。
    type Item: Copy + 'a;

    /// 各要素を `([usize; D], Item)` として列挙するイテレータを返す。
    fn jagged_enumerate(&'a self) -> impl Iterator<Item = ([usize; D], Self::Item)>;
}

/// `jagged_enumerate` の本体を、ネストした `enumerate().flat_map(...)` の連鎖として組み立てる。
///
/// 末端では `enumerate().map(...)` でインデックス配列 `[$acc.., $last]` と要素を返す。
/// 途中段では `enumerate().flat_map(...)` で自分のインデックスを `move` キャプチャしつつ、
/// 内側のコンテナに対して同じ処理を再帰的に展開する。
macro_rules! jagged_iterator_body {
    ($self_expr:expr; [$($acc:ident),*]; $last:ident) => {
        $self_expr
            .into_iter()
            .enumerate()
            .map(move |($last, &x)| ([$($acc,)* $last], x))
    };
    ($self_expr:expr; [$($acc:ident),*]; $head:ident, $($tail:ident),+) => {
        $self_expr.into_iter().enumerate().flat_map(move |($head, row)| {
            jagged_iterator_body!(row; [$($acc,)* $head]; $($tail),+)
        })
    };
}

/// `D` 次元分の `JaggedIterator` 実装を生成する。
///
/// `where` 句はマクロ内で再帰的に、`&'a I: IntoIterator` を1段ずつネストした
/// 境界として組み立てる（例えば `D = 3` なら `&'a I`, `<&'a I as IntoIterator>::Item`,
/// `<<&'a I as IntoIterator>::Item as IntoIterator>::Item` の3段）。
/// 最後の段だけ `IntoIterator<Item = &'a T>` を要求する。
///
/// `$D` は `usize` の式（[`impl_jagged_iterators`] からは `1 + 1 + ...` の形で渡される）。
/// トレイトの const generic 引数は式なら `{ }` で囲む必要があるが、配列長は不要。
/// `$D` が単なるリテラルに簡約される場合（`D = 1`）は `{ }` が不要になり
/// `unused_braces` の warning が出るため、生成する impl に `#[allow(unused_braces)]` を付ける。
macro_rules! impl_jagged_iterator {
    ($D:expr; $($idx:ident),+ $(,)?) => {
        impl_jagged_iterator!(@emit $D; ($($idx),+); &'a I; []; $($idx),+);
    };
    (@emit $D:expr; ($($all:ident),+); $cur:ty; [$($bounds:tt)*]; $head:ident, $($tail:ident),+) => {
        impl_jagged_iterator!(
            @emit $D; ($($all),+); <$cur as IntoIterator>::Item;
            [$($bounds)* $cur: IntoIterator,];
            $($tail),+
        );
    };
    (@emit $D:expr; ($($all:ident),+); $cur:ty; [$($bounds:tt)*]; $last:ident) => {
        #[allow(unused_braces)]
        impl<'a, I: ?Sized + 'a, T: Copy + 'a> JaggedIterator<'a, { $D }> for I
        where
            $($bounds)*
            $cur: IntoIterator<Item = &'a T>,
        {
            type Item = T;

            fn jagged_enumerate(&'a self) -> impl Iterator<Item = ([usize; $D], Self::Item)> {
                jagged_iterator_body!(self; []; $($all),+)
            }
        }
    };
}

/// [`impl_jagged_iterator`] を `D = 1` から idents の個数分だけ再帰的に呼び出す。
///
/// idents 列を1つずつ先頭から取り出し、その時点までの累積個数（`1`, `1 + 1`, ...）を
/// `D` として渡す。呼び出しコードは idents 列を1度書くだけでよく、`D` を明示する必要がない。
macro_rules! impl_jagged_iterators {
    (@step $count:expr; [$($acc:ident),+]) => {
        impl_jagged_iterator!($count; $($acc),+);
    };
    (@step $count:expr; [$($acc:ident),+] $head:ident $(, $tail:ident)*) => {
        impl_jagged_iterator!($count; $($acc),+);
        impl_jagged_iterators!(@step $count + 1; [$($acc,)+ $head] $($tail),*);
    };
    ($head:ident $(, $tail:ident)*) => {
        impl_jagged_iterators!(@step 1; [$head] $($tail),*);
    };
}

impl_jagged_iterators!(i0, i1, i2, i3, i4, i5, i6, i7);

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::VecDeque;

    #[test]
    fn test_1d_vec() {
        let v = vec![10, 20, 30];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result, vec![([0], 10), ([1], 20), ([2], 30)]);
    }

    #[test]
    fn test_1d_array() {
        let v = [10, 20, 30];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result, vec![([0], 10), ([1], 20), ([2], 30)]);
    }

    #[test]
    fn test_1d_slice() {
        let v: &[i32] = &[10, 20, 30];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result, vec![([0], 10), ([1], 20), ([2], 30)]);
    }

    #[test]
    fn test_1d_vec_deque() {
        let v = VecDeque::from(vec![10, 20, 30]);
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result, vec![([0], 10), ([1], 20), ([2], 30)]);
    }

    #[test]
    fn test_1d_empty() {
        let v: Vec<i32> = vec![];
        assert_eq!(v.jagged_enumerate().collect::<Vec<_>>(), vec![]);
    }

    #[test]
    fn test_2d_vec_of_vec() {
        let v = vec![vec![1, 2], vec![3, 4, 5]];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(
            result,
            vec![
                ([0, 0], 1),
                ([0, 1], 2),
                ([1, 0], 3),
                ([1, 1], 4),
                ([1, 2], 5),
            ]
        );
    }

    #[test]
    fn test_2d_array_of_array() {
        let v = [[1, 2], [3, 4]];
        // 行の型 `[i32; 2]` 自体が `Copy` なので `JaggedIterator<'_, 1>` も候補になり、
        // フルパス指定なしでは `D` を推論できない。
        let result = JaggedIterator::<2>::jagged_enumerate(&v).collect::<Vec<_>>();
        assert_eq!(
            result,
            vec![([0, 0], 1), ([0, 1], 2), ([1, 0], 3), ([1, 1], 4),]
        );
    }

    #[test]
    fn test_2d_vec_of_array() {
        let v = vec![[1, 2, 3], [4, 5, 6]];
        let result = JaggedIterator::<2>::jagged_enumerate(&v).collect::<Vec<_>>();
        assert_eq!(
            result,
            vec![
                ([0, 0], 1),
                ([0, 1], 2),
                ([0, 2], 3),
                ([1, 0], 4),
                ([1, 1], 5),
                ([1, 2], 6),
            ]
        );
    }

    #[test]
    fn test_2d_ragged() {
        let v = vec![vec![1], vec![], vec![2, 3]];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result, vec![([0, 0], 1), ([2, 0], 2), ([2, 1], 3)]);
    }

    #[test]
    fn test_3d_vec_of_vec_of_vec() {
        let v = vec![vec![vec![1, 2], vec![3]], vec![vec![4, 5, 6]]];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(
            result,
            vec![
                ([0, 0, 0], 1),
                ([0, 0, 1], 2),
                ([0, 1, 0], 3),
                ([1, 0, 0], 4),
                ([1, 0, 1], 5),
                ([1, 0, 2], 6),
            ]
        );
    }

    #[test]
    fn test_3d_ragged() {
        let v = vec![vec![vec![1], vec![]], vec![]];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result, vec![([0, 0, 0], 1)]);
    }

    #[test]
    fn test_4d_shape_2x2x2x2() {
        // 各要素の値を i0*8 + i1*4 + i2*2 + i3 で置いた 2x2x2x2 の入れ子 Vec。
        let v: Vec<Vec<Vec<Vec<i32>>>> = (0..2)
            .map(|i0| {
                (0..2)
                    .map(|i1| {
                        (0..2)
                            .map(|i2| (0..2).map(|i3| i0 * 8 + i1 * 4 + i2 * 2 + i3).collect())
                            .collect()
                    })
                    .collect()
            })
            .collect();
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result.len(), 16);
        for (idx, x) in result {
            let [i0, i1, i2, i3] = idx.map(|i| i as i32);
            assert_eq!(x, i0 * 8 + i1 * 4 + i2 * 2 + i3);
        }
    }

    #[test]
    fn test_8d_single_element() {
        let v = vec![vec![vec![vec![vec![vec![vec![vec![42]]]]]]]];
        let result = v.jagged_enumerate().collect::<Vec<_>>();
        assert_eq!(result, vec![([0, 0, 0, 0, 0, 0, 0, 0], 42)]);
    }
}
