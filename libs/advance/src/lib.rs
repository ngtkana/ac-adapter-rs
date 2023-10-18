//! しゃくとり法ユーティルです。
//!
//! # Contents
//!
//! * 添字を進める関数: [`advance_until`]
//! * それプラス通った要素を訪問する版: [`advance_visit_until`]

/// `checker` が `true` になるか配列をはみ出すまで添字を進めます。
///
/// # 効果
///
/// `checker(i)` が `true` になるか `a.len() == i` となるまで、`i` をインクリメントし続けます。
///
/// # Examples
///
/// ```
/// use advance::advance_until;
///
/// let a = [0, 1, 3, 6, 10, 15];
///
/// let mut i = 0;
/// advance_until(&mut i, &a, |&x| 10 <= x);
///
/// assert_eq!(i, 4); // 添字が 4 まで進みます。
/// ```
pub fn advance_until<T>(i: &mut usize, a: &[T], checker: impl FnMut(&T) -> bool) {
    *i = a[*i..].iter().position(checker).map_or(a.len(), |d| *i + d);
}

/// [`advance_until`] を呼んだあと、進んだ箇所すべてを訪問します。
///
/// # 効果
///
/// 次の 2 つが順に起こります。
///
/// 1. [`advance_until`] が呼ばれます。
/// 2. 変化する前の `i` を `orig_i` とするとき、`orig_i <= j < i` なる各 `j` に対して、`visitor(j,
///    &a[j])` を呼びます。
///
/// # Examples
///
/// ```
/// use advance::advance_visit_until;
///
/// let a = [0, 1, 3, 6, 10, 15];
///
/// let mut i = 0;
/// let mut visited = Vec::new();
/// advance_visit_until(&mut i, &a, |&x| 10 <= x, |i, &x| visited.push((i, x)));
///
/// assert_eq!(i, 4);   // 添字が 4 まで進みます。
/// assert_eq!(visited, vec![(0, 0), (1, 1), (2, 3), (3, 6)]);  // 添字 0, 1, 2, 3 を訪問します。
/// ```
pub fn advance_visit_until<T>(
    i: &mut usize,
    a: &[T],
    checker: impl FnMut(&T) -> bool,
    mut visitor: impl FnMut(usize, &T),
) {
    let orig_i = *i;
    advance_until(i, a, checker);
    a[orig_i..*i]
        .iter()
        .enumerate()
        .for_each(|(d, x)| visitor(orig_i + d, x));
}

#[cfg(test)]
mod tests {
    use super::advance_visit_until;
    use itertools::Itertools;

    #[test]
    fn test_advance_visit_until() {
        let a = (0..6).map(Element).collect_vec();

        let mut i = 0;
        let mut advance = |end: usize| -> (Vec<Element>, Vec<(usize, Element)>) {
            let mut checked = Vec::new();
            let mut visited = Vec::new();
            advance_visit_until(
                &mut i,
                &a,
                |&x| {
                    checked.push(x);
                    x == Element(end)
                },
                |i, &x| visited.push((i, x)),
            );
            (checked, visited)
        };

        let (checked, visited) = advance(2);
        assert_eq!(checked, vec![Element(0), Element(1), Element(2)]);
        assert_eq!(visited, vec![(0, Element(0)), (1, Element(1))]);

        let (checked, visited) = advance(2);
        assert_eq!(checked, vec![Element(2)]);
        assert_eq!(visited, Vec::<(usize, Element)>::new());

        let (checked, visited) = advance(3);
        assert_eq!(checked, vec![Element(2), Element(3)]);
        assert_eq!(visited, vec![(2, Element(2))]);

        let (checked, visited) = advance(6);
        assert_eq!(checked, vec![Element(3), Element(4), Element(5)]);
        assert_eq!(visited, vec![
            (3, Element(3)),
            (4, Element(4)),
            (5, Element(5))
        ]);
    }

    #[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
    struct Element(usize);
}
