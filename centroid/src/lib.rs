#![warn(missing_docs)]
#![warn(missing_doc_code_examples)]

//! 重心や重心分解を計算します。
//!
//! いずれの場合も、ブランチリストはもとのグラフの隣接リストにおける順番と同じになります。
//!
//! # 重心が頂点の場合
//!
//! 第一成分のヴァリアントは [`Vertex`] で、ここには重心の頂点番号が入ります。
//! 第二成分は重心から出ているブランチがすべて入ります。
//!
//! ## Examples
//!
//! ```
//! use centroid::{Branch, Centroid};
//! let g = [
//!     vec![1, 2, 3],
//!     vec![0],
//!     vec![0],
//!     vec![0],
//! ];
//! assert_eq!(
//!     centroid::centroid(&g, 2),
//!     (
//!         Centroid::Vertex(0),
//!         vec![
//!             Branch { root: 1, size: 1 },
//!             Branch { root: 2, size: 1 },
//!             Branch { root: 3, size: 1 },
//!         ]
//!     )
//! );
//! ```
//!
//! # 重心が辺の場合
//!
//! 第一成分のヴァリアントは [`Edge`] で、ここには `(x, p) =  (根から遠い方, 根に近い方)`
//! が入ります。 第二成分は x から出ているブランチがすべて入ります。これは p を根とするサイズちょうど半分のブランチも含みます。
//!
//! ## Examples
//!
//! ```
//! use centroid::{Branch, Centroid};
//! let g = [
//!     vec![1, 2, 5],
//!     vec![0],
//!     vec![0],
//!     vec![5],
//!     vec![5],
//!     vec![4, 3, 0],
//! ];
//! assert_eq!(
//!     centroid::centroid(&g, 2),
//!     (
//!         Centroid::Edge(5, 0),
//!         vec![
//!             Branch { root: 4, size: 1 },
//!             Branch { root: 3, size: 1 },
//!             Branch { root: 0, size: 3 },
//!         ]
//!     )
//! );
//! ```
//!
//! [`Vertex`]: enum.Centroid.html#variant.Vertex
//! [`Edge`]: enum.Centroid.html#variant.Edge

use std::cmp::{Eq, PartialEq};

/// 頂点または辺です。
/// [`centroid`] の戻り値型の一部です。
///
/// [`centroid`]: fn.centroid.html
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Centroid {
    /// 重心が頂点のときはこちらです。
    Vertex(usize),
    /// 重心が辺のときはこちらです。
    Edge(usize, usize),
}

/// [`centroid`] の戻り値型の一部です。
///
/// [`centroid`]: fn.centroid.html
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub struct Branch {
    /// 根の頂点番号です。
    pub root: usize,
    /// ブランチのサイズです。
    pub size: usize,
}

/// 根付き木を受け取って、重心とブランチリストを返します
///
/// 詳しくは [`Crate centroid`] までです。
///
/// [`Crate centroid`]: index.html
pub fn centroid(g: &[Vec<usize>], root: usize) -> (Centroid, Vec<Branch>) {
    let mut ans = None;
    let mut size = vec![0; g.len()];
    fn dfs(
        x: usize,
        p: usize,
        g: &[Vec<usize>],
        ans: &mut Option<Centroid>,
        size: &mut [usize],
    ) -> usize {
        let mut sx = 1;
        for y in g[x].iter().copied().filter(|&y| y != p) {
            sx += dfs(y, x, g, ans, size);
        }
        if g.len() <= sx * 2 {
            ans.get_or_insert_with(|| {
                if g.len() == sx * 2 {
                    Centroid::Edge(x, p)
                } else {
                    Centroid::Vertex(x)
                }
            });
        }
        size[x] = sx;
        sx
    }
    dfs(root, root, &g, &mut ans, &mut size);

    let centroid = ans.unwrap();
    let further_from_the_root = match centroid {
        Centroid::Vertex(x) => x,
        Centroid::Edge(x, _) => x,
    };
    let branches = g[further_from_the_root]
        .iter()
        .map(|&y| Branch {
            root: y,
            size: if g.len() <= size[y] * 2 {
                g.len() - size[further_from_the_root]
            } else {
                size[y]
            },
        })
        .collect();
    (centroid, branches)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_centroid_typical() {
        assert_eq!(
            centroid(&[Vec::new()], 0),
            (Centroid::Vertex(0), Vec::new())
        );
        assert_eq!(
            centroid(&[vec![1], vec![0]], 0),
            (Centroid::Edge(1, 0), vec![Branch { root: 0, size: 1 }])
        );
        assert_eq!(
            centroid(&[vec![1], vec![0, 2], vec![1]], 0),
            (
                Centroid::Vertex(1),
                vec![Branch { root: 0, size: 1 }, Branch { root: 2, size: 1 }]
            )
        );
        assert_eq!(
            centroid(&[vec![1, 2, 3], vec![0], vec![0], vec![0]], 0),
            (
                Centroid::Vertex(0),
                vec![
                    Branch { root: 1, size: 1 },
                    Branch { root: 2, size: 1 },
                    Branch { root: 3, size: 1 },
                ]
            )
        );
        assert_eq!(
            centroid(
                &[
                    vec![1, 2, 5],
                    vec![0],
                    vec![0],
                    vec![5],
                    vec![5],
                    vec![4, 3, 0],
                ],
                0
            ),
            (
                Centroid::Edge(5, 0),
                vec![
                    Branch { root: 4, size: 1 },
                    Branch { root: 3, size: 1 },
                    Branch { root: 0, size: 3 },
                ]
            )
        );
    }
}
