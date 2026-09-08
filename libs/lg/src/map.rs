use crate::align_of;
use crate::format;
use crate::table::Align;
use crate::table::Cell;
use crate::table::Table;
use std::collections;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt;
use std::iter;
use std::slice;
use std::vec;

/// マップを縦向きの表に変換する。1 行目に見出し、以降 1 行ずつ `キー | 値` を並べる。`vmap!` マクロの実体。
pub fn vmap<'a, K, V, M>(title: &str, map: M) -> Table
where
    M: Copy + Map<'a, K = K, V = V>,
    K: fmt::Debug,
    V: fmt::Debug,
{
    Table {
        table: iter::once(vec![
            Cell {
                text: String::new(),
                align: Align::Left,
            },
            Cell {
                text: title.to_string(),
                align: Align::Center,
            },
        ])
        .chain(map.map_iter().map(|(k, v)| {
            let v = format(&v);
            vec![
                Cell {
                    text: format(&k),
                    align: Align::Center,
                },
                Cell {
                    align: align_of(&v),
                    text: v,
                },
            ]
        }))
        .collect(),
    }
}

/// マップを横向きの表に変換する。1 行目にキーを、2 行目に値を並べる。`hmap!` マクロの実体。
pub fn hmap<'a, K, V, M>(title: &str, map: M) -> Table
where
    M: Copy + Map<'a, K = K, V = V>,
    K: fmt::Debug,
    V: fmt::Debug,
{
    Table {
        table: vec![
            iter::once(Cell {
                text: String::new(),
                align: Align::Left,
            })
            .chain(map.map_iter().map(|(k, _)| Cell {
                text: format(&k),
                align: Align::Center,
            }))
            .collect(),
            iter::once(Cell {
                text: title.to_string(),
                align: Align::Left,
            })
            .chain(map.map_iter().map(|(_, v)| {
                let v = format(&v);
                Cell {
                    align: align_of(&v),
                    text: v,
                }
            }))
            .collect(),
        ],
    }
}

/// `&(K, V)` を `(&K, &V)` に分解する。スライスや `Vec` に対する `Map::map_iter` の実装で使う。
pub fn deconstruct_ref_tuple<K, V>((k, v): &(K, V)) -> (&K, &V) {
    (k, v)
}

/// `vmap`/`hmap` がマップ的なコンテナを一様に走査するためのトレイト。
///
/// `HashMap`, `BTreeMap`, `&[(K, V)]`, `Vec<(K, V)>`, `[(K, V); N]` への参照に実装する。
pub trait Map<'a>: 'a {
    /// キーの型。
    type K;
    /// 値の型。
    type V;
    /// `(&K, &V)` を返すイテレータの型。
    type I: Iterator<Item = (&'a Self::K, &'a Self::V)>;
    /// キーと値のペアを走査するイテレータを返す。
    fn map_iter(self) -> Self::I;
}

impl<'a, K, V, S> Map<'a> for &'a HashMap<K, V, S> {
    type I = collections::hash_map::Iter<'a, K, V>;
    type K = K;
    type V = V;

    fn map_iter(self) -> Self::I {
        self.iter()
    }
}

impl<'a, K, V> Map<'a> for &'a BTreeMap<K, V> {
    type I = collections::btree_map::Iter<'a, K, V>;
    type K = K;
    type V = V;

    fn map_iter(self) -> Self::I {
        self.iter()
    }
}

impl<'a, K, V> Map<'a> for &'a [(K, V)] {
    type I = iter::Map<slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>;
    type K = K;
    type V = V;

    fn map_iter(self) -> Self::I {
        self.iter().map(deconstruct_ref_tuple)
    }
}

impl<'a, K, V> Map<'a> for &'a Vec<(K, V)> {
    type I = iter::Map<slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>;
    type K = K;
    type V = V;

    fn map_iter(self) -> Self::I {
        self.iter().map(deconstruct_ref_tuple)
    }
}

impl<'a, const N: usize, K, V> Map<'a> for &'a [(K, V); N] {
    type I = iter::Map<slice::Iter<'a, (K, V)>, fn(&(K, V)) -> (&K, &V)>;
    type K = K;
    type V = V;

    fn map_iter(self) -> Self::I {
        self.iter().map(deconstruct_ref_tuple)
    }
}
