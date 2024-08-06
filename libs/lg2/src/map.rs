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

pub fn deconstruct_ref_tuple<K, V>((k, v): &(K, V)) -> (&K, &V) {
    (k, v)
}

pub trait Map<'a>: 'a {
    type K;
    type V;
    type I: Iterator<Item = (&'a Self::K, &'a Self::V)>;
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
