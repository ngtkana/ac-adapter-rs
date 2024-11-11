use super::table::Cell;
use super::table::Table;
use crate::align_of;
use crate::table::Align;
use std::iter;

pub fn hvec(vecs: &[(String, Vec<String>)]) -> Table {
    let w = vecs.iter().map(|(_, row)| row.len()).max().unwrap();
    Table {
        table: iter::once(
            iter::once(Cell {
                text: String::new(),
                align: Align::Left,
            })
            .chain((0..w).map(|i| Cell {
                text: i.to_string(),
                align: Align::Center,
            }))
            .collect(),
        )
        .chain(vecs.iter().map(|(title, row)| {
            iter::once(Cell {
                text: title.to_string(),
                align: Align::Center,
            })
            .chain(row.iter().map(|v| Cell {
                align: align_of(v),
                text: v.clone(),
            }))
            .chain(iter::repeat_with(|| Cell {
                text: String::new(),
                align: Align::Left,
            }))
            .take(1 + w)
            .collect()
        }))
        .collect(),
    }
}

pub fn vvec(vecs: &[(String, Vec<String>)]) -> Table {
    let h = vecs.iter().map(|(_, col)| col.len()).max().unwrap();
    Table {
        table: iter::once(
            iter::once(Cell {
                text: String::new(),
                align: Align::Center,
            })
            .chain(vecs.iter().map(|(title, _)| Cell {
                text: title.to_string(),
                align: Align::Center,
            }))
            .collect(),
        )
        .chain((0..h).map(|i| {
            iter::once(Cell {
                text: i.to_string(),
                align: Align::Center,
            })
            .chain(vecs.iter().map(|(_, vec)| {
                let v = vec.get(i).map_or("", String::as_str);
                Cell {
                    align: align_of(v),
                    text: v.to_string(),
                }
            }))
            .collect()
        }))
        .collect(),
    }
}
