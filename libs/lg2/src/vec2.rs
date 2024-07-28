use crate::align_of;
use crate::format;
use crate::table::Align;
use crate::table::Cell;
use crate::table::Table;
use std::fmt;
use std::iter;

pub fn vec2<'a, T, R, S>(title: &str, vec2: &'a S) -> Table
where
    T: fmt::Debug + 'a,
    &'a R: Copy + IntoIterator<Item = &'a T> + 'a,
    &'a S: Copy + IntoIterator<Item = &'a R>,
{
    let w = vec2
        .into_iter()
        .map(|row| row.into_iter().count())
        .max()
        .unwrap();
    Table {
        table: iter::once(
            iter::once(Cell {
                text: title.to_string(),
                align: Align::Left,
            })
            .chain((0..w).map(|i| Cell {
                text: i.to_string(),
                align: Align::Center,
            }))
            .collect(),
        )
        .chain(vec2.into_iter().enumerate().map(|(j, row)| {
            iter::once(Cell {
                text: j.to_string(),
                align: Align::Center,
            })
            .chain(row.into_iter().map(|v| {
                let v = format(&v);
                Cell {
                    align: align_of(&v),
                    text: v,
                }
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
