use core::fmt;

const GRAY: &str = "\x1b[48;2;127;127;127;37m";
const RESET: &str = "\x1b[0m";

pub struct Table {
    pub table: Vec<Vec<Cell>>,
}

pub struct Cell {
    pub text: String,
    pub align: Align,
}

pub enum Align {
    Left,
    Center,
    Right,
}

impl fmt::Display for Table {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        struct ColumnFormat<'a> {
            pre: &'a str,
            width: usize,
            post: &'a str,
        }
        let Self { table } = self;
        let w = table[0].len();
        assert!(table.iter().all(|row| row.len() == w));
        let column_format = (0..w)
            .map(|j| ColumnFormat {
                pre: " ",
                width: table
                    .iter()
                    .map(|row| row[j].text.len().max(1))
                    .max()
                    .unwrap(),
                post: if j == 0 { " │" } else { " " },
            })
            .collect::<Vec<_>>();
        for (i, row) in table.iter().enumerate() {
            if i == 0 {
                write!(f, "{GRAY}")?;
            }
            for (&ColumnFormat { pre, width, post }, Cell { text, align }) in
                column_format.iter().zip(row)
            {
                write!(f, "{pre}")?;
                match align {
                    Align::Left => write!(f, "{text:<width$}")?,
                    Align::Center => write!(f, "{text:^width$}")?,
                    Align::Right => write!(f, "{text:>width$}")?,
                }
                write!(f, "{post}")?;
            }
            if i == 0 {
                write!(f, "{RESET}")?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}
