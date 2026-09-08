use core::fmt;

const GRAY: &str = "\x1b[48;2;127;127;127;37m";
const RESET: &str = "\x1b[0m";

/// 罫線付きの表。`Display` でヘッダー行をグレー背景にして整形出力する。
///
/// 各行は同じ列数を持つ必要がある（`Display` の実装内で `assert!` する）。
pub struct Table {
    /// 行の集まり。各行は `Cell` の列。
    pub table: Vec<Vec<Cell>>,
}

/// `Table` の 1 セル。表示テキストと寄せ方向を持つ。
pub struct Cell {
    /// 表示テキスト。
    pub text: String,
    /// 寄せ方向。
    pub align: Align,
}

/// セルの寄せ方向。
pub enum Align {
    /// 左寄せ。
    Left,
    /// 中央寄せ。
    Center,
    /// 右寄せ（数値のセルに使う）。
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
