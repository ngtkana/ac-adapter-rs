mod coord;
mod dihedral;
mod grid;
mod iter;

pub use self::grid::Grid;
pub use dihedral::Dihedral;
pub use iter::{Row, RowIter, Rows};

use coord::{coord, Coord};

fn swap_size(d: Dihedral) -> bool {
    use Dihedral::{R0S, R1, R2S, R3};
    matches!(d, R1 | R3 | R0S | R2S)
}
