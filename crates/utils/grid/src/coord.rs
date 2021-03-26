use super::{swap_size, Dihedral};
use std::mem::swap;

#[derive(Clone, Debug, Default, Hash, PartialEq, Copy)]
pub struct Coord {
    pub origin: isize,
    pub x: isize,
    pub y: isize,
    pub h: usize,
    pub w: usize,
}
#[allow(clippy::many_single_char_names)]
pub fn coord(h: usize, w: usize, d: Dihedral) -> Coord {
    use Dihedral::*;
    let mut h = h as isize;
    let mut w = w as isize;
    let (origin, x, y) = match d {
        R0 => (0, w, 1),
        R1 => (w - 1, -1, w),
        R2 => (h * w - 1, -w, -1),
        R3 => ((h - 1) * w, 1, -w),
        R0S => (0, 1, w),
        R1S => (w - 1, w, -1),
        R2S => (h * w - 1, -1, -w),
        R3S => ((h - 1) * w, -w, 1),
    };
    if swap_size(d) {
        swap(&mut h, &mut w);
    }
    let h = h as usize;
    let w = w as usize;
    Coord { origin, x, y, h, w }
}
