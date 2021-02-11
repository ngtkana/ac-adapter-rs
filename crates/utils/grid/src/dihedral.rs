use std::{convert::TryFrom, ops::Mul};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Dihedral {
    R0,
    R1,
    R2,
    R3,
    R0S,
    R1S,
    R2S,
    R3S,
}
impl TryFrom<u8> for Dihedral {
    type Error = u8;
    fn try_from(value: u8) -> Result<Self, Self::Error> {
        Ok(match value {
            0 => Self::R0,
            1 => Self::R1,
            2 => Self::R2,
            3 => Self::R3,
            4 => Self::R0S,
            5 => Self::R1S,
            6 => Self::R2S,
            7 => Self::R3S,
            x => return Err(x),
        })
    }
}
impl Into<u8> for Dihedral {
    fn into(self) -> u8 {
        match self {
            Self::R0 => 0,
            Self::R1 => 1,
            Self::R2 => 2,
            Self::R3 => 3,
            Self::R0S => 4,
            Self::R1S => 5,
            Self::R2S => 6,
            Self::R3S => 7,
        }
    }
}

impl Mul for Dihedral {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self::try_from(dihedral_mul(self.into(), rhs.into())).unwrap()
    }
}

fn dihedral_mul(x: u8, y: u8) -> u8 {
    match (x.checked_sub(4), y.checked_sub(4)) {
        (None, None) => z4_add(x, y),
        (None, Some(y)) => z4_add(x, y) + 4,
        (Some(x), None) => z4_sub(x, y) + 4,
        (Some(x), Some(y)) => z4_sub(x, y),
    }
}

fn z4_add(x: u8, y: u8) -> u8 {
    if x + y < 4 {
        x + y
    } else {
        x + y - 4
    }
}
fn z4_sub(x: u8, y: u8) -> u8 {
    if x >= y {
        x - y
    } else {
        x + 4 - y
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{dihedral_mul, z4_add, z4_sub, Dihedral},
        test_case::test_case,
    };

    #[test_case(0, 0 => 0)]
    #[test_case(0, 1 => 1)]
    #[test_case(0, 2 => 2)]
    #[test_case(0, 3 => 3)]
    #[test_case(1, 0 => 1)]
    #[test_case(1, 1 => 2)]
    #[test_case(1, 2 => 3)]
    #[test_case(1, 3 => 0)]
    #[test_case(2, 0 => 2)]
    #[test_case(2, 1 => 3)]
    #[test_case(2, 2 => 0)]
    #[test_case(2, 3 => 1)]
    #[test_case(3, 0 => 3)]
    #[test_case(3, 1 => 0)]
    #[test_case(3, 2 => 1)]
    #[test_case(3, 3 => 2)]
    fn test_z4_add(x: u8, y: u8) -> u8 {
        z4_add(x, y)
    }

    #[test_case(0, 0 => 0)]
    #[test_case(0, 1 => 3)]
    #[test_case(0, 2 => 2)]
    #[test_case(0, 3 => 1)]
    #[test_case(1, 0 => 1)]
    #[test_case(1, 1 => 0)]
    #[test_case(1, 2 => 3)]
    #[test_case(1, 3 => 2)]
    #[test_case(2, 0 => 2)]
    #[test_case(2, 1 => 1)]
    #[test_case(2, 2 => 0)]
    #[test_case(2, 3 => 3)]
    #[test_case(3, 0 => 3)]
    #[test_case(3, 1 => 2)]
    #[test_case(3, 2 => 1)]
    #[test_case(3, 3 => 0)]
    fn test_z4_sub(x: u8, y: u8) -> u8 {
        z4_sub(x, y)
    }

    #[test_case(0, 0 => 0)]
    #[test_case(0, 1 => 1)]
    #[test_case(0, 2 => 2)]
    #[test_case(0, 3 => 3)]
    #[test_case(0, 4 => 4)]
    #[test_case(0, 5 => 5)]
    #[test_case(0, 6 => 6)]
    #[test_case(0, 7 => 7)]
    #[test_case(1, 0 => 1)]
    #[test_case(1, 1 => 2)]
    #[test_case(1, 2 => 3)]
    #[test_case(1, 3 => 0)]
    #[test_case(1, 4 => 5)]
    #[test_case(1, 5 => 6)]
    #[test_case(1, 6 => 7)]
    #[test_case(1, 7 => 4)]
    #[test_case(2, 0 => 2)]
    #[test_case(2, 1 => 3)]
    #[test_case(2, 2 => 0)]
    #[test_case(2, 3 => 1)]
    #[test_case(2, 4 => 6)]
    #[test_case(2, 5 => 7)]
    #[test_case(2, 6 => 4)]
    #[test_case(2, 7 => 5)]
    #[test_case(3, 0 => 3)]
    #[test_case(3, 1 => 0)]
    #[test_case(3, 2 => 1)]
    #[test_case(3, 3 => 2)]
    #[test_case(3, 4 => 7)]
    #[test_case(3, 5 => 4)]
    #[test_case(3, 6 => 5)]
    #[test_case(3, 7 => 6)]
    #[test_case(4, 0 => 4)]
    #[test_case(4, 1 => 7)]
    #[test_case(4, 2 => 6)]
    #[test_case(4, 3 => 5)]
    #[test_case(4, 4 => 0)]
    #[test_case(4, 5 => 3)]
    #[test_case(4, 6 => 2)]
    #[test_case(4, 7 => 1)]
    #[test_case(5, 0 => 5)]
    #[test_case(5, 1 => 4)]
    #[test_case(5, 2 => 7)]
    #[test_case(5, 3 => 6)]
    #[test_case(5, 4 => 1)]
    #[test_case(5, 5 => 0)]
    #[test_case(5, 6 => 3)]
    #[test_case(5, 7 => 2)]
    #[test_case(6, 0 => 6)]
    #[test_case(6, 1 => 5)]
    #[test_case(6, 2 => 4)]
    #[test_case(6, 3 => 7)]
    #[test_case(6, 4 => 2)]
    #[test_case(6, 5 => 1)]
    #[test_case(6, 6 => 0)]
    #[test_case(6, 7 => 3)]
    #[test_case(7, 0 => 7)]
    #[test_case(7, 1 => 6)]
    #[test_case(7, 2 => 5)]
    #[test_case(7, 3 => 4)]
    #[test_case(7, 4 => 3)]
    #[test_case(7, 5 => 2)]
    #[test_case(7, 6 => 1)]
    #[test_case(7, 7 => 0)]
    fn test_dihedral_mul(x: u8, y: u8) -> u8 {
        dihedral_mul(x, y)
    }

    #[test_case(Dihedral::R0, Dihedral::R0 => Dihedral::R0)]
    #[test_case(Dihedral::R0, Dihedral::R1 => Dihedral::R1)]
    #[test_case(Dihedral::R0, Dihedral::R2 => Dihedral::R2)]
    #[test_case(Dihedral::R0, Dihedral::R3 => Dihedral::R3)]
    #[test_case(Dihedral::R0, Dihedral::R0S => Dihedral::R0S)]
    #[test_case(Dihedral::R0, Dihedral::R1S => Dihedral::R1S)]
    #[test_case(Dihedral::R0, Dihedral::R2S => Dihedral::R2S)]
    #[test_case(Dihedral::R0, Dihedral::R3S => Dihedral::R3S)]
    #[test_case(Dihedral::R1, Dihedral::R0 => Dihedral::R1)]
    #[test_case(Dihedral::R1, Dihedral::R1 => Dihedral::R2)]
    #[test_case(Dihedral::R1, Dihedral::R2 => Dihedral::R3)]
    #[test_case(Dihedral::R1, Dihedral::R3 => Dihedral::R0)]
    #[test_case(Dihedral::R1, Dihedral::R0S => Dihedral::R1S)]
    #[test_case(Dihedral::R1, Dihedral::R1S => Dihedral::R2S)]
    #[test_case(Dihedral::R1, Dihedral::R2S => Dihedral::R3S)]
    #[test_case(Dihedral::R1, Dihedral::R3S => Dihedral::R0S)]
    #[test_case(Dihedral::R2, Dihedral::R0 => Dihedral::R2)]
    #[test_case(Dihedral::R2, Dihedral::R1 => Dihedral::R3)]
    #[test_case(Dihedral::R2, Dihedral::R2 => Dihedral::R0)]
    #[test_case(Dihedral::R2, Dihedral::R3 => Dihedral::R1)]
    #[test_case(Dihedral::R2, Dihedral::R0S => Dihedral::R2S)]
    #[test_case(Dihedral::R2, Dihedral::R1S => Dihedral::R3S)]
    #[test_case(Dihedral::R2, Dihedral::R2S => Dihedral::R0S)]
    #[test_case(Dihedral::R2, Dihedral::R3S => Dihedral::R1S)]
    #[test_case(Dihedral::R3, Dihedral::R0 => Dihedral::R3)]
    #[test_case(Dihedral::R3, Dihedral::R1 => Dihedral::R0)]
    #[test_case(Dihedral::R3, Dihedral::R2 => Dihedral::R1)]
    #[test_case(Dihedral::R3, Dihedral::R3 => Dihedral::R2)]
    #[test_case(Dihedral::R3, Dihedral::R0S => Dihedral::R3S)]
    #[test_case(Dihedral::R3, Dihedral::R1S => Dihedral::R0S)]
    #[test_case(Dihedral::R3, Dihedral::R2S => Dihedral::R1S)]
    #[test_case(Dihedral::R3, Dihedral::R3S => Dihedral::R2S)]
    #[test_case(Dihedral::R0S, Dihedral::R0 => Dihedral::R0S)]
    #[test_case(Dihedral::R0S, Dihedral::R1 => Dihedral::R3S)]
    #[test_case(Dihedral::R0S, Dihedral::R2 => Dihedral::R2S)]
    #[test_case(Dihedral::R0S, Dihedral::R3 => Dihedral::R1S)]
    #[test_case(Dihedral::R0S, Dihedral::R0S => Dihedral::R0)]
    #[test_case(Dihedral::R0S, Dihedral::R1S => Dihedral::R3)]
    #[test_case(Dihedral::R0S, Dihedral::R2S => Dihedral::R2)]
    #[test_case(Dihedral::R0S, Dihedral::R3S => Dihedral::R1)]
    #[test_case(Dihedral::R1S, Dihedral::R0 => Dihedral::R1S)]
    #[test_case(Dihedral::R1S, Dihedral::R1 => Dihedral::R0S)]
    #[test_case(Dihedral::R1S, Dihedral::R2 => Dihedral::R3S)]
    #[test_case(Dihedral::R1S, Dihedral::R3 => Dihedral::R2S)]
    #[test_case(Dihedral::R1S, Dihedral::R0S => Dihedral::R1)]
    #[test_case(Dihedral::R1S, Dihedral::R1S => Dihedral::R0)]
    #[test_case(Dihedral::R1S, Dihedral::R2S => Dihedral::R3)]
    #[test_case(Dihedral::R1S, Dihedral::R3S => Dihedral::R2)]
    #[test_case(Dihedral::R2S, Dihedral::R0 => Dihedral::R2S)]
    #[test_case(Dihedral::R2S, Dihedral::R1 => Dihedral::R1S)]
    #[test_case(Dihedral::R2S, Dihedral::R2 => Dihedral::R0S)]
    #[test_case(Dihedral::R2S, Dihedral::R3 => Dihedral::R3S)]
    #[test_case(Dihedral::R2S, Dihedral::R0S => Dihedral::R2)]
    #[test_case(Dihedral::R2S, Dihedral::R1S => Dihedral::R1)]
    #[test_case(Dihedral::R2S, Dihedral::R2S => Dihedral::R0)]
    #[test_case(Dihedral::R2S, Dihedral::R3S => Dihedral::R3)]
    #[test_case(Dihedral::R3S, Dihedral::R0 => Dihedral::R3S)]
    #[test_case(Dihedral::R3S, Dihedral::R1 => Dihedral::R2S)]
    #[test_case(Dihedral::R3S, Dihedral::R2 => Dihedral::R1S)]
    #[test_case(Dihedral::R3S, Dihedral::R3 => Dihedral::R0S)]
    #[test_case(Dihedral::R3S, Dihedral::R0S => Dihedral::R3)]
    #[test_case(Dihedral::R3S, Dihedral::R1S => Dihedral::R2)]
    #[test_case(Dihedral::R3S, Dihedral::R2S => Dihedral::R1)]
    #[test_case(Dihedral::R3S, Dihedral::R3S => Dihedral::R0)]
    fn test_impl_dihedral_mul(x: Dihedral, y: Dihedral) -> Dihedral {
        x * y
    }
}
