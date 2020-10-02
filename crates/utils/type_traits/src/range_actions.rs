use super::{binary::Len, Commut, OpN, RangeAction};

/// アップデート作用です。
#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Update<T>(pub T);

impl<T: OpN> RangeAction for Update<T> {
    type Space = Len<T>;
    fn acted(self, x: Self::Space) -> Self::Space {
        Len {
            len: x.len,
            base: self.0.op_n(x.len),
        }
    }
}

/// 随伴作用です。
#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Adjoint<T>(pub T);

impl<T: OpN + Commut> RangeAction for Adjoint<T> {
    type Space = Len<T>;
    fn acted(self, x: Self::Space) -> Self::Space {
        Len {
            len: x.len,
            base: self.0.op_n(x.len).op(x.base),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::binary::{Add, BitXor};

    #[test]
    fn test_update() {
        assert_eq!(
            Update(Add(3)).acted(Len::single(Add(2))),
            Len::single(Add(3))
        );

        assert_eq!(
            Update(Add(3)).acted(Len {
                len: 2,
                base: Add(2)
            }),
            Len {
                len: 2,
                base: Add(6)
            }
        );

        assert_eq!(
            Update(BitXor(3)).acted(Len {
                len: 2,
                base: BitXor(2)
            }),
            Len {
                len: 2,
                base: BitXor(0)
            }
        );
    }

    #[test]
    fn test_adjoint() {
        assert_eq!(
            Adjoint(Add(3)).acted(Len::single(Add(2))),
            Len::single(Add(5))
        );

        assert_eq!(
            Adjoint(Add(3)).acted(Len {
                len: 2,
                base: Add(2)
            }),
            Len {
                len: 2,
                base: Add(8)
            }
        );

        assert_eq!(
            Adjoint(BitXor(3)).acted(Len {
                len: 2,
                base: BitXor(2)
            }),
            Len {
                len: 2,
                base: BitXor(2)
            }
        );
    }
}
