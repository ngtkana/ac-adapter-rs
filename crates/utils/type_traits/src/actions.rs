use super::{binary::Len, Action, Commut, OpN};

/// アップデート作用です。
#[derive(Debug, Clone, PartialEq, Copy)]
pub struct Update<T>(pub T);

impl<T: OpN> Action for Update<T> {
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

impl<T: OpN + Commut> Action for Adjoint<T> {
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

    use crate::binary::Add;

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
    }
}
