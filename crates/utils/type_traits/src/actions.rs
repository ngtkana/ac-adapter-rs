use super::{Action, Assoc, Element, Identity};

/// 1 付加です。
impl<T: Action> Action for Option<T> {
    type Space = T::Space;
    fn acted(self, rhs: T::Space) -> T::Space {
        match self {
            Some(x) => x.acted(rhs),
            None => rhs,
        }
    }
}

/// 代入作用 （`x (y) = x` で定義される作用）です。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Update<T>(pub T);
triv_wrapper! { Update<T> }
impl<T: Element> Assoc for Update<T> {
    fn op(self, _rhs: Self) -> Self {
        self
    }
}
impl<T: Element> Action for Update<T> {
    type Space = T;
    fn acted(self, _rhs: T) -> T {
        self.0
    }
}

/// 随伴作用（`x (y) = x * y` で定義される作用）です。
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Adj<T>(pub T);
triv_wrapper! { Adj<T> }
impl<T: Assoc> Assoc for Adj<T> {
    fn op(self, rhs: Self) -> Self {
        Adj(self.0.op(rhs.0))
    }
}
impl<T: Identity> Identity for Adj<T> {
    fn identity() -> Self {
        Adj(T::identity())
    }
}
impl<T: Assoc> Action for Adj<T> {
    type Space = T;
    fn acted(self, rhs: T) -> T {
        self.0.op(rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_impl::assert_impl;

    #[test]
    fn test_update() {
        use crate::binary::Add;
        assert_impl!(Assoc: Update<()>);
        assert_impl!(!Identity: Update<()>);
        assert_impl!(Action<Space = ()>: Update<()>);

        assert_impl!(Assoc: Update<Add<u32>>);
        assert_impl!(!Identity: Update<Add<u32>>);
        assert_impl!(Action<Space = Add<u32>>: Update<Add<u32>>);

        assert_impl!(Assoc: Option<Update<()>>);
        assert_impl!(Identity: Option<Update<()>>);
        assert_impl!(Action<Space = ()>: Option<Update<()>>);

        assert_eq!(Update(3).acted(2), 3);
        assert_eq!(Some(Update(3)).acted(2), 3);
        assert_eq!(None::<Update<u32>>.acted(2), 2);
        assert_eq!(<Option<Update<u32>> as Identity>::identity(), None);
    }

    #[test]
    fn test_adj() {
        use crate::binary::Add;
        assert_impl!(!Assoc: Adj<()>);
        assert_impl!(!Identity: Adj<()>);
        assert_impl!(!Action: Adj<()>);

        assert_impl!(Assoc: Adj<Add<u32>>);
        assert_impl!(Identity: Adj<Add<u32>>);
        assert_impl!(Action<Space = Add<u32>>: Adj<Add<u32>>);

        assert_impl!(!Assoc: Option<Adj<()>>);
        assert_impl!(!Identity: Option<Adj<()>>);
        assert_impl!(!Action<Space = ()>: Option<Adj<()>>);

        assert_eq!(Adj(Add(3)).acted(Add(2)), Add(5));
        assert_eq!(Some(Adj(Add(3))).acted(Add(2)), Add(5));
        assert_eq!(None::<Adj<Add<u32>>>.acted(Add(2)), Add(2));
        assert_eq!(<Adj<Add<u32>> as Identity>::identity(), Adj(Add(0)));
        assert_eq!(<Option<Adj<Add<u32>>> as Identity>::identity(), None);
    }
}
