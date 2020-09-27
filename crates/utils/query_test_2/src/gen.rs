use rand::prelude::*;

/// 長さを生成します。
pub trait GenLen {
    #[allow(missing_docs)]
    fn gen_len<R: Rng>(rng: &mut R) -> usize;
}

/// 値を生成します。
pub trait GenValue<T> {
    #[allow(missing_docs)]
    fn gen_value<R: Rng>(rng: &mut R) -> T;
}
