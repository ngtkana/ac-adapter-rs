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

/// キーを生成します。
pub trait GenKey<T> {
    #[allow(missing_docs)]
    fn gen_key<R: Rng>(rng: &mut R) -> T;
}

/// 作用素を生成します。
pub trait GenAction<T> {
    #[allow(missing_docs)]
    fn gen_action<R: Rng>(rng: &mut R) -> T;
}

/// 畳み込まれた値を生成します。
pub trait GenFoldedValue<T> {
    #[allow(missing_docs)]
    fn gen_folded_value<R: Rng>(rng: &mut R) -> T;
}

/// 畳み込まれたキーを生成します。
pub trait GenFoldedKey<T> {
    #[allow(missing_docs)]
    fn gen_folded_key<R: Rng>(rng: &mut R) -> T;
}
