use rand::rngs::StdRng;

pub trait Params {}

#[derive(Debug, Clone)]
pub struct Test {
    rng: StdRng,
}

#[derive(Debug, Clone)]
pub struct Instant<Src, Dst> {
    src: Src,
    dst: Dst,
}
