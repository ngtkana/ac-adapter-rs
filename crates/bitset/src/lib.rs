//! Boolean 配列を [`u64`] のベクターに詰め込みます。
//!
//! [詳しくは `Bs` のドキュメントをご覧ください。](Bs)

use std::{
    fmt::Debug,
    iter::FromIterator,
    mem::replace,
    ops::{BitAndAssign, BitOrAssign, BitXorAssign, ShlAssign, ShrAssign},
};

/// Boolean 配列を [`u64`] のベクターに詰め込んだものです。
///
/// # 使い方
///
/// 構造体のメソッド以外にも、
/// `<<=`, `>>=`, `|=`, `&=`, `^=` という
/// ビット演算に対応しています。
///
/// ```
/// # use bitset::Bs;
/// let mut bs = Bs::from_01str("0010010010");
///
/// // 左シフト
/// // NOTE: スライスや文字列でいうところの右に移動する感じになります。
/// bs <<= 2;
/// assert_eq!(&bs, &Bs::from_01str("0000100100"));
/// bs <<= 10;
/// assert_eq!(&bs, &Bs::from_01str("0000000000"));
///
/// // 右シフト
/// // NOTE: スライスや文字列でいうところの左に移動する感じになります。
/// bs = Bs::from_01str("0010010010");
/// bs >>= 2;
/// assert_eq!(&bs, &Bs::from_01str("1001001000"));
/// bs >>= 10;
/// assert_eq!(&bs, &Bs::from_01str("0000000000"));
///
/// // OR 演算
/// // NOTE: 複合代入しかありません。右辺は参照です。
/// bs = Bs::from_01str("0000011111");
/// bs |= &Bs::from_01str("0101010101");
/// assert_eq!(&bs, &Bs::from_01str("0101011111"));
///
/// // AND 演算
/// // NOTE: 複合代入しかありません。右辺は参照です。
/// bs = Bs::from_01str("0000011111");
/// bs &= &Bs::from_01str("0101010101");
/// assert_eq!(&bs, &Bs::from_01str("0000010101"));
///
/// // XOR 演算
/// // NOTE: 複合代入しかありません。右辺は参照です。
/// bs = Bs::from_01str("0000011111");
/// bs ^= &Bs::from_01str("0101010101");
/// assert_eq!(&bs, &Bs::from_01str("0101001010"));
/// ```
#[derive(Clone, Hash, PartialEq)]
pub struct Bs {
    vec: Vec<u64>,
    len: usize,
}
impl Bs {
    /// サイズを指定して 0 埋め構築します。
    ///
    /// # Example
    ///
    /// ```
    /// # use bitset::Bs;
    /// let mut bs = Bs::new(10);
    /// assert_eq!(&bs, &Bs::from_01str("0000000000"));
    /// ```
    pub fn new(len: usize) -> Self {
        Self::from_raw(vec![0; div_ceil(len, 64)], len)
    }
    /// "01" 文字列から構築します。
    ///
    /// # Panics
    ///
    /// '0', '1' 以外の文字があるときです。
    ///
    ///
    /// # Example
    ///
    /// ```
    /// # use bitset::Bs;
    /// let mut bs = Bs::from_01str("010");
    /// assert_eq!(bs.test(0), false);
    /// assert_eq!(bs.test(1), true);
    /// assert_eq!(bs.test(2), false);
    /// ```
    pub fn from_01str(s: &str) -> Self {
        s.chars()
            .map(|c| match c {
                '0' => false,
                '1' => true,
                _ => panic!("{}", s),
            })
            .collect()
    }
    /// 長さを返します。
    ///
    /// # Example
    ///
    /// ```
    /// # use bitset::Bs;
    /// let mut bs = Bs::from_01str("010");
    /// assert_eq!(bs.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }
    /// 後ろに要素を追架します。
    ///
    /// # Example
    ///
    /// ```
    /// # use bitset::Bs;
    /// let mut bs = Bs::from_01str("010");
    /// bs.push(false);
    /// bs.push(true);
    /// assert_eq!(&bs, &Bs::from_01str("01001"));
    /// ```
    pub fn push(&mut self, x: bool) {
        let i = self.len;
        self.len += 1;
        if i % 64 == 0 {
            self.vec.push(x as u64);
        } else if x {
            self.set(i);
        }
    }
    /// 特定のビットが立っていれば `true` を返します。
    ///
    /// # Example
    ///
    /// ```
    /// # use bitset::Bs;
    /// let mut bs = Bs::from_01str("010");
    /// assert_eq!(bs.test(0), false);
    /// assert_eq!(bs.test(1), true);
    /// assert_eq!(bs.test(2), false);
    /// ```
    pub fn test(&self, i: usize) -> bool {
        debug_assert!(i < self.len);
        self.vec[i / 64] >> i % 64 & 1 == 1
    }
    /// 特定のビットを立てます。
    ///
    /// もともと立っているときにも立ったままです。
    ///
    /// # Example
    ///
    /// ```
    /// # use bitset::Bs;
    /// let mut bs = Bs::from_01str("010");
    /// bs.set(2);
    /// assert_eq!(&bs, &Bs::from_01str("011"));
    /// ```
    pub fn set(&mut self, i: usize) {
        debug_assert!(i < self.len);
        self.vec[i / 64] |= 1_u64 << i % 64;
    }
    /// 特定のビットをおろします。
    ///
    /// もともと立っていないときにも立っていないままです。
    ///
    /// # Example
    ///
    /// ```
    /// # use bitset::Bs;
    /// let mut bs = Bs::from_01str("010");
    /// bs.unset(1);
    /// assert_eq!(&bs, &Bs::from_01str("000"));
    /// ```
    pub fn unset(&mut self, i: usize) {
        debug_assert!(i < self.len);
        self.vec[i / 64] &= !(1_u64 << i % 64);
    }
    pub fn format(&self, t: char, f: char) -> String {
        self.iter().map(|b| if b { t } else { f }).collect()
    }
    pub fn iter(&self) -> Iter<'_> {
        Iter { bs: self, i: 0 }
    }
    fn from_raw(vec: Vec<u64>, len: usize) -> Self {
        Self { vec, len }
    }
}

pub struct Iter<'a> {
    bs: &'a Bs,
    i: usize,
}
impl<'a> Iterator for Iter<'a> {
    type Item = bool;
    fn next(&mut self) -> Option<bool> {
        if self.bs.len() == self.i {
            None
        } else {
            let res = self.bs.test(self.i);
            self.i += 1;
            Some(res)
        }
    }
}

impl Default for Bs {
    fn default() -> Self {
        Self::from_raw(Vec::new(), 0)
    }
}

impl FromIterator<bool> for Bs {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let mut vec = Vec::with_capacity(div_ceil(iter.size_hint().1.unwrap_or(0), 64));
        let mut cell = 0;
        let mut i = 0;
        for x in iter {
            if i == 64 {
                i = 0;
                vec.push(replace(&mut cell, 0));
            }
            cell |= (x as u64) << i;
            i += 1;
        }
        if vec.is_empty() && i == 0 {
            return Self::default();
        }
        let len = vec.len() * 64 + i;
        vec.push(cell);
        Self::from_raw(vec, len)
    }
}
impl Debug for Bs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string())
    }
}
impl ToString for Bs {
    fn to_string(&self) -> String {
        self.format('1', '0')
    }
}

impl BitAndAssign<&Self> for Bs {
    fn bitand_assign(&mut self, rhs: &Self) {
        assert_eq!(self.len(), rhs.len());
        self.vec
            .iter_mut()
            .zip(&rhs.vec)
            .for_each(|(x, &y)| *x &= y);
    }
}
impl BitOrAssign<&Self> for Bs {
    fn bitor_assign(&mut self, rhs: &Self) {
        assert_eq!(self.len(), rhs.len());
        self.vec
            .iter_mut()
            .zip(&rhs.vec)
            .for_each(|(x, &y)| *x |= y);
    }
}
impl BitXorAssign<&Self> for Bs {
    fn bitxor_assign(&mut self, rhs: &Self) {
        assert_eq!(self.len(), rhs.len());
        self.vec
            .iter_mut()
            .zip(&rhs.vec)
            .for_each(|(x, &y)| *x ^= y);
    }
}

macro_rules! impl_shifts {
    ($($t: ty,)*) => {$(
        impl ShlAssign<$t> for Bs {
            fn shl_assign(&mut self, other: $t) {
                let other = other as usize;
                assert!(other <= self.len());
                let (q, r) = (other / 64, other % 64);
                self.vec.rotate_right(q);
                self.vec[..q].iter_mut().for_each(|x| *x = 0);
                if r != 0 {
                    let mut crr = 0;
                    for x in &mut self.vec {
                        let swp = *x >> 64 - r;
                        *x <<= r;
                        *x |= replace(&mut crr, swp);
                    }
                }
                let r = self.len() % 64;
                if r != 0 {
                    *self.vec.last_mut().unwrap() &= (1_u64 << r) - 1;
                }
            }
        }
        impl ShrAssign<$t> for Bs {
            fn shr_assign(&mut self, other: $t) {
                let other = other as usize;
                assert!(other <= self.len());
                let (q, r) = (other / 64, other % 64);
                let l = self.vec.len();
                self.vec.rotate_left(q);
                self.vec[l - q..].iter_mut().for_each(|x| *x = 0);
                if r != 0 {
                    let mut crr = 0;
                    for x in self.vec.iter_mut().rev() {
                        let swp = (*x & (1 << r) - 1) << 64 - r;
                        *x >>= r;
                        *x |= replace(&mut crr, swp);
                    }
                }
            }
        }
    )*}
}
impl_shifts! {
    u8, u16, u32, u64, u128, usize,
    i8, i16, i32, i64, i128, isize,
}

fn div_ceil(x: usize, y: usize) -> usize {
    if x == 0 {
        0
    } else {
        (x - 1) / y + 1
    }
}

#[cfg(test)]
mod tests {
    use super::Bs;
    use rand::{prelude::StdRng, Rng, SeedableRng};
    use std::iter::repeat_with;

    macro_rules! assert_eq_bs {
        ($bs: expr, $slice: expr) => {
            let bs: &Bs = $bs;
            let slice: &[bool] = $slice;
            assert_eq!(bs.len(), slice.len(), "different size",);
            for i in 0..bs.len() {
                assert_eq!(
                    bs.test(i),
                    slice[i],
                    "{} th bit differs;\n bs = {:?},\n slice = {}",
                    i,
                    &bs,
                    slice
                        .iter()
                        .map(|&b| if b { '1' } else { '0' })
                        .collect::<String>(),
                );
            }
            let r = bs.len() % 64;
            if r != 0 {
                assert_eq!(bs.vec.last().unwrap() >> r, 0, "nonzero");
            }
        };
    }

    fn generate_random(rng: &mut StdRng, len: usize) -> Vec<bool> {
        repeat_with(|| rng.gen_ratio(1, 2)).take(len).collect()
    }

    #[test]
    fn test_from_iter() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let a = generate_random(&mut rng, n);
            let bs = a.iter().copied().collect::<Bs>();
            assert_eq_bs!(&bs, &a);
        }
    }

    #[test]
    fn test_shl() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let i = rng.gen_range(0..=n);
            let mut a = generate_random(&mut rng, n);
            let mut bs = a.iter().copied().collect::<Bs>();
            bs <<= i;
            a.rotate_right(i);
            a[..i].iter_mut().for_each(|x| *x = false);
            assert_eq_bs!(&bs, &a);
        }
    }

    #[test]
    fn test_shr() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let i = rng.gen_range(0..=n);
            let mut a = generate_random(&mut rng, n);
            let mut bs = a.iter().copied().collect::<Bs>();
            bs >>= i;
            a.rotate_left(i);
            a[n - i..].iter_mut().for_each(|x| *x = false);
            assert_eq_bs!(&bs, &a);
        }
    }

    #[test]
    fn test_bit_or() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let mut a = generate_random(&mut rng, n);
            let mut bs = a.iter().copied().collect::<Bs>();
            let a1 = generate_random(&mut rng, n);
            let bs1 = a1.iter().copied().collect::<Bs>();
            bs |= &bs1;
            a.iter_mut().zip(&a1).for_each(|(x, &y)| *x |= y);
            assert_eq_bs!(&bs, &a);
        }
    }

    #[test]
    fn test_bit_xor() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let mut a = generate_random(&mut rng, n);
            let mut bs = a.iter().copied().collect::<Bs>();
            let a1 = generate_random(&mut rng, n);
            let bs1 = a1.iter().copied().collect::<Bs>();
            bs ^= &bs1;
            a.iter_mut().zip(&a1).for_each(|(x, &y)| *x ^= y);
            assert_eq_bs!(&bs, &a);
        }
    }

    #[test]
    fn test_push() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let x = rng.gen_ratio(1, 2);
            let mut a = generate_random(&mut rng, n);
            let mut bs = a.iter().copied().collect::<Bs>();
            a.push(x);
            bs.push(x);
            assert_eq_bs!(&bs, &a);
        }
    }

    #[test]
    fn test_set() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let i = rng.gen_range(0..n);
            let mut a = generate_random(&mut rng, n);
            let mut bs = a.iter().copied().collect::<Bs>();
            a[i] = true;
            bs.set(i);
            assert_eq_bs!(&bs, &a);
        }
    }

    #[test]
    fn test_unset() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..2000 {
            let n = rng.gen_range(1..=256);
            let i = rng.gen_range(0..n);
            let mut a = generate_random(&mut rng, n);
            let mut bs = a.iter().copied().collect::<Bs>();
            a[i] = false;
            bs.unset(i);
            assert_eq_bs!(&bs, &a);
        }
    }
}
