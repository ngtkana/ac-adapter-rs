//! 高速フーリエ変換を利用した、形式的べき級数の諸演算です。
//!
//! # 使い方
//!
//! ```
//! use fp::F998244353 as Fp;
//! use fps::Convolution; // 畳み込みはここにあります。
//! use fps::fps_inverse;
//!
//! // 畳み込み（掛け算）
//! let a = vec![Fp::new(1), Fp::new(2)];
//! let b = vec![Fp::new(1), Fp::new(3)];
//! assert_eq!(Fp::convolution(a, b), vec![Fp::new(1),  Fp::new(5), Fp::new(6)]);
//!
//! // 乗法逆元（一般に無限になるので、第二引数で精度を指定）
//! let a = vec![Fp::new(1), Fp::new(2)];
//! assert_eq!(fps_inverse(a, 4), vec![Fp::from(1), Fp::from(-2), Fp::from(4), Fp::from(-8)]);
//! ```
//!
//! # 整数、任意 mod
//!
//! | 整数 | 関数 |
//! | - | - |
//! | [`integer_convolution`] | [`integer_convolution`] |

use fp::{Fp, Mod, F1012924417, F924844033, F998244353};
mod arith;
mod fourier;
pub use arith::{fps_exp, fps_inverse, fps_log, fps_sqrt};

/// 高速フーリエ変換
pub trait Fourier: Sized {
    /// 高速フーリエ変換
    ///
    /// # 出力
    ///
    /// フーリ変換の結果が、成分が bit-reverse された状態で返ります。
    ///
    /// ```
    /// use fp::F998244353 as Fp;
    /// use fps::Fourier;
    ///
    /// // [0, 1, 0, 0]
    /// let mut a = [Fp::new(0), Fp::new(1), Fp::new(0), Fp::new(0)];
    /// Fp::fourier(&mut a);
    ///
    /// // [1, -1, i, -i] （成分の順序に注意です。）
    /// assert_eq!(a, [Fp::new(1), Fp::from(-1), Fp::new(86583718), Fp::from(-86583718)]);
    /// ```
    fn fourier(a: &mut [Self]);

    ///
    /// # 出力
    ///
    /// フーリ変換の結果が、成分が bit-reverse された状態で返ります。
    ///
    /// ```
    /// use fp::F998244353 as Fp;
    /// use fps::Fourier;
    ///
    /// // 先ほどとちょうど逆の変換
    /// let mut a = [Fp::new(1), Fp::from(-1), Fp::new(86583718), Fp::from(-86583718)];
    /// Fp::fourier_inverse(&mut a);
    /// assert_eq!(a, [Fp::new(0), Fp::new(1), Fp::new(0), Fp::new(0)]);
    /// ```
    fn fourier_inverse(a: &mut [Self]);
}
/// 畳み込み
pub trait Convolution: Sized + Clone + From<u32> {
    /// 原子根
    const PRIM_ROOT: u32;
    /// `Fp::P - 1` の 2 進付値
    const E: u32;
    /// 畳み込み
    fn convolution(a: Vec<Self>, b: Vec<Self>) -> Vec<Self>;
}

macro_rules! impl_fourier_and_convolution {
    ($(($mod: ident, $Fp: ty, $prim_root: expr, $e: expr),)*) => {$(
        mod $mod {
            use super::{Convolution, Fourier};
            type Fp = $Fp;

            fn init(lg: u32) -> [Vec<Fp>; 2] {
                let mut root = Vec::new();
                let mut root_recip = Vec::new();
                for i in 0..lg {
                    let x = -Fp::new($prim_root).pow((Fp::P - 1) >> (i + 2));
                    root.push(x);
                    root_recip.push(x.recip());
                }
                [root, root_recip]
            }

            impl Fourier for Fp {
                fn fourier(a: &mut [Fp]) {
                    debug_assert!(a.len().is_power_of_two());
                    let [root, _root_recip] = init(a.len().trailing_zeros());
                    super::fourier::fourier_impl(a, &root);
                }
                fn fourier_inverse(a: &mut [Fp]) {
                    debug_assert!(a.len().is_power_of_two());
                    let [_root, root_recip] = init(a.len().trailing_zeros());
                    super::fourier::fourier_inverse_impl(a, &root_recip);
                }
            }
            impl Convolution for Fp {
                const PRIM_ROOT: u32 = $prim_root;
                const E: u32 = $e;
                fn convolution(mut a: Vec<Fp>, mut b: Vec<Fp>) -> Vec<Fp> {
                    let n = a.len() + b.len() - 1;
                    let next_power_of_two = n.next_power_of_two();
                    let [root, root_recip] = init(next_power_of_two.trailing_zeros());
                    a.resize(next_power_of_two, Self::from(0));
                    b.resize(next_power_of_two, Self::from(0));
                    let mut c = super::fourier::convolution_impl(a, b, &root, &root_recip);
                    c.truncate(n);
                    c
                }
            }
        }
    )*};
}

impl_fourier_and_convolution! {
    (fourier_998244353, fp::F998244353, 3, 23),
    (fourier_1012924417, fp::F1012924417, 5, 21),
    (fourier_924844033, fp::F924844033, 5, 21),
}

/// 3 つの NTT-friendly 素数を用いて整数でコンボリューションします。
pub fn integer_convolution(a: &[u32], b: &[u32]) -> Vec<u128> {
    type Fp1 = F998244353;
    type Fp2 = F1012924417;
    type Fp3 = F924844033;
    let v1 = Fp1::convolution(
        a.iter().map(|&x| Fp1::new(x)).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp1::new(x)).collect::<Vec<_>>(),
    );
    let v2 = Fp2::convolution(
        a.iter().map(|&x| Fp2::new(x)).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp2::new(x)).collect::<Vec<_>>(),
    );
    let v3 = Fp3::convolution(
        a.iter().map(|&x| Fp3::new(x)).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp3::new(x)).collect::<Vec<_>>(),
    );
    v1.into_iter()
        .zip(v2)
        .zip(v3)
        .map(|((e1, e2), e3)| {
            let x1 = e1;
            let x2 = (e2 - Fp2::new(x1.value())) * Fp2::new(Fp1::P).recip();
            let x3 = ((e3 - Fp3::new(x1.value())) * Fp3::new(Fp1::P).recip()
                - Fp3::new(x2.value()))
                * Fp3::new(Fp2::P).recip();
            u128::from(x1.value())
                + u128::from(x2.value()) * u128::from(Fp1::P)
                + u128::from(x3.value()) * u128::from(Fp1::P) * u128::from(Fp2::P)
        })
        .collect::<Vec<_>>()
}

/// 3 つの NTT-friendly 素数を用いて任意 mod でコンボリューションします。
pub fn anymod_convolution<M: Mod>(a: &[Fp<M>], b: &[Fp<M>]) -> Vec<Fp<M>> {
    type Fp1 = F998244353;
    type Fp2 = F1012924417;
    type Fp3 = F924844033;
    let v1 = Fp1::convolution(
        a.iter().map(|&x| Fp1::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp1::new(x.value())).collect::<Vec<_>>(),
    );
    let v2 = Fp2::convolution(
        a.iter().map(|&x| Fp2::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp2::new(x.value())).collect::<Vec<_>>(),
    );
    let v3 = Fp3::convolution(
        a.iter().map(|&x| Fp3::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp3::new(x.value())).collect::<Vec<_>>(),
    );
    v1.into_iter()
        .zip(v2)
        .zip(v3)
        .map(|((e1, e2), e3)| {
            let x1 = e1;
            let x2 = (e2 - Fp2::new(x1.value())) * Fp2::new(Fp1::P).recip();
            let x3 = ((e3 - Fp3::new(x1.value())) * Fp3::new(Fp1::P).recip()
                - Fp3::new(x2.value()))
                * Fp3::new(Fp2::P).recip();
            Fp::new(x1.value())
                + Fp::new(x2.value()) * Fp::new(Fp1::P)
                + Fp::new(x3.value()) * Fp::new(Fp1::P) * Fp::new(Fp2::P)
        })
        .collect::<Vec<_>>()
}

#[cfg(test)]
mod test {
    use {
        super::{anymod_convolution, integer_convolution, Convolution},
        fp::{Fp, Mod},
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::iter::repeat_with,
    };

    #[test]
    fn test_convolution_998244353() {
        test_convolution_impl::<fp::Mod998244353>()
    }
    #[test]
    fn test_convolution_1012924417() {
        test_convolution_impl::<fp::Mod1012924417>()
    }
    #[test]
    fn test_convolution_924844033() {
        test_convolution_impl::<fp::Mod924844033>()
    }

    fn test_convolution_impl<M: Mod>()
    where
        Fp<M>: Convolution,
    {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..100);
            let m = rng.gen_range(1..100);
            let a = repeat_with(|| Fp::<M>::new(rng.gen_range(0..Fp::<M>::P)))
                .take(n)
                .collect_vec();
            let b = repeat_with(|| Fp::new(rng.gen_range(0..Fp::<M>::P)))
                .take(m)
                .collect_vec();
            let result = Fp::convolution(a.clone(), b.clone());
            let mut expected = vec![Fp::new(0); n + m - 1];
            for i in 0..n {
                for j in 0..m {
                    expected[i + j] += a[i] * b[j];
                }
            }
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_integer_convolution_power_of_two() {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..100);
            let m = rng.gen_range(1..100);
            let a = repeat_with(|| rng.gen_range(0..std::u32::MAX))
                .take(n)
                .collect_vec();
            let b = repeat_with(|| rng.gen_range(0..std::u32::MAX))
                .take(m)
                .collect_vec();
            let result = integer_convolution(&a, &b);
            let mut expected = vec![0; n + m - 1];
            for i in 0..n {
                for j in 0..m {
                    expected[i + j] += u128::from(a[i]) * u128::from(b[j]);
                }
            }
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_anymod_convolution() {
        use fp::F1000000007 as Fp;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let n = rng.gen_range(1..100);
            let m = rng.gen_range(1..100);
            let a = repeat_with(|| Fp::new(rng.gen_range(0..Fp::P)))
                .take(n)
                .collect_vec();
            let b = repeat_with(|| Fp::new(rng.gen_range(0..Fp::P)))
                .take(m)
                .collect_vec();
            let result = anymod_convolution(&a, &b);
            let mut expected = vec![Fp::new(0); n + m - 1];
            for i in 0..n {
                for j in 0..m {
                    expected[i + j] += a[i] * b[j];
                }
            }
            assert_eq!(result, expected);
        }
    }
}
