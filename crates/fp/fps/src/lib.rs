//! 高速フーリエ変換を利用した、形式的べき級数の諸演算です。
//!
//! # 使い方
//!
//! ```
//! use fp::F998244353 as Fp;
//! use fps::Convolution; // 畳み込みはここにあります。
//!
//! // 最も普通なもの
//! let a = vec![Fp::new(1), Fp::new(2)];
//! let b = vec![Fp::new(1), Fp::new(3)];
//! assert_eq!(Fp::convolution(a, b), vec![Fp::new(1),  Fp::new(5), Fp::new(6)]);
//!
//! // リサイズをしないバージョン（余分に確保しておかないと答えが合わないので注意）
//! let a = vec![Fp::new(1), Fp::new(2), Fp::new(0), Fp::new(0)];
//! let b = vec![Fp::new(1), Fp::new(3), Fp::new(0), Fp::new(0)];
//! assert_eq!(Fp::convolution_power_of_two(a, b), vec![Fp::new(1),  Fp::new(5), Fp::new(6),
//! Fp::new(0)]);
//! ```
//!
//! # 整数、任意 mod
//!
//! | 種類 | 整数 | 関数 |
//! | - | - | - |
//! | 2 冪精度 | [`integer_convolution_power_of_two`] | [`integer_convolution_power_of_two`] |
//! | 適切 | [`integer_convolution`] | [`integer_convolution`] |

use fp::{Fp, Mod, F1012924417, F924844033, F998244353};

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
    /// 長さが 2 冪かつ等しいものを受け取って、**長さと同じ精度**で畳み込みを計算します。
    fn convolution_power_of_two(a: Vec<Self>, b: Vec<Self>) -> Vec<Self>;
    /// `convolution_power_of_two` と resize, truncate を用いて十分な精度で計算します。
    fn convolution(mut a: Vec<Self>, mut b: Vec<Self>) -> Vec<Self> {
        let n = a.len() + b.len() - 1;
        a.resize(n.next_power_of_two(), Self::from(0));
        b.resize(n.next_power_of_two(), Self::from(0));
        let mut c = Self::convolution_power_of_two(a, b);
        c.truncate(n);
        c
    }
}

/// [`Fourier`] と [`Convolution`] を導出します。
///
/// # 引数
///
/// * `$mod`: モジュール名（中はトレイトの実装なので、使う必要のないお名前です。）
/// * `$Fp`:  Fp 型
/// * `$prim_root`: [`Convolution::PRIM_ROOT`] の値
/// * `$e`: [`Convolution::E`] の値
#[macro_export]
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
                    super::fourier(a, &root);
                }
                fn fourier_inverse(a: &mut [Fp]) {
                    debug_assert!(a.len().is_power_of_two());
                    let [_root, root_recip] = init(a.len().trailing_zeros());
                    super::fourier_inverse(a, &root_recip);
                }
            }
            impl Convolution for Fp {
                const PRIM_ROOT: u32 = $prim_root;
                const E: u32 = $e;
                fn convolution_power_of_two(a: Vec<Fp>, b: Vec<Fp>) -> Vec<Fp> {
                    let [root, root_recip] = init(a.len().trailing_zeros());
                    super::convolution_power_of_two(a, b, &root, &root_recip)
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

fn fourier<M: Mod>(a: &mut [Fp<M>], root: &[Fp<M>]) {
    let n = a.len();
    let mut d = a.len() / 2;
    while d != 0 {
        let mut coeff = Fp::new(1);
        for (i, t) in (0..n).step_by(2 * d).zip(1u32..) {
            for (i, j) in (i..i + d).zip(i + d..) {
                let x = a[i];
                let y = a[j] * coeff;
                a[i] = x + y;
                a[j] = x - y;
            }
            coeff *= root[t.trailing_zeros() as usize];
        }
        d /= 2;
    }
}

fn fourier_inverse<M: Mod>(a: &mut [Fp<M>], root_recip: &[Fp<M>]) {
    let n = a.len();
    let mut d = 1;
    while d != n {
        let mut coeff = Fp::new(1);
        for (i, t) in (0..n).step_by(2 * d).zip(1u32..) {
            for (i, j) in (i..i + d).zip(i + d..) {
                let x = a[i];
                let y = a[j];
                a[i] = x + y;
                a[j] = (x - y) * coeff;
            }
            coeff *= root_recip[t.trailing_zeros() as usize];
        }
        d *= 2;
    }
    let d = Fp::from(a.len()).recip();
    a.iter_mut().for_each(|x| *x *= d);
}

fn convolution_power_of_two<M: Mod>(
    mut a: Vec<Fp<M>>,
    mut b: Vec<Fp<M>>,
    root: &[Fp<M>],
    root_recip: &[Fp<M>],
) -> Vec<Fp<M>> {
    assert!(a.len().is_power_of_two());
    assert!(b.len().is_power_of_two());
    assert_eq!(a.len(), b.len());
    fourier(&mut a, root);
    fourier(&mut b, root);
    a.iter_mut().zip(b.iter()).for_each(|(x, y)| *x *= *y);
    fourier_inverse(&mut a, root_recip);
    a
}

/// 3 つの NTT-friendly 素数を用いて整数でコンボリューションします。
pub fn integer_convolution_power_of_two(a: Vec<u32>, b: Vec<u32>) -> Vec<u128> {
    assert!(a.len().is_power_of_two());
    assert!(b.len().is_power_of_two());
    assert_eq!(a.len(), b.len());
    type Fp1 = F998244353;
    type Fp2 = F1012924417;
    type Fp3 = F924844033;
    let v1 = Fp1::convolution_power_of_two(
        a.iter().map(|&x| Fp1::new(x)).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp1::new(x)).collect::<Vec<_>>(),
    );
    let v2 = Fp2::convolution_power_of_two(
        a.iter().map(|&x| Fp2::new(x)).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp2::new(x)).collect::<Vec<_>>(),
    );
    let v3 = Fp3::convolution_power_of_two(
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
            x1.value() as u128
                + x2.value() as u128 * Fp1::P as u128
                + x3.value() as u128 * Fp1::P as u128 * Fp2::P as u128
        })
        .collect::<Vec<_>>()
}

/// 3 つの NTT-friendly 素数を用いて任意 mod でコンボリューションします。
pub fn anymod_convolution_power_of_two<M: Mod>(a: Vec<Fp<M>>, b: Vec<Fp<M>>) -> Vec<Fp<M>> {
    assert!(a.len().is_power_of_two());
    assert!(b.len().is_power_of_two());
    assert_eq!(a.len(), b.len());
    type Fp1 = F998244353;
    type Fp2 = F1012924417;
    type Fp3 = F924844033;
    let v1 = Fp1::convolution_power_of_two(
        a.iter().map(|&x| Fp1::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp1::new(x.value())).collect::<Vec<_>>(),
    );
    let v2 = Fp2::convolution_power_of_two(
        a.iter().map(|&x| Fp2::new(x.value())).collect::<Vec<_>>(),
        b.iter().map(|&x| Fp2::new(x.value())).collect::<Vec<_>>(),
    );
    let v3 = Fp3::convolution_power_of_two(
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

/// 3 つの NTT-friendly 素数を用いて整数でコンボリューションします。
pub fn integer_convolution(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u128> {
    let n = a.len() + b.len() - 1;
    a.resize(n.next_power_of_two(), 0);
    b.resize(n.next_power_of_two(), 0);
    let mut c = integer_convolution_power_of_two(a, b);
    c.truncate(n);
    c
}

/// 3 つの NTT-friendly 素数を用いて任意 mod でコンボリューションします。
pub fn anymod_convolution<M: Mod>(mut a: Vec<Fp<M>>, mut b: Vec<Fp<M>>) -> Vec<Fp<M>> {
    let n = a.len() + b.len() - 1;
    a.resize(n.next_power_of_two(), Fp::<M>::new(0));
    b.resize(n.next_power_of_two(), Fp::<M>::new(0));
    let mut c = anymod_convolution_power_of_two(a, b);
    c.truncate(n);
    c
}

#[cfg(test)]
mod test {
    use {
        super::{anymod_convolution_power_of_two, integer_convolution_power_of_two, Convolution},
        fp::{Fp, Mod},
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::iter::{repeat, repeat_with},
    };

    #[test]
    fn test_convolution_power_of_two_998244353() {
        test_convolution_power_of_two_impl::<fp::Mod998244353>()
    }
    #[test]
    fn test_convolution_power_of_two_1012924417() {
        test_convolution_power_of_two_impl::<fp::Mod1012924417>()
    }
    #[test]
    fn test_convolution_power_of_two_924844033() {
        test_convolution_power_of_two_impl::<fp::Mod924844033>()
    }

    fn test_convolution_power_of_two_impl<M: Mod>()
    where
        Fp<M>: Convolution,
    {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let k = rng.gen_range(0..8);
            let n = 1 << k;
            let a = repeat_with(|| Fp::<M>::new(rng.gen_range(0..Fp::<M>::P)))
                .take(n)
                .chain(repeat(Fp::new(0)).take(n))
                .collect_vec();
            let b = repeat_with(|| Fp::new(rng.gen_range(0..Fp::<M>::P)))
                .take(n)
                .chain(repeat(Fp::new(0)).take(n))
                .collect_vec();
            println!("a = {:?}", &a);
            println!("b = {:?}", &b);
            let result = Fp::convolution_power_of_two(a.clone(), b.clone());
            let mut expected = vec![Fp::new(0); 2 * n];
            for i in 0..n {
                for j in 0..n {
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
            let k = rng.gen_range(0..8);
            let n = 1 << k;
            let a = repeat_with(|| rng.gen_range(0..std::u32::MAX))
                .take(n)
                .chain(repeat(0).take(n))
                .collect_vec();
            let b = repeat_with(|| rng.gen_range(0..std::u32::MAX))
                .take(n)
                .chain(repeat(0).take(n))
                .collect_vec();
            let result = integer_convolution_power_of_two(a.clone(), b.clone());
            let mut expected = vec![0; 2 * n];
            for i in 0..n {
                for j in 0..n {
                    expected[i + j] += a[i] as u128 * b[j] as u128;
                }
            }
            assert_eq!(result, expected);
        }
    }

    #[test]
    fn test_anymod_convolution_power_of_two() {
        use fp::F1000000007 as Fp;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..100 {
            let k = rng.gen_range(0..8);
            let n = 1 << k;
            let a = repeat_with(|| Fp::new(rng.gen_range(0..Fp::P)))
                .take(n)
                .chain(repeat(Fp::new(0)).take(n))
                .collect_vec();
            let b = repeat_with(|| Fp::new(rng.gen_range(0..Fp::P)))
                .take(n)
                .chain(repeat(Fp::new(0)).take(n))
                .collect_vec();
            let result = anymod_convolution_power_of_two(a.clone(), b.clone());
            let mut expected = vec![Fp::new(0); 2 * n];
            for i in 0..n {
                for j in 0..n {
                    expected[i + j] += a[i] * b[j];
                }
            }
            assert_eq!(result, expected);
        }
    }
}
