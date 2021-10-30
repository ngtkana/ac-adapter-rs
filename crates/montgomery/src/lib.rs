//! 定数項が 0 でない多項式を法として、モンゴメリ乗算をします。
//!
//! # 仕組み
//!
//! * 法となる多項式 p を受け取ると、次のものを計算します。
//!     * n = deg( p ) + 1
//!     * k = ( -1 / p ) mod xⁿ
//!     * r² = x ²ⁿ mod p
//!
//!
//! * [`reduce`](Montgomery::reduce) が呼ばれると、( f / xⁿ ) mod p
//! を求めるために次のものを計算します。これは f の次数が 2n - 2 以下のとき、次数 n - 2 以下、
//! すなわち次数 deg(p) 未満になります。（MR は
//! [Wikipedia](https://ja.wikipedia.org/wiki/%E3%83%A2%E3%83%B3%E3%82%B4%E3%83%A1%E3%83%AA%E4%B9%97%E7%AE%97)
//! の記号です。）
//!
//!     * MR ( f ) = ( f + p ( ( f k ) mod xⁿ) ) / xⁿ
//!
//!
//!
//! * [`reduce_inverse`](Montgomery::reduce_inverse) が呼ばれると、MR ⁻¹( f ) を求めるために、
//! 次のものを計算します。
//!
//!     * MR⁻¹( f ) = MR ( f r²)
//!
//!
//! # 一般素数 mod
//!
//! 非対応です。
//!

use {
    fp::{Fp, Mod},
    fps::{fps_inverse, Convolution},
    std::iter::{once, repeat},
};

/// モンゴメリ乗算をします。
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Montgomery<M: Mod> {
    p: Vec<Fp<M>>,
    k: Vec<Fp<M>>,
    r2: Vec<Fp<M>>,
}
impl<M: Mod> Montgomery<M>
where
    Fp<M>: Convolution,
{
    /// 法となる多項式 p を与えて、モンゴメリ乗算の準備をします。
    ///
    /// # 入力
    ///
    /// * p: 法となる多項式
    ///
    /// ただし trailing zeros のある場合は自動的に削られます。
    ///
    ///
    /// # Panics
    ///
    /// * p が 0 のとき
    ///
    ///
    /// # 使用例
    ///
    /// ```
    /// use montgomery::Montgomery;
    /// use fp::F998244353 as Fp;
    ///
    /// // 法を x² - 1 にセットです。
    /// let mont = Montgomery::new(vec![-Fp::new(1), Fp::new(0), Fp::new(1)]);
    /// ```
    ///
    pub fn new(mut p: Vec<Fp<M>>) -> Self {
        normalize(&mut p);
        assert!(
            *p.first().unwrap() != Fp::new(0),
            "法は x^n と互いに素でないといけませんから、定数項 0 はだめです。"
        );
        let mut k = fps_inverse(p.clone(), p.len());
        k.iter_mut().for_each(|x| *x = -*x);
        let [_, mut r2] = div_rem_newton(
            repeat(Fp::new(0))
                .take(p.len() * 2)
                .chain(once(Fp::new(1)))
                .collect::<Vec<_>>(),
            p.clone(),
        );
        r2.resize(p.len() - 1, Fp::new(0));
        Self { p, k, r2 }
    }
    /// 多項式 f を受け取って、MR ( f ) = ( f / xⁿ ) mod p を計算します。
    ///
    /// # 入力
    ///
    /// * f: 2n 次未満の多項式
    ///
    /// ただし trailing zeros のある場合は自動的に削られます。
    ///
    ///
    /// # Panics
    ///
    /// * 2n ≦ deg(f) のとき
    ///
    ///
    /// # 出力
    ///
    /// 以下のものを、trailing zeros なしで返します。
    ///
    /// * ( f / xⁿ ) mod p
    ///
    ///
    /// # 使用例
    ///
    /// ```
    /// use montgomery::Montgomery;
    /// use fp::F998244353 as Fp;
    ///
    /// // 法を x² - 1 にセットです。( x⁻³ = x mod p )
    /// let mont = Montgomery::new(vec![-Fp::new(1), Fp::new(0), Fp::new(1)]);
    ///
    /// let f = vec![Fp::new(4), Fp::new(8)];   // f(x) = 8x + 4 とします。
    /// let result = mont.reduce(f);            // x⁻³ ( = x ) を掛けます。
    ///
    /// let expected = vec![Fp::new(8), Fp::new(4)]; // すると 4x + 8 になります。
    /// assert_eq!(result, expected);
    /// ```
    pub fn reduce(&self, mut f: Vec<Fp<M>>) -> Vec<Fp<M>> {
        normalize(&mut f);
        assert!(
            f.len() < 2 * self.p.len(),
            "Reducer の次数( = p.len() ）の 2 倍未満でお願いします。"
        );
        reduce(self.p.clone(), self.k.clone(), &f)
    }
    /// 多項式 f を受け取って、MR⁻¹ ( f ) を計算します。
    ///
    /// # 入力
    ///
    /// * f: n 次未満の多項式
    ///
    /// ただし trailing zeros のある場合は自動的に削られます。
    ///
    ///
    /// # Panics
    ///
    /// * n ≦ deg(f) のとき
    ///
    ///
    /// # 出力
    ///
    /// 以下のものを、trailing zeros なしで返します。
    ///
    /// * MR⁻¹( f )
    ///
    ///
    /// # 使用例
    ///
    /// ```
    /// use montgomery::Montgomery;
    /// use fp::F998244353 as Fp;
    ///
    /// // 法を x² - 1 にセットです。( x⁻³ = x mod p )
    /// let mont = Montgomery::new(vec![-Fp::new(1), Fp::new(0), Fp::new(1)]);
    ///
    /// let f = vec![Fp::new(8), Fp::new(4)];   // f(x) = 4x + 8 とします。
    /// let result = mont.reduce_inverse(f);    // x³ ( = x ) を掛けます。
    ///
    /// let expected = vec![Fp::new(4), Fp::new(8)]; // すると 8x + 4 になります。
    /// assert_eq!(result, expected);
    /// ```
    pub fn reduce_inverse(&self, mut f: Vec<Fp<M>>) -> Vec<Fp<M>> {
        normalize(&mut f);
        assert!(
            f.len() < self.p.len(),
            "Reducer の次数( = p.len() ）未満でお願いします。"
        );
        self.reduce(Fp::convolution(f, self.r2.clone()))
    }
    /// p を法として、多項式の掛け算をします。
    ///
    /// # 使用例
    ///
    /// ```
    /// use montgomery::Montgomery;
    /// use fp::F998244353 as Fp;
    ///
    /// // 法を x² - 1 にセットです。( x⁻³ = x mod p )
    /// let mont = Montgomery::new(vec![-Fp::new(1), Fp::new(0), Fp::new(1)]);
    ///
    /// let f = vec![Fp::new(8), Fp::new(4)];   // f(x) = 4x + 8 とします。
    /// let g = vec![Fp::new(3), Fp::new(2)];   // g(x) = 2x + 3 とします。
    /// let result = mont.mul_single(f, g);     // f(x) g(x) = ( 8x² + 28x + 24 ) mod p です。
    ///
    /// let expected = vec![Fp::new(32), Fp::new(28)]; // 28x + 32 です。
    /// assert_eq!(result, expected);
    /// ```
    pub fn mul_single(&self, mut f: Vec<Fp<M>>, mut g: Vec<Fp<M>>) -> Vec<Fp<M>> {
        normalize(&mut f);
        normalize(&mut g);
        if f.is_empty() || g.is_empty() {
            return Vec::new();
        }
        self.reduce(Fp::convolution(
            self.reduce(Fp::convolution(f, g)),
            self.r2.clone(),
        ))
    }
    /// p を法として、多項式の冪を計算します。
    ///
    /// # 使用例
    ///
    /// ```
    /// use montgomery::Montgomery;
    /// use fp::F998244353 as Fp;
    ///
    /// // 法を x² - 1 にセットです。( x⁻³ = x mod p )
    /// let mont = Montgomery::new(vec![-Fp::new(1), Fp::new(0), Fp::new(1)]);
    ///
    /// let f = vec![Fp::new(1), Fp::new(2)];   // f(x) = 2x + 1 とします。
    /// let result = mont.pow_single(f, 3 as u32);     // f(x)³ = ( 8x³ + 12x² + 6x + 1) mod p です。
    ///
    /// let expected = vec![Fp::new(13), Fp::new(14)]; // 14x + 13 です。
    /// assert_eq!(result, expected);
    /// ```
    pub fn pow_single(&self, mut f: Vec<Fp<M>>, pow: impl Into<u64>) -> Vec<Fp<M>> {
        let mut pow = pow.into();
        normalize(&mut f);
        if f.is_empty() {
            return match pow {
                0 => vec![Fp::new(1)],
                _ => Vec::new(),
            };
        }
        let mut f = self.reduce(f);
        let mut ans = self.reduce(vec![Fp::new(1)]);
        while pow != 0 {
            if pow % 2 == 1 {
                ans = self.reduce(Fp::convolution(
                    self.reduce_inverse(ans),
                    self.reduce_inverse(f.clone()),
                ));
            }
            pow /= 2;
            f = self.reduce(Fp::convolution(
                self.reduce_inverse(f.clone()),
                self.reduce_inverse(f),
            ));
        }
        self.reduce_inverse(ans)
    }
}

/// ニュートン法で多項式の除算をします。モンゴメリはしません。
///
/// # 入力
///
/// * f: 多項式
/// * g: 多項式
///
/// ただし trailing zeros のある場合は自動的に削られます。
///
///
/// # Panics
///
/// * g が 0 のとき
///
///
/// # 出力
///
/// 以下のものを、trailing zeros なしで返します。
///
/// * f div g
/// * f mod g
///
pub fn div_rem_newton<M: Mod>(mut f: Vec<Fp<M>>, mut g: Vec<Fp<M>>) -> [Vec<Fp<M>>; 2]
where
    Fp<M>: Convolution,
{
    normalize(&mut f);
    normalize(&mut g);
    assert!(!g.is_empty(), "g は 0 でない多項式である必要があります。");
    if f.len() < g.len() {
        return [Vec::new(), f];
    }
    f.reverse();
    g.reverse();
    let len = f.len() + 1 - g.len();
    let mut div = Fp::convolution(f.clone(), fps::fps_inverse(g.clone(), len));
    div.truncate(len);
    f.reverse();
    g.reverse();
    div.reverse();
    let mut rem = f
        .iter()
        .copied()
        .zip(
            Fp::convolution(g.clone(), div.clone())
                .into_iter()
                .chain(repeat(Fp::new(0))),
        )
        .map(|(x, y)| x - y)
        .take(g.len() - 1)
        .collect::<Vec<_>>();
    debug_assert_eq!(rem.len(), g.len() - 1);
    normalize(&mut div);
    normalize(&mut rem);
    [div, rem]
}

fn normalize<M: Mod>(f: &mut Vec<Fp<M>>) {
    while f.last().map_or(false, |&x| x == Fp::new(0)) {
        f.pop().unwrap();
    }
}

fn reduce<M: Mod>(p: Vec<Fp<M>>, k: Vec<Fp<M>>, f: &[Fp<M>]) -> Vec<Fp<M>>
where
    Fp<M>: Convolution,
{
    if f.is_empty() {
        return Vec::new();
    }
    debug_assert!(!p.is_empty());
    debug_assert_eq!(p.len(), k.len());
    let n = p.len();
    debug_assert_eq!(
        Fp::convolution(p.clone(), k.clone())
            .into_iter()
            .take(n)
            .collect::<Vec<_>>(),
        once(-Fp::new(1))
            .chain(repeat(Fp::new(0)))
            .take(n)
            .collect::<Vec<_>>(),
    );

    let mut fk_bar = Fp::convolution(
        f.iter()
            .copied()
            .chain(repeat(Fp::new(0)))
            .take(n)
            .collect::<Vec<_>>(),
        k,
    );
    fk_bar.push(Fp::new(0));
    fk_bar.truncate(n);
    debug_assert_eq!(fk_bar.len(), n);

    let mut ans = Fp::convolution(p, fk_bar);
    ans.resize(2 * n - 1, Fp::new(0));
    ans.iter_mut().zip(f.iter()).for_each(|(x, y)| *x += *y);
    debug_assert!(ans[..n].iter().all(|&x| x == Fp::new(0)));
    let mut ans = ans[n..].to_vec();
    debug_assert_eq!(ans.len(), n - 1);
    normalize(&mut ans);
    ans
}

#[cfg(test)]
mod tests {
    use {
        super::{div_rem_newton, normalize, Montgomery},
        fp::F998244353 as Fp,
        fps::Convolution,
        itertools::Itertools,
        rand::{prelude::StdRng, Rng, SeedableRng},
        std::iter::{once, repeat, repeat_with},
        test_case::test_case,
    };

    #[allow(clippy::unused_unit)]
    #[test_case(3; "small")]
    #[test_case(30; "medium")]
    #[test_case(std::u32::MAX; "large")]
    fn test_mul_single(lim: u32) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..30);
            let f = repeat_with(|| Fp::new(rng.gen_range(0..lim)))
                .take(n)
                .collect_vec();
            let g = once(1)
                .chain(repeat(0))
                .take(n)
                .map(|start| Fp::new(rng.gen_range(start..lim)))
                .collect_vec();
            let p = once(1)
                .chain(repeat(0).take(n - 1))
                .chain(once(1))
                .map(|start| Fp::new(rng.gen_range(start..lim)))
                .collect_vec();
            let mont = Montgomery::new(p.clone());

            let rem = mont.mul_single(f.clone(), g.clone());
            let fg = Fp::convolution(f.clone(), g.clone());

            let [_, expected_rem] = div_rem_newton(fg.clone(), p.clone());
            assert_eq!(expected_rem, rem);
        }
    }

    #[allow(clippy::unused_unit)]
    #[test_case(3, 50; "small")]
    #[test_case(30, 100_000; "medium")]
    #[test_case(std::u32::MAX, std::u64::MAX; "large")]
    fn test_pow_single(lim: u32, pow_lim: u64) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..3);
            let f = repeat_with(|| Fp::new(rng.gen_range(0..lim)))
                .take(n)
                .collect_vec();
            let pow = rng.gen_range(0..pow_lim);
            let p = once(1)
                .chain(repeat(0).take(n - 1))
                .chain(once(1))
                .map(|start| Fp::new(rng.gen_range(start..lim)))
                .collect_vec();
            let mont = Montgomery::new(p.clone());
            let result = mont.pow_single(f.clone(), pow);
            let expected = {
                let mut ans = vec![Fp::new(1)];
                let mut pow = pow;
                let mut f = f.clone();
                while pow != 0 {
                    if pow % 2 == 1 {
                        ans = mont.mul_single(ans, f.clone());
                    }
                    f = mont.mul_single(f.clone(), f);
                    pow /= 2;
                }
                ans
            };
            assert_eq!(result, expected);
        }
    }

    #[allow(clippy::unused_unit)]
    #[test_case(3; "small")]
    #[test_case(30; "medium")]
    #[test_case(std::u32::MAX; "large")]
    fn test_reduce_inverse(lim: u32) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..20 {
            let n = rng.gen_range(1..30);
            let f = repeat_with(|| Fp::new(rng.gen_range(0..lim)))
                .take(n)
                .collect_vec();
            let mut normal_f = f.clone();
            normalize(&mut normal_f);
            let p = once(1)
                .chain(repeat(0).take(n - 1))
                .chain(once(1))
                .map(|start| Fp::new(rng.gen_range(start..lim)))
                .collect_vec();
            let mont = Montgomery::new(p.clone());

            let expected_to_be_f = mont.reduce_inverse(mont.reduce(f.clone()));
            assert_eq!(normal_f, expected_to_be_f);

            let expected_to_be_f = mont.reduce(mont.reduce_inverse(f));
            assert_eq!(normal_f, expected_to_be_f);
        }
    }

    #[test]
    fn test_fibonacci() {
        const LIM: usize = 40;
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..10 {
            let init = repeat_with(|| Fp::new(rng.gen_range(0..std::u32::MAX)))
                .take(2)
                .collect_vec();
            let f = vec![-Fp::new(1), -Fp::new(1), Fp::new(1)];
            let mont = Montgomery::new(f.clone());
            let expected = {
                let mut ans = init.clone();
                while ans.len() < LIM {
                    let x = ans[ans.len() - 2] + ans[ans.len() - 1];
                    ans.push(x);
                }
                ans
            };
            for i in 0..LIM {
                let coeffs = mont.pow_single(vec![Fp::new(0), Fp::new(1)], i as u64);
                let result = init
                    .iter()
                    .zip(coeffs.iter())
                    .map(|(&x, &y)| x * y)
                    .sum::<Fp>();
                let expected = expected[i];
                assert_eq!(result, expected);
            }
        }
    }
}
