//! ラグランジュ補完
//!
//! # できること
//!
//! ラグランジュ補間はこれです。
//!
//! | できること                            | 計算量            | 関数名                                |
//! | - | - | - |
//! | n 点から多項式の係数を復元            | Θ ( N ^ 2 lg P ) | [`interpolate`]                       |
//! | 0..n の評価から多項式の係数を復元     | Θ ( N ^ 2 )      | [`interpolate_first_n`]               |
//! | 0..n の評価から多項式の係数を復元     | Θ ( N lg P )     | [`interpolate_one_point_first_n`]     |
//!
//!
//! ついでにどうせテストで使いたいですし一緒に使うことも多いので、多項式を評価する関数もご用意いたしました。[`evaluate`]
//!
//!
//! # 一般の等差数列上の評価からの復元
//!
//! g ( x ) =  f ( a x + y ) と定めて、g に関して復元をするとできるので用意しません。

use fp::Fp;
use std::iter::once;

/// 多項式の係数から 1 点での評価を計算します。
///
/// # 使い方
///
/// ```
/// use lagrange::evaluate;
/// type Fp = fp::Fp<998244353>;
///
/// // 13 ^ 2 = 169
/// assert_eq!(
///     evaluate(&[Fp::new(0), Fp::new(0), Fp::new(1)], Fp::new(13)),
///     Fp::new(169)
/// );
/// ```
///
/// # 計算量
///
/// O ( N )
pub fn evaluate<const P: u64>(a: &[Fp<P>], x: Fp<P>) -> Fp<P> {
    let mut power = Fp::new(1);
    let mut ans = Fp::new(0);
    for &ai in a {
        ans += ai * power;
        power *= x;
    }
    ans
}

/// x 座標の異なるような N 点の評価から、N - 1 次以下の多項式を一意的に復元します。
///
/// # 使い方
///
/// ```
/// use lagrange::interpolate;
/// type Fp = fp::Fp<998244353>;
///
/// // [[0, 0], [1, 1], [2, 4], [3, 9]] -> x ^ 2
/// let eval = [
///     [Fp::new(0), Fp::new(0)],
///     [Fp::new(1), Fp::new(1)],
///     [Fp::new(2), Fp::new(4)],
///     [Fp::new(3), Fp::new(9)],
/// ];
/// let poly = [Fp::new(0), Fp::new(0), Fp::new(1), Fp::new(0)];
/// assert_eq!(interpolate(&eval), poly);
/// ```
///
/// # 計算量
///
/// xi - xj の逆数の計算でログが乗ります。
///
/// O ( N ^ 2 lg P )
///
///
/// # Panics
///
/// * evals が空のとき
/// * x 座標が distinct でないとき
pub fn interpolate<const P: u64>(evals: &[[Fp<P>; 2]]) -> Vec<Fp<P>> {
    assert!(!evals.is_empty());
    evals
        .iter()
        .enumerate()
        .map(|(i, &[xi, yi])| {
            let (left, right) = evals.split_at(i);
            let (_, right) = right.split_at(1);
            left.iter()
                .chain(right.iter())
                .fold(vec![yi], |mut acc, &[xj, _]| {
                    let scalar = (xi - xj).inv();
                    acc.iter_mut().for_each(|y| *y *= scalar);
                    acc.insert(0, Fp::new(0));
                    for i in 0..acc.len() - 1 {
                        let sub = acc[i + 1] * xj;
                        acc[i] -= sub;
                    }
                    acc
                })
        })
        .fold(vec![Fp::new(0); evals.len()], |acc, f| {
            acc.iter()
                .zip(f.iter())
                .map(|(&x, &y)| x + y)
                .collect::<Vec<_>>()
        })
}

/// 0..N の評価から、N - 1 次以下の多項式を一意的に復元します。
///
/// # 使い方
///
/// ```
/// use lagrange::interpolate;
/// type Fp = fp::Fp<998244353>;
///
/// // [[0, 0], [1, 1], [2, 4], [3, 9]] -> x ^ 2
/// let eval = [
///     [Fp::new(0), Fp::new(0)],
///     [Fp::new(1), Fp::new(1)],
///     [Fp::new(2), Fp::new(4)],
///     [Fp::new(3), Fp::new(9)],
/// ];
/// let poly = [Fp::new(0), Fp::new(0), Fp::new(1), Fp::new(0)];
/// assert_eq!(interpolate(&eval), poly);
/// ```
///
/// # 計算量
///
/// xi - xj の逆数の計算は、定数時間で行うのでログが乗りません。
///
/// Θ ( N ^ 2 )
///
/// # Panics
///
/// * evals が空のとき
pub fn interpolate_first_n<const P: u64>(evals: &[Fp<P>]) -> Vec<Fp<P>> {
    assert!(!evals.is_empty());
    let n = evals.len();
    if n == 1 {
        return evals.to_vec();
    }
    let mut inv = vec![Fp::new(0); n];
    inv[1] = Fp::new(1);
    for i in 2..n {
        let q = P as usize / i;
        let r = P as usize - i * q;
        inv[i] = -Fp::from(q) * inv[r];
    }
    evals
        .iter()
        .enumerate()
        .map(|(xi, &yi)| {
            (0..n).filter(|&xj| xj != xi).fold(vec![yi], |mut acc, xj| {
                let scalar = if xi > xj { inv[xi - xj] } else { -inv[xj - xi] };
                acc.iter_mut().for_each(|y| *y *= scalar);
                acc.insert(0, Fp::new(0));
                for i in 0..acc.len() - 1 {
                    let sub = acc[i + 1] * Fp::from(xj);
                    acc[i] -= sub;
                }
                acc
            })
        })
        .fold(vec![Fp::new(0); n], |acc, f| {
            acc.iter()
                .zip(f.iter())
                .map(|(&x, &y)| x + y)
                .collect::<Vec<_>>()
        })
}

/// 0..N での評価から決まる N - 1
/// 次以下の一意的な多項式で、与えられた点を評価します。
///
/// # 使い方
///
/// ```
/// use lagrange::interpolate_one_point_first_n;
/// type Fp = fp::Fp<998244353>;
///
/// // [[0, 0], [1, 1], [2, 4], [3, 9]], 13 -> 13 ^ 2 = 169
/// let eval = [Fp::new(0), Fp::new(1), Fp::new(4), Fp::new(9)];
/// assert_eq!(
///     interpolate_one_point_first_n(&eval, Fp::new(13)),
///     Fp::new(169)
/// );
/// ```
///
/// # 計算量
///
/// Θ( N lg P )
///
///
/// # Panics
///
/// * evals が空のとき
pub fn interpolate_one_point_first_n<const P: u64>(evals: &[Fp<P>], x: Fp<P>) -> Fp<P> {
    assert!(!evals.is_empty());
    if (x.value() as usize) < evals.len() {
        return evals[x.value() as usize];
    }
    let n = evals.len();
    let init = (1..n)
        .map(|j| (x - Fp::from(j)) / -Fp::from(j))
        .product::<Fp<P>>();
    evals
        .iter()
        .zip(once(init).chain((0..n - 1).scan(init, |state, i| {
            *state *= (x - Fp::from(i)) * (-Fp::from(n - 1 - i));
            *state /= (x - Fp::from(i + 1)) * (Fp::from(i + 1));
            Some(*state)
        })))
        .map(|(&y, coeff)| y * coeff)
        .sum()
}

#[cfg(test)]
mod tests {
    use super::evaluate;
    use super::interpolate;
    use super::interpolate_first_n;
    use super::interpolate_one_point_first_n;
    use itertools::Itertools;
    use rand::prelude::StdRng;
    use rand::Rng;
    use rand::SeedableRng;
    use std::collections::HashSet;
    use std::iter::repeat_with;
    use test_case::test_case;

    const P: u64 = 998244353;
    type Fp = fp::Fp<P>;

    #[test_case(3; "small")]
    #[test_case(30; "medium")]
    #[test_case(P; "maximum")]
    fn test_interpolate_rand(lim: u64) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..20.min(lim as usize));
            let mut used = HashSet::new();
            let evals = repeat_with(|| {
                [
                    Fp::new(rng.gen_range(0..lim)),
                    Fp::new(rng.gen_range(0..lim)),
                ]
            })
            .filter(|&[x, _]| {
                if used.contains(&x) {
                    false
                } else {
                    used.insert(x);
                    true
                }
            })
            .take(n)
            .collect_vec();
            let poly = interpolate(&evals);
            for &[x, y] in &evals {
                assert_eq!(y, evaluate(&poly, x));
            }
        }
    }

    #[test_case(3; "small")]
    #[test_case(30; "medium")]
    #[test_case(P; "maximum")]
    fn test_interpolate_first_n_rand(lim: u64) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..20);
            let evals = repeat_with(|| Fp::new(rng.gen_range(0..lim)))
                .take(n)
                .collect_vec();
            let poly = interpolate_first_n(&evals);
            for (i, &y) in evals.iter().enumerate() {
                assert_eq!(y, evaluate(&poly, Fp::from(i)));
            }
        }
    }

    #[test_case(3; "small")]
    #[test_case(30; "medium")]
    #[test_case(P; "maximum")]
    fn test_interpolate_one_point_rand(lim: u64) {
        let mut rng = StdRng::seed_from_u64(42);
        for _ in 0..200 {
            let n = rng.gen_range(1..3);
            let evals = repeat_with(|| Fp::new(rng.gen_range(0..lim)))
                .take(n)
                .collect_vec();
            let poly = interpolate(
                &evals
                    .iter()
                    .enumerate()
                    .map(|(i, &y)| [Fp::from(i), y])
                    .collect_vec(),
            );
            let x = Fp::new(rng.gen_range(0..lim));
            let y = interpolate_one_point_first_n(&evals, x);
            assert_eq!(y, evaluate(&poly, x));
        }
    }
}
