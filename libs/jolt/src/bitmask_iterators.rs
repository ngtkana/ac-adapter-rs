use super::bitmask_operations::i2powm1;
use super::numeric_traits::Unsigned;

/// ちょうど $k$ ビット立っている $n$ ビットのビットマスクを昇順に列挙する。
///
/// $[0, 2^n)$ の整数のうち popcount が $k$ であるもの全体を昇順に返す。
/// 立っている最下位ビットの塊を 1 段上にずらす古典的な手法（Gosper's hack）で、
/// 各要素を $O(1)$ で次に進める。
///
/// # 計算量
///
/// 全体で $O(\binom{n}{k})$。
///
/// # 例
///
/// ```
/// use jolt::bitmask_combinations;
///
/// assert_eq!(bitmask_combinations::<u32>(3, 2).collect::<Vec<_>>(), vec![
///     3, 5, 6
/// ]);
/// ```
pub fn bitmask_combinations<T: Unsigned>(n: u32, k: u32) -> BitmaskCombinations<T> {
    assert!(k < T::bit_length() && n <= T::bit_length());
    BitmaskCombinations {
        n,
        bs: (T::ONE << k) - T::ONE,
        finished: false,
    }
}

/// [`bitmask_combinations`] が返すイテレータ。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct BitmaskCombinations<T> {
    n: u32,
    bs: T,
    finished: bool,
}
impl<T: Unsigned> Iterator for BitmaskCombinations<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let res = Some(self.bs);
        if self.bs == T::ZERO {
            self.finished = true;
        } else {
            let x = self.bs & self.bs.wrapping_neg();
            if self.bs > T::MAX - x {
                // `self.bs + x` would overflow `T`: `self.bs` was the last combination.
                self.finished = true;
            } else {
                let y = self.bs + x;
                let next_bs = (((self.bs & !y) / x) >> 1) | y;
                if next_bs > i2powm1::<T>(self.n) {
                    self.finished = true;
                } else {
                    self.bs = next_bs;
                }
            }
        }
        res
    }
}

/// `bs` の部分ビットマスク（`bs` 自身と $0$ を含む）を昇順に列挙する。
///
/// $s \mathbin{\&} \mathrm{bs} = s$ を満たす整数 $s$ 全体を昇順に返す。
/// 部分マスクを $1$ ずつ減らして `bs` との AND を取っていく古典的な手法を、
/// `bs` との XOR で反転させることで昇順化している。各要素 $O(1)$。
///
/// # 計算量
///
/// 全体で $O(2^{\mathrm{popcount}(\mathrm{bs})})$。
///
/// # 例
///
/// ```
/// use jolt::bitmask_subsets;
///
/// assert_eq!(bitmask_subsets(10u32).collect::<Vec<_>>(), vec![
///     0, 2, 8, 10
/// ]);
/// ```
pub fn bitmask_subsets<T: Unsigned>(bs: T) -> BitmaskSubsets<T> {
    BitmaskSubsets {
        bs,
        full: bs,
        finished: false,
    }
}

/// [`bitmask_subsets`] が返すイテレータ。
#[derive(Clone, Debug, Default, Hash, PartialEq, Eq)]
pub struct BitmaskSubsets<T> {
    bs: T,
    full: T,
    finished: bool,
}
impl<T: Unsigned> Iterator for BitmaskSubsets<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.finished {
            return None;
        }
        let res = Some(self.bs ^ self.full);
        if self.bs == T::ZERO {
            self.finished = true;
        } else {
            self.bs -= T::ONE;
            self.bs &= self.full;
        }
        res
    }
}
