# FFT Benchmark Report


| Version | `fft_1^23` | `fft_with_twiddle_factors` | 
| - | - | - |
| 00. Radix-2 decimation in frequency | 255.11 ms | - |
| 01. Pre-Calculate Twiddle Factors | 172.55 ms | 155.02 ms |
| 02. Radix-4 decimation in frequency (no pre-calculation) | 159.67 ms | - |
| 03. Pre-Calculation & Radix-4 | 175.02 ms | 195.43 ms |


## 00. Radix-2 decimation in frequency

これを素直にやります。

```rust
[*a, *b] = [*a + *b, *a - *b];
*b *= wk;
wk *= w;
```

## 01. Radix-2 decimation in frequency

`fft` 関数内で Twiddle factor を全て前計算。
データ表現は、$(\_, e[0], e[0], e[1/4], e[0], e[1/8], e[2/8], e[3/8], e[0], ...)$

ちなみに、`build_twiddle_factors` 自体の benchmark 結果は 21.789 ms

```rust
let mut len = 4;
while len <= n {
    for i in 0..len / 4 {
        twiddle_factors[len / 2 + i * 2] = twiddle_factors[len / 4 + i];
    }
    for i in 0..len / 4 {
        twiddle_factors[len / 2 + i * 2 + 1] =
            twiddle_factors[len / 2 + i * 2] * Diroot::FORWARD[len.trailing_zeros() as usize];
    }
    len *= 2;
}
```

## 02. Radix-4 decimation in frequency (no pre-calculation)

一旦 pre-calculation を revert して、radix-4 を試します。

$n, n / 4, n / 16, \dots$ のように行います。

```rust
[*a, *c] = [*a + *c, *a - *c];
[*b, *d] = [*b + *d, *b - *d];
*d *= forth;
[*a, *b] = [*a + *b, *a - *b];
[*c, *d] = [*c + *d, *c - *d];
let wk2 = wk * wk;
*b *= wk2;
*c *= wk;
*d *= wk * wk2;
wk *= w;
```

## 03. Pre-Calculation & Radix-4

`wk`, `wk2` を `twiddle_factors` から取ってきます。$n/2 \le 3i$ になりうるので結局 $w ^ {3i}$ は計算しないといけないというね。

逆効果でした。

```rust
[*a, *c] = [*a + *c, *a - *c];
[*b, *d] = [*b + *d, *b - *d];
*d *= forth;
[*a, *b] = [*a + *b, *a - *b];
[*c, *d] = [*c + *d, *c - *d];
let w = twiddle_factors[n / 2 + i];
let w2 = twiddle_factors[n / 4 + i];
*b *= w2;
*c *= w;
*d *= w2 * w;
```

## アイデアメモ

`twiddle_factors` は半周分ではなく全周分計算すると良いことがありそう

* `fft` 用と `ifft` 用を兼ねられる
* そうしたら `Diroot::{FORWARD, BACKWARD}` も片方でよくなる
* Radix-4 のときの $n / 2 \le 3i$ 問題も解決する
* でも当然長さは $2$ 倍になる
