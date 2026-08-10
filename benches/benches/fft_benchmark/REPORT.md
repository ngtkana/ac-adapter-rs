# FFT Benchmark Report


| Version | `fft_1^23` | `fft_with_twiddle_factors` | 
| - | - | - |
| 00. Radix-2 decimation in frequency | 255.11 ms | - |
| 01. Pre-Calculation of Twiddle Factors | 182.98 ms | 137.69 ms |


## 00. Radix-2 decimation in frequency

これを素直にやります。

```rust
[*a, *b] = [*a + *b, *a - *b];
*b *= wk;
wk *= w;
```

## 01. Pre-Calculation of Twiddle Factors

`fft` 関数内で Twiddle factor を全て前計算。

ちなみに、`build_twiddle_factors` 自体の benchmark 結果は 42.979 ms

```rust
let mut n = items.len();
while n >= 2 {
    for chunk in items.chunks_mut(n) {
        for i in 0..n / 2 {
            let [a, b] = unsafe { chunk.get_disjoint_unchecked_mut([i, i + n / 2]) };
            [*a, *b] = [*a + *b, *a - *b];
            *b *= twiddle_factors[n + i];
        }
    }
    n /= 2;
}
```
