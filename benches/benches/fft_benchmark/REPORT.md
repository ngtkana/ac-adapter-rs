# FFT/IFFT 高速化ベンチマーク結果

## 環境
- FFT サイズ: 1<<23 (8,388,608 elements)
- Prime P: 998_244_353
- Compiler: rustc 1.89.0
- Build: release (optimized)

## Baseline (2025-07-24)
**実装**: 既存の radix-2 DIF Cooley-Tukey

```
fft_1<<23: 256.72 ms - 257.72 ms
  Mean: 257.21 ms
  Std Dev: ~0.50 ms
  Samples: 100
```

---

## ステップ1: Butterfly Operation 融合（4要素ずつアンロール）

**実装**: 内側ループを 4 要素ずつ処理、twiddle factor を事前計算

```
fft_1<<23: 242.71 ms - 244.74 ms
  Mean: 243.68 ms
  Std Dev: ~1.03 ms
  Samples: 100
```

**改善結果**:
- 絶対値: 257.21 - 243.68 = **13.53 ms削減**
- 改善率: **5.3% 高速化** ✓
- テスト状態: ✓ ユニットテスト通過（6/6） / ✓ プロパティテスト通過（6/6）
- 状態: **✓ 確定採用**

---

## ステップ2: Radix-4 化

*実装予定*

---

## まとめ

| 最適化 | 平均時間 | 改善率 | 状態 |
|--------|---------|--------|------|
| Baseline | 257.21 ms | - | ✓ 確定 |
| Butterfly融合 | 243.68 ms | 5.3% | ✓ **確定採用** |
| Radix-4化 | - | - | 実装中 |
