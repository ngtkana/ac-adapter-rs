# {関数名} ベンチマーク

## 設定

- **パラメータ1**: {値 (数式表記可: 2^20, 3×10^6など)}
- **パラメータ2**: {値}
- **ターゲット**: 100–500 ms/反復

## ベンチマーク

| 名前 | 反復時間 | 測定対象 |
|------|---------|---------|
| benchmark_1 | XXX ms ✓ | {説明} |
| benchmark_2 | XXX ms ✓ | {説明} |

## パフォーマンス（単位）

- Operation A: X.X ns/op
- Operation B: X.X ns/op

## ベースライン（Criterion）

```
test benchmark_1 ... bench:   XXX ns/iter (+/- YYY)
test benchmark_2 ... bench:   XXX ns/iter (+/- YYY)
```

## 前提条件

- {各ベンチマークの初期状態を明記}
- {計測対象と計測外の境界}
- {データセット生成方法}

## 最適化記録（vN）

### 最適化 v1: {説明}

```
test benchmark_1 ... bench:   XXX ns/iter (+/- YYY)
test benchmark_2 ... bench:   XXX ns/iter (+/- YYY)
```

改善：benchmark_1 [X%] / benchmark_2 [X%]
