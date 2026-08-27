# w_ary_tree Predecessor Query ベンチマーク

## 設定

- **$N$**: $2^{29}$
- **$Q$**: $3 \times 10^6$
- **ターゲット**: 100–500 ms/反復

## ベンチマーク

| 名前 | 反復時間 | クエリ単位 | 説明 |
|------|---------|---------|------|
| constructor | 192.9 ms ✓ | — | 確率 $1/2$ のビット列から構築 |
| predecessor_sparse | 111.4 ms ✓ | 37.1 ns/op | $10^3$ 個（Fisher-Yates）での操作 |
| insert | 127.6 ms ✓ | 42.5 ns/op | 空の木からのinsert |

## ベースライン（Criterion）

```
test constructor ... bench:   192938203 ns/iter (+/- 1861368)
test predecessor_sparse ... bench:   111381825 ns/iter (+/- 5572326)
test insert ... bench:   127612102 ns/iter (+/- 5271561)
```

## 最適化記録（vN）

### 最適化 v1: [説明]

```
test constructor ... bench:   XXX ns/iter (+/- YYY)
test predecessor_sparse ... bench:   XXX ns/iter (+/- YYY)
test insert ... bench:   XXX ns/iter (+/- YYY)
```

改善：constructor [X%] / predecessor_sparse [X%] / insert [X%]
