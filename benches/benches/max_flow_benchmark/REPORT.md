# max_flow ベンチマーク結果

## ベースライン（初期実装）

- **テストケース 1**: ランダムグラフ (n=40000頂点, m=400000エッジ, m/n=10でBFS回数が最大, source=0, sink=39999)
- **テストケース 2**: MiSawaキラーケース (depth=200層, layer_size=200, 頂点数=40003, current_edge最適化の検証用)
- **ターゲット反復時間**: ~100-500ms
- **日付**: 2026-08-03

**パラメータ選定**:
- `stats/stat_max_flow`での実験により、ランダムグラフでBFS回数が最大になるのはm/n=10～20
- ランダムグラフはm/n=10で設定（BFS回数最大化）
- キラーケースはhttps://gist.github.com/MiSawa/47b1d99c372daffb6891662db1a2b686 の構造をスケールアップ
  - source → a, b; b → a; a → 層状構造 → c → sink
  - 各層layer_size頂点、各頂点から次層の全頂点へ辺（完全二部グラフ的）
  - current_edge最適化のバグがあると指数時間になる構造

### Criterion 出力
```
Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 21.1s, or reduce sample count to 20.
test max_flow_random_n40000_m400000 ... bench:   218060229 ns/iter (+/- 12170320)

Warning: Unable to complete 100 samples in 5.0s. You may wish to increase target time to 16.6s, or reduce sample count to 30.
test max_flow_killer_case_depth200_layer200 ... bench:   165896542 ns/iter (+/- 3256516)
```

- **ランダムグラフ**: 約218ms ✅ (目標範囲内)
- **キラーケース**: 約166ms ✅ (目標範囲内)

**注**: キラーケースはlayer_size=2, depth=20000にするとバグのない実装では約2.6msで速すぎる。
current_edge最適化のバグがあるとO(layer_size^depth) = O(2^20000)で実行不可能になるが、
正しい実装ではO(V²E)で高速。layer_size=200にすることで適度な計算量を確保。

---

## サマリーテーブル

### ランダムグラフ (n=40000, m=400000, m/n=10)
| バージョン | 時間 (ms) | ベースラインとの比較 | 日付 |
|---------|-----------|------------|------|
| ベースライン | 218.1 | — | 2026-08-03 |

### MiSawaキラーケース (depth=200, layer_size=200)
| バージョン | 時間 (ms) | ベースラインとの比較 | 日付 |
|---------|-----------|------------|------|
| ベースライン | 165.9 | — | 2026-08-03 |

---

## メモと学習

- **ランダムグラフ**: 典型的なユースケース、グラフの疎密性による性能変化
- **二分木状グラフ**: Dinicのcurrent_edge最適化が効かないとO(2^depth)に悪化するキラーケース
  - 参考: https://gist.github.com/MiSawa/47b1d99c372daffb6891662db1a2b686
  - 正しい実装ではO(V²E)で処理できる

---

## 最適化セクション追加時のテンプレート

新しい最適化がある場合は、以下を追加してください：

```markdown
## 最適化 v1: [最適化説明]

- **変更**: [何が最適化されたか]
- **日付**: [測定日]

### Criterion 出力
```
[Criterion 出力を貼り付け]
```

### 改善
- **ランダムグラフ**: ベースラインより XX% 高速
- **二分木グラフ**: ベースラインより XX% 高速
- **分析**: [うまくいったこと、予期しない結果]

---
```

サマリーテーブルにも行を追加してください。
