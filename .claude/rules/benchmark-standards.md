# ベンチマーク標準

ベンチマーク実装時に従うべき標準的な方法とベストプラクティス。

## 1. Black Box の使用

**ルール**: 計測対象のすべてのデータ（入力・結果・クエリ）に `black_box()` を適用する

**理由**: コンパイラの最適化（定数畳み込み、デッドコード削除）を防ぎ、実アプリケーション環境に近い性能測定を実現

**実装例**:
```rust
// ❌ 不十分
b.iter(|| func(black_box(&input)));

// ✅ 正しい
b.iter(|| black_box(func(black_box(&input))));

// クエリベンチマークの場合
b.iter(|| {
    let mut tree = create_tree(black_box(&initial_data));
    tree.execute_operation(black_box(&queries));
    black_box(tree)
});
```

## 2. 反復時間の目標

**標準目標**: 100–500 ms per iteration

**理由**: 
- Criterion の統計精度向上（100 ms未満では変動が大きい）
- 測定時間の現実性（500 msを超えるとベンチマーク実行時間が膨らむ）
- 既存ベンチマーク（bipartite_matching: 271 ms, fps_inv: 157 ms）との統一

**調整方法**: N（データサイズ）と Q（クエリ数）をバランスよく調整
- 反復時間が短い → N/Q を増やす
- 反復時間が長い → N/Q を減らす

**表記**: パラメータは数式表記可（2^20, 3×10^6など）

## 3. Sparsity 生成（Set/Tree データ構造の場合）

**推奨方法**: Exact Count Sampling（Fisher-Yates Shuffle）

**理由**: 確実な要素個数保証＋ランダム配置による現実性

**実装**:
```rust
use rand::seq::SliceRandom;

fn gen_sparse_exact(n: usize, count: usize) -> Vec<bool> {
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let mut bits = vec![false; n];
    let mut indices: Vec<usize> = (0..n).collect();
    indices.shuffle(&mut rng);
    for i in 0..count.min(n) {
        bits[indices[i]] = true;
    }
    bits
}
```

**使用例**: 
- 密（dense）：`gen_bitstring(0.9)` 
- スパース（sparse）：`gen_sparse_exact(N, 1000)` で確実に 1000 個

## 3.5 クエリ/操作ベンチマークの計測外処理

**ルール**: クエリベンチマークでは、データ構造の構築を計測外にする

**実装方法**:
```rust
// ❌ 誤り：構築が計測に含まれる
b.iter(|| {
    let mut tree = DataStructure::new(n);  // 計測内
    tree.query(black_box(&queries));
    black_box(tree)
});

// ✅ 正しい：構築が計測外
let tree = DataStructure::new(n);  // 計測外：セットアップ
let queries = gen_queries(q);      // 計測外：セットアップ
b.iter_batched(
    || tree.clone(),  // 計測外：各反復の初期化
    |mut t| {
        t.query(black_box(&queries));  // 計測内：操作のみ
        black_box(t)
    },
    BatchSize::SmallInput,
);

// または、BTreeMap が Clone を持つ場合：
let tree = DataStructure::new(n);
b.iter(|| {
    let mut t = tree.clone();  // 計測外：複製（初期化と見なす）
    t.query(black_box(&queries));
    black_box(t)
});
```

**理由**: 
- データ構造の操作性能を正確に計測
- 構築時間は `constructor` ベンチマークで独立して計測
- クエリ単位の性能分析が可能

**例外**: 
- 構築自体が最適化対象の場合は、独立した `constructor` ベンチマークを用意

## 4. 複数シナリオのテスト

**ルール**: 単一のシナリオではなく、複数の入力特性でベンチマークを実施

**最小構成**:
- Constructor/構築
- 操作（dense なデータ）
- 操作（sparse なデータ）
- 特殊操作（insert, delete など）

**理由**: データ構造の実装特性を正確に反映（例：w_ary_tree はスパースで 2.9 倍遅い）

## 5. クエリベンチマークの単位化

**ルール**: クエリベンチマークは「1反復 = Q 個のクエリ実行」で統一

**明記方法**: REPORT.md に以下を記載
```
**反復単位**: 1 反復 = Q = {値} クエリを実行
クエリ単位の性能は (反復時間 / Q) で計算可能
```

**例**:
- 反復時間: 114ms, Q = 50M → クエリ単位: 2.3 μs/query

## 6. REPORT.md の記載

**シンプル構成を維持**:
1. 設定（パラメータ値のみ）
2. ベンチマーク結果表（シンプルな表形式）
3. パフォーマンス（単位化された数値）
4. ベースライン（Criterion 出力そのまま）
5. **前提条件**（各ベンチマークの初期状態・計測外・データセット生成法）
6. 最適化記録テンプレート

**前提条件セクションの必須項目**:
- 各ベンチマークの初期状態（constructor の入力、insert の開始状態など）
- 計測対象と計測外の明確な区別
- スパース/密などの特殊なデータセット生成方法

**原則**: 完結性重視。不要な説明は書かない。前提条件は明確に。

## 7. 性能向上の判定基準

**基準**:
- ✅ 改善 > 5%：最適化を保持
- 🤔 改善 2-5%：トレードオフを検討
- ❌ 改善 < 2%：複雑さが正当化されない可能性
- 🔄 回帰あり：元に戻す

## 8. ファイル構成と簡潔性

```
benches/benches/{name}_benchmark/
├── main.rs        （シンプル、計測対象のコードのみ）
└── REPORT.md      （シンプル、設定・結果・テンプレートのみ）
```

**main.rs ガイドライン**:
- 150-200 行程度に保つ
- 関数は `gen_*`, `benchmark_*` で命名統一

**REPORT.md ガイドライン**:
- シンプル構成を必ず守る
- 不要な説明は削除
- 表と箇条書きを活用
- ベースライン Criterion 出力は貼り付け（コピペ）

---

**根拠**: w_ary_tree (predecessor query) ベンチマーク実装経験から得た標準化。スパース/密の大幅な性能差（2.9x）検出による重要性確認。
