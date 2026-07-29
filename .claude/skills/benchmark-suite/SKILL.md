---
name: benchmark-suite
description: 任意の関数の criterion ベンチマークを作成し、ベースライン測定を行い、最適化全体での改善を追跡します。ベンチマークコード、REPORT.md テンプレート、および測定ワークフロー自動化を生成します。
compatibility:
  - Read
  - Write
  - Edit
  - Bash
---

# ベンチマークスイート: 測定と最適化の追跡

任意の関数に対するベンチマークを作成、実行、追跡する汎用スキル。最適化の反復全体にわたります。

## 入力

ユーザーが以下を提供：
- **関数名**: 例 `fps_inv`、`fft`、`poly_mul`
- **ライブラリ/クレート**: 関数が定義されている場所（例 `fp_fps`、`fp_fft`）
- **関数シグネチャ**: 主要なパラメータとその範囲
  - 例：`fps_inv(&[Fp<P>], precision)` ただし `precision = 2^20`
- **ターゲット反復時間**: ベンチマーク反復あたりのターゲット実行時間（例 "~200ms"）
- **入力セットアップ**: 現実的なテストデータを構築する方法
  - 例：「f[0] = 1 で他の要素が連続的な多項式」

## プロセス

### フェーズ 1: ベンチマークインフラストラクチャを作成

#### 1.1 ディレクトリとファイルを作成

```
benches/benches/{function_name}_benchmark/
├── main.rs          # Criterion ベンチマークコード
└── REPORT.md        # 結果追跡と改善ログ
```

#### 1.2 ベンチマークコードを書く

テンプレート（関数シグネチャに合わせて調整）:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use fp::{fp, Fp};
use {crate_name}::{function_name};

const P: u64 = 998_244_353;

fn {function_name}_bench_{size}(c: &mut Criterion) {
    c.bench_function("{function_name}_{size}", |b| {
        // Setup: create realistic test data
        let data = {/* setup code */};
        
        b.iter(|| {
            {function_name}(black_box(&data), /* params */)
        });
    });
}

criterion_group!(benches, {function_name}_bench_{size});
criterion_main!(benches);
```

**重要なポイント:**
- コンパイラの最適化を防ぐため、`black_box()` で入力をラップする
- 現実的なテストデータを使用する（些細なケースではない）
- ベンチマーク文字列の関数名は一致する必要があります：`"{function_name}_{size}"`
- 有限体クレート用に `const P: u64 = 998_244_353` を使用する

#### 1.3 REPORT.md テンプレートを作成

テンプレートは `report-template.md` を参照してください。`benches/benches/{function_name}_benchmark/REPORT.md` にコピーしてから、`{関数名}` をプレースホルダーとして使用します。

### フェーズ 2: ベースラインを登録して実行

#### 2.1 `benches/Cargo.toml` を更新

`[dependencies]` に追加：
```toml
{crate_name} = { path = "../libs/{crate_name}" }
```

ベンチマークターゲットを追加：
```toml
[[bench]]
name = "{function_name}_benchmark"
harness = false
```

#### 2.2 ベースライン測定を実行

```bash
cd /repo/root
cargo bench --bench {function_name}_benchmark -- --output-format bencher
```

**予想される出力:**
```
{function_name}_{size}          time:   [XXX ms XXX ms XXX ms]
```

完全な criterion 出力を `REPORT.md` の「ベースライン → Criterion 出力」にコピーする。

#### 2.3 反復時間を確認して調整

**ターゲット範囲:** 反復あたり 100ms–500ms（統計的精度のため）

**測定がターゲット外の場合:**
- **高速すぎる** (<100ms): 入力サイズを増やす
  - 要素を追加、問題サイズをスケールアップ、密度を増加させる
  - 例：`n=512` を `n=2048` に変更、または `precision=2^20` を `2^22` に変更
- **遅すぎる** (>500ms): 入力サイズを減らす
  - 要素を減らし、スケールダウン、密度を低下させる
  - 例：`n=2048` を `n=512` に変更、または `precision=2^20` を `2^18` に変更

**アクション:**
1. `main.rs` ベンチマーク入力サイズを調整
2. 測定を再実行
3. 反復時間が 100ms–500ms 範囲に収まるまで繰り返す
4. 最終テストケースパラメータで `REPORT.md` を更新

### フェーズ 3: 最適化の反復

各最適化試行に対して：

1. **関数を修正** `libs/{crate_name}/src/lib.rs` で
2. **測定を実行**:
   ```bash
   cargo bench --bench {function_name}_benchmark -- --output-format bencher
   ```
3. **REPORT.md に記録**:
   - 新しい「最適化 vN」セクションを追加
   - Criterion 出力を貼り付け
   - % 改善を計算：`((baseline - new) / baseline) * 100`
4. **新しい測定でサマリーテーブルを更新**

### フェーズ 4: 分析と決定

各測定サイクルの後：
- ✅ 改善 > 5% の場合：最適化を保持することを検討
- ❌ 改善 < 2% の場合：トレードオフが複雑さを正当化しないかもしれない
- 🔄 回帰がある場合：元に戻して別のアプローチを試す

## 出力チェックリスト

- ✅ `benches/benches/{function_name}_benchmark/main.rs` 作成
- ✅ `benches/benches/{function_name}_benchmark/REPORT.md` テンプレート付きで作成
- ✅ `benches/Cargo.toml` deps + ベンチマークターゲットで更新
- ✅ ベースライン測定を実行して記録
- ✅ 反復時間を検証（100ms–500ms 範囲。必要に応じて調整）
- ✅ 最適化の反復に準備完了

## 最適化の準備完了：次のコマンド

```bash
cargo bench --bench {function_name}_benchmark -- --output-format bencher
```

**使用方法:**
1. `libs/{crate_name}/src/lib.rs` の関数を修正
2. 上記のコマンドを実行して改善を測定
3. 結果を `benches/benches/{function_name}_benchmark/REPORT.md` に記録
4. 新しい測定でサマリーテーブルを更新
5. 各最適化試行に対して繰り返す

## 典型的なワークフロー

```
1. [ユーザー] 「fps_inv、precision=2^20 のベンチマークを作成」
2. [スキル] main.rs、REPORT.md を作成、Cargo.toml を更新
3. [スキル] ベースラインを実行：「time: [156.85 ms 157.21 ms 157.58 ms]」
4. [ユーザー] 「fps_inv を最適化させてください...」
5. [ユーザー] 「もう一度測定」
6. [スキル] 測定を実行：「time: [102.43 ms 103.15 ms 104.12 ms]」
7. [スキル] 計算：「34.5% スピードアップ！✅ これを保持」
8. [ユーザー] 「最適化 2 を試す...」
9. [満足まで繰り返す]
```

## ヒント

- **ターゲット時間が重要**：正確な criterion 統計のため、反復あたり 100ms–500ms を目指す
- **安定した測定**：静かなマシンで実行。バックグラウンドアプリを閉じる
- **サイズ選択**：保守的に開始（2^20 以下）、必要に応じてスケールアップ
- **結果をドキュメント化**：REPORT.md はラボノート。予期しない結果をメモする

## 制限事項

- 特別なセットアップが必要なベンチマークを処理しない（例：データベースフィクスチャ）
- 関数が決定論的であることを前提（同じ入力 → 同じ時間）
- ハードウェア変更に対するパフォーマンス追跡を行わない
