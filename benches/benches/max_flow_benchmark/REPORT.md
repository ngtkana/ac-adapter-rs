# max_flow ベンチマーク結果

| Algorithm | Random | Gary's case | 日付 |
|---------|-----------|------------|------|
| v0: Dinic | 216.59 ms | 242.45 ms | 2026-08-03 |
| v1: Dinic with backward DFS | 111.08 ms | 148.04 ms | 2026-08-04 |
| v2: Push-Relabel with Heap | 159.56 ms | 118.98 ms | 2026-08-04 |
| v3: Push-Relabel with Buckets | 148.05 ms | 131.92 ms | 2026-08-04 |
| v4: Push-Relabel with Gap Heuristic | 156.07 ms | 8.6569 μs | 2026-08-04 |
| v4: Push-Relabel with BFS Init. | 152.92 ms | 8.8233 μs | 2026-08-04 |

## Instances

### Random

* $V = 1 \cdot 10 ^ 5$
* $E = 5 \cdot 10 ^ 5$

### Gary's case

* $V = 3 \cdot 10 ^ 3$

https://deepblue.lib.umich.edu/items/ca084c10-fdcf-451b-a874-f3d367f3c299

## Algorithms

## v0: Dinic

DFS を 1 回で済ませる

$O(V^2E)$ 時間


## v1: Dinic with backward DFS

DFS を逆から行うことで、到達不能な頂点を訪れることを防ぐ


## v2: Push-Relabel by Heap

Excess 頂点を heap で管理する(highest height戦略)

## v3: Push-Relabel by Buckets

それを buckets に変更

## v4: Push-Relabel by Gap Heuristic

Gap heuristic を導入。そのために各 $h$ に対して高さ $h$ である中間ノードの個数を管理します。

## v5: Push-Relabel by BFS Init.

高さの初期化を次のように行います:

* source: $n$
* sink: $0$
* internal: $G_f$ における sink への距離

