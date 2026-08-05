# max_flow ベンチマーク結果

| Algorithm | Random | Gary's case | 日付 |
|---------|-----------|------------|------|
| 00. Dinic | 216.59 ms | 242.45 ms | 2026-08-03 |
| 01. Dinic with backward DFS | 111.08 ms | 148.04 ms | 2026-08-04 |
| 02. Push-Relabel with Heap | 148.79 ms | 132.37 ms | 2026-08-04 |
| 03. Push-Relabel with BFS Init. | 47.381 ms | 111.36 ms | 2026-08-04 |

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


## 01. Dinic with backward DFS

DFS を逆から行うことで、到達不能な頂点を訪れることを防ぐ


## 02. Push-Relabel with Heap

Excess 頂点を heap で管理する(highest height戦略)

## 03. Push-Relabel with BFS Init.

高さの初期化を次のように変更しました

* 旧: source 以外全て $0$
* 新: source 以外全て sink からの $G_f$ における距離

