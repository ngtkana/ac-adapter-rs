# max_flow ベンチマーク結果

| Algorithm | Random | Worst | 日付 |
|---------|-----------|------------|------|
| v0 | 216.59 ms | 242.45 ms | 2026-08-03 |
| v1 | 111.08 ms | 148.04 ms | 2026-08-03 |

## Instances

### Random

* $V = 1 \cdot 10 ^ 5$
* $E = 5 \cdot 10 ^ 5$

### Worst

* $V = 3 \cdot 10 ^ 3$

https://deepblue.lib.umich.edu/items/ca084c10-fdcf-451b-a874-f3d367f3c299

## Algorithms

## v0: Dinic

DFS を 1 回で済ませる

$O(V^2E)$ 時間


## v1: Dinic with backward DFS

DFS を逆から行うことで、到達不能頂点を調べなくて済むという huristic 高速化
