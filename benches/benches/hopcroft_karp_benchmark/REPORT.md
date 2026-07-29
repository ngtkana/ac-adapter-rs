# Hopcroft-Karp Benchmark Results

## Baseline (Initial Implementation)

- **Test case**: Bipartite graph with 1M total nodes (500K left, 500K right), 1M edges
- **Target iteration time**: ~200ms range (100ms–500ms)
- **Date**: 2026-07-29

### Criterion Output
```
test hopcroft_karp_V1M_E1M ... bench:   271171005 ns/iter (+/- 5675346)
```

**Observation**: Baseline runs at ~271 ms per iteration. ✅ **Within target range**. Good statistical stability (±5.7 ms). Ready for optimization iteration.

---

## Optimized v1: Remove current-edge iterator structure, use label marking

- **Changes**: 
  - Removed `iter` array (current-edge tracking structure)
  - Changed `primal()` to accept `g: &[Vec<usize>]` instead of `iter: &mut [Iter<'_, usize>]`
  - Direct edge iteration: `for &y in &g[x]` instead of `iter[x].next()`
  - Label caching: Save `label[x]` to `d`, then set `label[x] = usize::MAX` to prevent revisiting node
  - Removed tests (moved to separate crate)
- **Date**: 2026-07-30

### Criterion Output
```
test hopcroft_karp_V1M_E1M ... bench:   219242364 ns/iter (+/- 5050334)
```

### Improvement
- **Speedup**: 19.2% faster than baseline
- **Analysis**: Eliminating the iterator array reduces memory overhead and improves cache locality. Label-marking technique prevents redundant node revisits during DFS, achieving the same correctness as current-edge tracking with simpler code.

---

## Summary Table

| Version | Time (ms) | vs Baseline | Date |
|---------|-----------|------------|------|
| Baseline | 271.2 | — | 2026-07-29 |
| v1 | 219.2 | -19.2% | 2026-07-30 |

---

## Notes & Learnings

- [Key findings about what optimizes this function]
- [Performance characteristics by size/parameter]
- [Compiler/architecture observations]
