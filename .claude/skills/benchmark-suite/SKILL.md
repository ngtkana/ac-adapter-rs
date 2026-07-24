---
name: benchmark-suite
description: Create criterion benchmarks for any function, measure baseline, and track improvements over optimizations. Generates benchmark code, REPORT.md template, and automates measurement workflow.
compatibility:
  - Read
  - Write
  - Edit
  - Bash
---

# Benchmark Suite: Measure & Track Optimizations

Generic skill to create, run, and track benchmarks for any function across optimization iterations.

## Input

The user provides:
- **Function name**: e.g., `fps_inv`, `fft`, `poly_mul`
- **Library/crate**: Where the function is defined (e.g., `fp_fps`, `fp_fft`)
- **Function signature**: Key parameters and their ranges
  - Example: `fps_inv(&[Fp<P>], precision)` with `precision = 2^20`
- **Target iteration time**: Target execution time per benchmark iteration (e.g., "~200ms")
- **Input setup**: How to construct realistic test data
  - Example: "polynomial with f[0] = 1, other elements sequential"

## Process

### Phase 1: Create Benchmark Infrastructure

#### 1.1 Create Directory & Files

```
benches/benches/{function_name}_benchmark/
├── main.rs          # Criterion benchmark code
└── REPORT.md        # Results tracking and improvement log
```

#### 1.2 Write Benchmark Code

Template (adapt to function signature):

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

**Key points:**
- Wrap inputs with `black_box()` to prevent compiler optimizations
- Use realistic test data (not trivial cases)
- Function name in benchmark string must match: `"{function_name}_{size}"`
- Use `const P: u64 = 998_244_353` for finite field crates

#### 1.3 Create REPORT.md Template

```markdown
# {Function Name} Benchmark Results

## Baseline (Initial Implementation)

- **Test case**: [Describe input size/parameters]
- **Target iteration time**: [e.g., ~200ms]
- **Date**: [when measured]

### Criterion Output
\`\`\`
[Paste criterion benchmark output here]
\`\`\`

---

## Optimized v1: [Optimization description]

- **Changes**: [What was optimized]
- **Date**: [measurement date]

### Criterion Output
\`\`\`
[Paste criterion output]
\`\`\`

### Improvement
- **Speedup**: XX% faster than baseline
- **Analysis**: [What worked, unexpected results]

---

## Optimized v2: [Next optimization]

[Repeat structure]

---

## Summary Table

| Version | Time (ms) | vs Baseline | Date |
|---------|-----------|------------|------|
| Baseline | XXX | — | YYYY-MM-DD |
| v1 | XXX | +XX% | YYYY-MM-DD |
| v2 | XXX | +XX% | YYYY-MM-DD |

---

## Notes & Learnings

- [Key findings about what optimizes this function]
- [Performance characteristics by size/parameter]
- [Compiler/architecture observations]
```

### Phase 2: Register & Run Baseline

#### 2.1 Update `benches/Cargo.toml`

Add to `[dependencies]`:
```toml
{crate_name} = { path = "../libs/{crate_name}" }
```

Add benchmark target:
```toml
[[bench]]
name = "{function_name}_benchmark"
harness = false
```

#### 2.2 Run Baseline Measurement

```bash
cd /repo/root
cargo bench --bench {function_name}_benchmark -- --output-format bencher
```

**Expected output:**
```
{function_name}_{size}          time:   [XXX ms XXX ms XXX ms]
```

Copy the full criterion output to `REPORT.md` under "Baseline → Criterion Output".

### Phase 3: Iterate on Optimizations

For each optimization attempt:

1. **Modify the function** in `libs/{crate_name}/src/lib.rs`
2. **Run measurement**:
   ```bash
   cargo bench --bench {function_name}_benchmark -- --output-format bencher
   ```
3. **Record in REPORT.md**:
   - Add new "Optimized vN" section
   - Paste criterion output
   - Calculate % improvement: `((baseline - new) / baseline) * 100`
4. **Update Summary Table** with new measurement

### Phase 4: Analysis & Decision

After each measurement cycle:
- ✅ If improvement > 5%: consider keeping the optimization
- ❌ If improvement < 2%: trade-off may not justify complexity
- 🔄 If regression: revert and try different approach

## Output Checklist

- ✅ `benches/benches/{function_name}_benchmark/main.rs` created
- ✅ `benches/benches/{function_name}_benchmark/REPORT.md` created with template
- ✅ `benches/Cargo.toml` updated with deps + benchmark target
- ✅ Baseline measurement executed and recorded
- ✅ Ready for optimization iteration

## Typical Workflow

```
1. [User] "Create benchmark for fps_inv, precision=2^20"
2. [Skill] Creates main.rs, REPORT.md, updates Cargo.toml
3. [Skill] Runs baseline: "time: [156.85 ms 157.21 ms 157.58 ms]"
4. [User] "Let me optimize fps_inv..."
5. [User] "Measure again"
6. [Skill] Runs measurement: "time: [102.43 ms 103.15 ms 104.12 ms]"
7. [Skill] Calculates: "34.5% speedup! ✅ Keep this."
8. [User] "Try optimization 2..."
9. [Repeat until satisfied]
```

## Tips

- **Target time matters**: Aim for 100ms–500ms per iteration for accurate criterion statistics
- **Stable measurements**: Run on quiet machine; close background apps
- **Size selection**: Start conservative (2^20 or smaller), scale up if needed
- **Document findings**: REPORT.md is your lab notebook—note unexpected results

## Limitations

- Does not handle benchmarks requiring special setup (e.g., database fixtures)
- Assumes function is deterministic (same inputs → same time)
- Does not track performance vs hardware changes
