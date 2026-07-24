---
name: specify-and-test
description: Understand function specification from naive reference, generate doc-comments, create comprehensive random tests, and verify implementation against specification (not vice versa).
compatibility:
  - Read
  - Write
  - Edit
  - Bash
---

# Specify & Test: Specification-Driven Development

Three-phase skill to understand a function's specification from its naive reference, document it, test it comprehensively, and trust the spec over the code.

## Input

The user provides:
- **Function name**: e.g., `mask_lower_part`
- **Crate**: e.g., `fp_fft`
- **Main implementation**: File path (e.g., `libs/fp_fft/src/lib.rs`)
- **Naive reference**: Test file path and function name (e.g., `libs/fp_fft/tests/test_postfft.rs::naive_mask_lower_part`)

## Process

### Phase 1: Specification Extraction & Understanding

#### 1.1 Read Naive Implementation

- Read the naive function from test file
- **Document the specification**:
  - What does it do?
  - Input preconditions (e.g., "array length must be power of two")
  - Output postconditions (what changes?)
  - Invariants

#### 1.2 Read Optimized Implementation

- Read the main implementation
- Compare with naive version
- Identify optimizations

#### 1.3 Specification Summary

Create internal notes (for Claude) describing:
- **Specification (from naive)**: Plain English or pseudo-code
- **Optimized approach (from main)**: How it achieves the same result faster
- **Test strategy**: What to verify via random testing

**Example format**:
```
Specification (from naive_mask_lower_part):
  1. Inverse FFT the entire array
  2. Zero out the lower half (indices 0..len/2)
  3. Forward FFT the entire array
  Result: A masked frequency-domain array

Optimized approach (from mask_lower_part):
  - Splits array in half (a, b)
  - Only IFFT upper half (b)
  - Apply twiddle factors to upper half
  - Only FFT upper half (b)
  - Combine results via averaging
  Result: Same mathematical effect, faster
```

### Phase 2: Documentation Generation

#### 2.1 Create Doc Comment (Manual or via /write-doc-comments)

Generate `///` doc comment for the function with:
- **One-line summary**: What the function does (from naive spec)
- **Longer explanation**: 
  - Purpose and use case
  - Mathematical meaning
  - Input preconditions
  - Output postconditions
- **Examples section**: 
  - Realistic example using the function
  - Verify result matches naive specification
- **Complexity** (if relevant): Time/space complexity

**Template**:
```rust
/// Brief description of what this does.
///
/// Longer explanation:
/// - This function [what it does, from naive spec]
/// - Input [x] must be [precondition]
/// - Output [y] will be [postcondition]
///
/// # Examples
///
/// ```
/// [Example code verifying against naive expectation]
/// ```
pub fn function_name(...) {
```

#### 2.2 Add Doc Comment to Source

Edit `libs/{crate}/src/lib.rs` to insert doc comment above function.

### Phase 3: Random Test Generation

#### 3.1 Create Test File (if doesn't exist)

Path: `libs/{crate}/tests/compare_with_naive.rs`

#### 3.2 Import Naive Function

```rust
// At top of test file, import from source test file or redefine
use fp_fft::fft; // (or other dependencies)

fn naive_function_name(...) {
    // Copy from tests/{original_test_file}.rs
    // ...
}
```

#### 3.3 Create Random Test Suite

**Pattern** (follow fp_fps, fp_precalc conventions):

```rust
#[test]
fn test_function_name_compare_with_naive() {
    let mut rng = StdRng::seed_from_u64(42);
    for _ in 0..200 {
        // Generate random input within specification bounds
        let size = 1 << rng.gen_range(0..=6);  // Or appropriate range
        let mut input: Vec<_> = (...).collect();
        
        // Ensure preconditions are met (e.g., f[0] is invertible)
        // input[0] = fp(rng.gen_range(1..P));
        
        // Clone for comparison
        let mut expected = input.clone();
        let mut result = input.clone();
        
        // Run naive version on expected
        naive_function_name(&mut expected);
        
        // Run optimized version on result
        function_name(&mut result);
        
        // Verify they match
        assert_eq!(result, expected, "input: {:?}", input);
    }
}
```

**Key points**:
- **Iteration count**: 200+ cycles (follow fp_fps pattern)
- **Size variation**: Test multiple sizes via `rng.gen_range()`
- **Precondition setup**: Ensure input satisfies function requirements
- **Black box**: If needed, use `black_box()` for criterion-like behavior
- **Clear error messages**: Include input in assertion for debugging

#### 3.4 Add to Test Targets

Update `Cargo.toml` if needed:
```toml
[[test]]
name = "compare_with_naive"
harness = true
```

### Phase 4: Verification & Bug Handling

#### 4.1 Run Tests

```bash
cd /repo
cargo test --lib {crate_name}
cargo test --test compare_with_naive
```

#### 4.2 Test Failures: Trust the Spec, Not the Code

**If test fails**:
1. **Do NOT modify the test** — the test encodes the specification
2. **Assume the implementation has a bug**
3. **Analyze the failure**:
   - What precondition is violated?
   - What postcondition does the output fail?
   - Which step of the naive algorithm is being skipped in the optimized version?
4. **Report to user**:
   - Show failing input
   - Show expected vs actual
   - Point to the implementation line that's likely wrong
   - Suggest fix (do not apply without user approval)

**Example failure report**:
```
Test: test_mask_lower_part_compare_with_naive
Input: f = [1, 2, 3, 4]
Expected (naive): [a, b, c, d]
Actual (optimized): [x, y, z, w]

Difference: Upper half values don't match.
Likely bug: Line 42 in lib.rs — twiddle factor application may be 
incorrect for even/odd indices.
```

### Phase 5: Iteration (if needed)

After user fixes the implementation:
1. Re-run tests
2. If still failing, repeat Phase 4.2
3. If passing, doc-string verification is complete ✅

## Output Checklist

- ✅ Specification understood and documented (internal notes)
- ✅ Doc comment added to function in `libs/{crate}/src/lib.rs`
- ✅ Test file created: `libs/{crate}/tests/compare_with_naive.rs`
- ✅ Random test suite (200+ iterations) implemented
- ✅ All tests passing
- ✅ Implementation verified against specification

## Key Principle

**The test is the specification. The code is the implementation.**

When test and code disagree → the code is wrong, not the test.
Modify the implementation until it matches the specification,
never the reverse.

## Tips

- **Naive = Specification**: Treat naive version as golden truth
- **Optimize freely**: The optimized version can be completely different internally
- **Same inputs → same outputs**: That's the contract being tested
- **Document the WHY**: The doc comment should explain what the function does (from naive spec), not how it does it (from optimized code)
- **Test sizes**: Include power-of-two sizes that exercise all code paths
