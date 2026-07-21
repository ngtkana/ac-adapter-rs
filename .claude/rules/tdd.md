---
paths:
  - "libs/**/*.rs"
  - "tests/**/*.rs"
---

# Test Driven Development (TDD) — Testing Standards

Based on the implementation patterns from _Test Driven Development_ (Kent Beck), following the approach emphasized by twada.

## The Three Phases: Red → Green → Refactor

1. **Red Phase**: Write a failing test that specifies the desired behavior
   - The test defines *what* the code should do
   - Expected values come from the specification, not from running the code
   - Failure confirms the test is meaningful
   - **Doc comments and doctests count as tests.** For new `pub` items, write the doc comment (usage, complexity, invariants) and its `# Examples` doctest(s) *before* the implementation body. Doctests are compiled and executed by `cargo test`, so they are bound by the same rule: expected values come from the specification, not from running the code. Confirm the doctest fails first (compile error, or a runtime panic via `todo!()`) before writing the implementation.

2. **Green Phase**: Write minimal code to make the test pass
   - No more, no less
   - If multiple tests fail, make them pass one at a time

3. **Refactor Phase**: Improve the code without changing behavior
   - Tests stay green throughout
   - Only the implementation changes, never the test expectations

## Core Rule: Tests Are Specification

**Fundamental principle**: A test's expected value must be determined *before* the code is written. The expected value comes from the **specification, not from the code**.

**🚫 Absolutely Prohibited:**
- Observing code output and using that to set test expected values
- Modifying test expectations to match what the code currently does
- Treating "the test passes" as evidence that the test is correct
- Silently fixing test expectations

**✅ The Only Valid Source of Expected Values:**
- Specification or requirements document
- Mathematical correctness proof (e.g., algorithm invariant, formula)
- Domain knowledge or real-world constraint
- Previously verified, audited behavior from a trusted reference

## When Test Expectations Must Change

**Allowed only when**:
1. You have documented evidence the previous expectation was incorrect
2. You can prove the new expectation is correct
3. You get explicit approval before making the change

**Valid reasons to change an expectation**:
- "The spec says X, but the test expected Y" (provide spec reference)
- "The algorithm invariant requires X; test had Y which violates it" (provide invariant)
- "The test itself had a bug; the correct expected value is X" (explain the bug)

**Invalid reasons**:
- "The code produces Y, so the test should expect Y" ← **This is backwards**
- "The test failed, so I'll change the expectation" ← **This defeats the purpose**

## When a Test Fails During Implementation

1. **Stop immediately** — do not modify the test
2. **Analyze**:
   - Is the code wrong? (The normal case — fix the code)
   - Is the test wrong? (Rare — but if so, provide evidence before changing)
   - Is the expectation wrong? (Very rare — but if so, provide evidence before changing)
3. **Report to the user** if the test or expectation might be wrong
4. **Never guess** — escalate with evidence, not assumptions

## For Code Reviewers (Claude)

- If a test fails unexpectedly, **report it** — do not modify the test to pass
- Include evidence: spec reference, mathematical proof, domain knowledge
- All test expectation changes require justification
- Commit messages must explain *why* an expectation changed, not just *what* changed

---

## Summary

The core discipline: **Test expectations are locked down by specification, and locked forever by pride.**

We write the test first (Red), the code second (Green), and improve the code third (Refactor) — but we never, ever move backward from Green to Red by changing the test.
