# Verify User Claims and Corrections

When a user corrects, contradicts, or challenges a prior analysis or finding:

1. **Do not silently accept the correction** — verify it independently before acting
2. **Run concrete checks:**
   - Execute code/tests to confirm the claim (if applicable)
   - Search documentation or version logs for facts (e.g., Rust edition availability)
   - Re-examine the evidence that contradicts your prior statement
3. **Report your findings:**
   - Quote the evidence that proves the correction is right (or wrong)
   - If evidence confirms the user: update findings with outcome annotation
   - If evidence refutes the user: explain why and ask for clarification
4. **Never assume the user is correct just because they asserted it** — even experienced users make typos or misremember details

**Rationale:** Trust but verify. User corrections often point to real issues, but verification catches mutual mistakes and ensures the final record is accurate.
