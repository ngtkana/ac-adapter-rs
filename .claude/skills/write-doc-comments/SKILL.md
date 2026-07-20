---
name: write-doc-comments
description: Generate comprehensive doc comments for Rust library crates. Use this whenever a user needs to write or improve documentation for a library's public API. Given a library path, generates doc comments for all pub items (traits, structs, enums, functions, methods) following Rust std library conventions. Always include Examples sections for every pub item.
compatibility:
  - Read
  - Edit
  - Write
---

# Write Doc Comments for Rust Libraries

Your task is to generate high-quality doc comments for a Rust library following the Rust standard library documentation style.

## Input

The user will specify:
- **Library path**: e.g., `libs/fenwick/src/lib.rs` or `src/lib.rs`
- **Optional notes**: Any specific documentation patterns, style preferences, or context

Note: Crate-level documentation (`//!`) is **always** included; the user does not need to request it.

## Process

### 1. Crate-level Documentation (always included)

Add or update a `//!` module comment at the top of lib.rs with this structure:

```rust
//! One-line summary of what this crate does.
//!
//! Longer explanation of:
//! - Primary use cases (When would you use this?)
//! - What problems it solves
//! - Key features or capabilities
//!
//! # Examples
//!
//! ```
//! [Realistic example showing typical usage]
//! ```
//!
//! # Module / Item Overview
//!
//! - [`NamedItem`]: Brief description of what this trait/struct is for
//! - [`AnotherItem`]: ...
//!
//! # Complexity
//!
//! (Optional but useful for algorithm libraries)
//! - Operation A: O(log n)
//! - Operation B: O(1)
```

**Guidelines for crate-level docs:**
- Keep it 100–200 lines (high-level overview, not detailed)
- Focus on "When & Why" not "How" (leave "How" to item-level docs)
- Include one concrete, runnable example
- List key items and what they're for
- For algorithm/data structure libraries, include complexity info
- Avoid overwhelming detail — readers should quickly grasp purpose and scope

**If crate-level docs already exist:** Improve and refine them to meet these standards rather than replacing. Keep the existing structure if it's sound; polish clarity, add missing sections (Examples, Complexity if appropriate), and ensure tone is consistent with Std library style.

### 2. Item-level Documentation

1. **Read the library file(s)** — understand the public API structure
2. **Identify all pub items**:
   - Traits (trait keyword, pub visibility)
   - Structs (struct keyword, pub visibility)
   - Enums (enum keyword, pub visibility) — document the enum itself, but NOT enum variants (unless they have special meaning beyond simple data carrying)
   - Functions (fn keyword, pub visibility)
   - Methods (impl blocks with pub functions)
3. **Generate doc comments** for each item following these patterns:

### Documentation Patterns

#### Traits

```rust
/// Brief one-line description of what the trait represents.
///
/// Longer explanation of when and how to implement or use this trait.
/// Explain the invariants or contract that implementations must uphold.
///
/// # Examples
///
/// ```
/// [Concrete example showing implementation or usage]
/// ```
pub trait MyTrait {
```

#### Structs

```rust
/// Brief one-line description.
///
/// Longer explanation including:
/// - What this struct represents
/// - When you would use it
/// - Any important invariants
///
/// # Examples
///
/// ```
/// [Example: creating and using the struct]
/// ```
pub struct MyStruct {
```

#### Enums

```rust
/// Brief one-line description.
///
/// Longer explanation of the different variants and when to use each.
///
/// # Examples
///
/// ```
/// [Example showing enum usage and pattern matching]
/// ```
pub enum MyEnum {
```

Do NOT document individual enum variants unless they carry special meaning beyond simple data carrying (use your judgment; when in doubt, ask the user).

#### Functions and Methods

For straightforward, self-explanatory functions/methods:

```rust
/// One-line description.
///
/// # Examples
///
/// ```
/// [Simple example]
/// ```
pub fn simple_method(&self) {
```

For more complex functions/methods with parameters or important behavior:

```rust
/// Brief one-line description.
///
/// Longer explanation of behavior, including:
/// - What this does
/// - Any important side effects or guarantees
/// - Panic conditions (if any)
///
/// # Arguments
///
/// * `param1` - Description of param1
/// * `param2` - Description of param2
///
/// # Examples
///
/// ```
/// [Realistic example showing typical usage]
/// ```
pub fn complex_method(&mut self, param1: T, param2: usize) -> Result<U> {
```

### Style Guidelines

- **Keep explanations concise and clear** — use simple English
- **Examples section is mandatory** for every pub item
- **Examples should be realistic** — show actual use cases, not trivial toy examples
- **Use backticks** for code identifiers and types (e.g., \`Vec<T>\`, \`add_assign\`)
- **Reference related items** using backticks (e.g., "See \`other_method\`" links in Rust docs)
- **For simple methods**, 2-3 sentences + example is often sufficient
- **Follow std library tone** — informative but not overly verbose

### Examples Philosophy

Each example should:
1. Be runnable (or clearly a logical example)
2. Show the typical use case
3. For methods on generic types, include a concrete instantiation
4. Keep it short — usually 3-10 lines

Bad: `"let x = my_method()"` with no context
Good: Full struct creation + method call with clear intent

## Output

Return the **full source file** with:
1. **Crate-level documentation** (`//!` at the top) — newly written or refined
2. **Item-level documentation** (`///` on each pub item) — newly written or refined

Use standard Rust doc comment syntax throughout.

**If documentation already exists:** Do not replace it wholesale. Instead, treat the existing docs as a foundation and:
- Refine unclear explanations
- Expand to meet the standards (add missing Examples, parameters, edge cases)
- Improve tone and clarity to match Std library style
- Remove redundant or outdated information

## Quality Checklist

### Crate-level (if applicable)
- [ ] One-line summary at the top
- [ ] "When & Why" section explaining use cases
- [ ] At least one runnable example
- [ ] Brief overview of main items
- [ ] (Optional) Complexity info for algorithm libraries
- [ ] Total length: 100–200 lines

### Item-level
- [ ] Every pub trait has a doc comment with Examples
- [ ] Every pub struct has a doc comment with Examples
- [ ] Every pub enum has a doc comment with Examples (variants excluded unless special)
- [ ] Every pub fn and pub method has a doc comment with Examples
- [ ] Examples are realistic and functional
- [ ] Language is clear and concise
- [ ] Style follows Rust std library conventions
