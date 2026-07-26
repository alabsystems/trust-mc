<!-- dscan:allow(volatile_numbers) -->
# Debugging Slow Proofs

trust-mc uses SAT/SMT solvers to verify code, which can sometimes result in slow or non-terminating proofs. This chapter outlines common causes of slowness and strategies to debug and improve proof performance.

## Common Causes of Slow Proofs

### Complex/Large Non-deterministic Types
Some types are inherently more expensive to represent symbolically, e.g. strings, which have complex validation rules for UTF-8 encoding,
or large bounded collections, like a vector with a large size.

### Large Value Operations
Mathematical operations on large values can be expensive, e.g., multiplication/division/modulo, especially with larger types (e.g., `u64`).

### Unbounded Loops
If trust-mc cannot determine a loop bound, it will unwind forever, c.f. [the loop unwinding tutorial](./tutorial-loop-unwinding.md).

## Debugging Strategies

These are some strategies to debug slow proofs, ordered roughly in terms of in the order you should try them:

### Limit Loop Iterations

First, identify whether (unbounded) loop unwinding may be the root cause. Try the `#[kani::unwind]` attribute or the `--unwind` option to limit [loop unwinding](./tutorial-loop-unwinding.md). If the proof fails because the unwind value is too low, but raising it causing the proof to be too slow, try specifying a [loop contract](./reference/experimental/loop-contracts.md) instead.

### Use Different Solvers

trust-mc supports multiple SMT solvers that may perform differently on your specific problem. Select the solver with `--smt-solver` (or its alias `--ay-solver`):

| Solver | Description |
|--------|-------------|
| `auto` | (Default) Uses ay native - the production solver |
| `ay`   | Force native AY solver (the default/production solver) |
| `direct` | Use direct AY linking without subprocess (requires `ay-direct` feature) |

Example:
```bash
trust-mc --smt-solver=ay your_file.rs
```

The `#[kani::solver]` [attribute](./reference/attributes.md) from upstream Kani is ignored by trust-mc's AY backend (a warning is emitted). Use `--smt-solver` (or `--ay-solver`) to configure AY solver selection instead.

### Remove Sources of Nondeterminism

Start by replacing `kani::any()` calls with concrete values to isolate the problem:

```rust
#[kani::proof]
fn slow_proof() {
    // Instead of this:
    // let x: u64 = kani::any();
    // let y: u64 = kani::any();

    // Try this:
    let x: u64 = 42;
    let y: u64 = 100;

    let result = complex_function(x, y);
    assert!(result > 0);
}
```

If the proof becomes fast with concrete values, the issue is likely with the symbolic representation of your inputs. In that case, see you can [partition the proof](#partition-the-input-space) to cover different ranges of possible values, or restrict the proof to a smaller range of values if that is acceptable for your use case.

### Reduce Collection Sizes

Similarly, if smaller values are acceptable for your proof, use those instead:

```rust
#[kani::proof]
fn test_with_small_collection() {
    // Instead of a large Vec
    // let vec: Vec<u8> = kani::bounded_any::<_, 100>();

    // Start with a small size
    let vec: Vec<u8> = kani::bounded_any::<_, 2>();

    process_collection(&vec);
}
```

### Partition the Input Space

Break down complex proofs by partitioning the input space:

```rust
// Instead of one slow proof with large inputs
#[kani::proof]
fn test_multiplication_slow() {
    let x: u64 = kani::any();
    let y: u64 = kani::any();

    // This might be too slow for the solver
    let result = x.saturating_mul(y);
    assert!(result >= x || x == 0);
}

// Split into multiple proofs with bounded inputs
#[kani::proof]
fn test_multiplication_small_values() {
    let x: u64 = kani::any_where(|x| *x <= 100);
    let y: u64 = kani::any_where(|y| *y <= 100);

    let result = x.saturating_mul(y);
    assert!(result >= x || x == 0);
}

// Insert harnesses for other ranges of `x` and `y`
```

See [upstream Kani #3006](https://github.com/model-checking/kani/issues/3006) for tracking automatic partitioning support.

### Use Stubs

If a function has a complex body, consider using a [stub](./reference/experimental/stubbing.md) or a [verified stub](./reference/experimental/contracts.md) to stub the body with a simpler abstraction.

### Disable Unnecessary Checks

If you're focusing on functional correctness rather than safety, you may disable memory safety checks (run `trust-mc --help` for a list of options to do so). Note that disabling these checks may cause trust-mc to miss undefined behavior, so use it with caution.

Alternatively, to assume that all assertions succeed and only focus on finding safety violations, use the `--prove-safety-only` option.

## CHC-Specific Slowness

When using trust-mc's CHC backend (the default for unbounded verification), certain patterns cause the solver to timeout even when the property is valid.

### Loops with Symbolic Bounds

Simple symbolic-bound counting loops are no longer a blanket timeout case: the
checked-in 2026-03-20 tier2 reports record `7/7 PROOF` for
`tier2_unbounded` and `tier2_loop_for` at `AY@a70a12da`.

The remaining CHC timeout risk is symbolic-bound loops whose invariants are
harder to synthesize, especially when they combine the symbolic bound with
nonlinear arithmetic, multiple induction variables, or nested loop structure:

```rust
let n: u32 = kani::any();
kani::assume(n < 1_000_000);

// This simple counting shape is covered by the green tier2 reports
let mut i: u32 = 0;
while i < n {
    i += 1;
}
assert!(i == n);
```

The solver still struggles once the expected invariant stops looking like the simple
counting shape above. The usual hard cases are:

- nonlinear arithmetic (for example triangular sums or factorial-style growth)
- coupled induction variables
- nested symbolic loops

### Solutions for CHC Slowness

1. **Use constant bounds**: If a complex symbolic-bound loop times out, try concrete bounds to verify correctness within that range.

2. **Try BMC mode**: For bounded verification, BMC (Bounded Model Checking) may be faster:
   ```bash
   trust-mc --ay-emit-bmc --unwind 100 your_file.rs
   ```

3. **Partition the input space**: Split symbolic ranges into multiple proofs with concrete bounds.

See [CHC solver limitations](./chc-limitations.md) for the recorded tier2 evidence and the current workaround guidance.

## Advanced AY Tuning Flags (Experimental)

These flags are for advanced users experimenting with solver behavior. They may change between releases.

### Logic Override

Override the SMT-LIB logic with `--ay-logic`:

```bash
trust-mc --ay-logic=HORN your_file.rs    # Force Horn clause logic
trust-mc --ay-logic=QF_AUFBV your_file.rs  # Quantifier-free arrays+bitvectors
```

Default behavior:
- CHC mode (`--ay-chc`): Uses `HORN` logic
- BMC mode: Uses `QF_AUFBV` (or `ALL` when datatypes are present)

### CHC Memory Tracking

Control how memory operations are modeled with `--ay-chc-track`:

| Level | Description | Use Case |
|-------|-------------|----------|
| `reg` | (Default) Register-only: loads havoc, stores no-op | Fast proofs where memory aliasing isn't critical |
| `ptr` | Pointer validity: emits `r_ok` checks | Validating pointer bounds without full memory |
| `mem` | Full memory: uses select/store | Complete memory modeling (slower) |

Example:
```bash
trust-mc --ay-chc --ay-chc-track=mem your_file.rs
```

#### Wide Memory Model

For additional heap bounds checking, use `--ay-wide-mem` (alias: `--wide-mem`):

```bash
trust-mc --ay-chc --ay-chc-track=mem --ay-wide-mem your_file.rs
```

This enables the wide memory model which adds `is_dereferenceable` checks for heap accesses.
Use this when verifying memory-safety properties beyond basic validity, particularly for:
- Complex pointer arithmetic
- Allocation size tracking
- Defense-in-depth bounds validation

**Note**: Requires `--ay-chc` mode. Most effective with `--ay-chc-track=mem` since bounds
checks are generated during memory operations. Adds additional SMT constraints which may
increase solving time.

### CHC Transformation Pipeline

Enable transformations to simplify CHC problems before solving:

```bash
trust-mc --ay-chc --ay-chc-transform your_file.rs  # Safe transforms (scalarize, split-ite, split-or)
trust-mc --ay-chc --ay-chc-transform --ay-chc-transforms=inline your_file.rs  # Specific transform
trust-mc --ay-chc --ay-chc-transform --ay-chc-transforms=all your_file.rs  # All transforms (including inline)
```

Available transforms:
- `scalarize`: Convert array-sorted predicate arguments to scalar Int when arrays use constant indices only
- `split-ite`: Split ITE branches into separate Horn clauses
- `split-or`: Split OR branches into separate clauses
- `inline`: Inline simple predicates (opt-in; can cause regressions on some harnesses)
- `all`: Enable all transforms including inline

**Note**: The default (`--ay-chc-transform` without `--ay-chc-transforms`) enables only the safe set
(scalarize, split-ite, split-or). Inline preprocessing is opt-in because it can cause PROOF→UNKNOWN
regressions on some problem structures.
