<!-- dscan:allow(volatile_numbers) -->
# CHC Solver Limitations

Author: Andrew Yates <andrewyates.name@gmail.com>

trust-mc's CHC (Constrained Horn Clauses) backend uses the ay-chc portfolio solver, which implements the PDR/IC3 algorithm (among others) for inductive verification. While powerful for many verification tasks, the solver has fundamental limitations when verifying certain loop patterns.

## Quick Reference

| Pattern | Status | Notes |
|---------|--------|-------|
| Loops with constant bounds | Fully supported | Fast verification |
| Simple loops with weak assertions | Usually works | Depends on invariant complexity |
| Loops with symbolic bounds (counting/accumulation) | Unmeasured on the current pin | Last recorded 7/7 PROOF at AY@a70a12da (2026-03-20) |
| Loops with complex nonlinear invariants | Limited | May timeout depending on invariant complexity |
| Nested loops with parametric bounds | Limited | Likely timeout |

## Encoding Limitations

In addition to the solver's algorithmic limitations, the CHC backend has some
incomplete MIR encodings. Unsupported paths log warnings and either drop the
expression or fall back to a lossy type, so results may be incomplete or
imprecise for programs that rely on them.

| Feature | Current behavior | Impact |
|---------|------------------|--------|
| Ref/AddressOf rvalues | Partial at Reg level; full at Mem level | Simple refs work; projections need `--ay-chc-track=mem` |
| `Len` rvalues | Fixed-size arrays: compile-time constant | Slice length requires fat pointer metadata |
| `ShallowInitBox` | Translated to heap allocation (Phase 4) | Box allocation supported |
| `CopyForDeref` | Translated at Mem level | Use `--ay-chc-track=mem` for support |
| `NullaryOp` | Translated (RuntimeChecks variants) | UbChecks=false, ContractChecks=true, OverflowChecks=false |
| `Repeat` | Translated to `const_array` | Array initialization supported |
| `ThreadLocalRef` | Not translated (returns `None`) | Thread-local access unsupported |
| Unknown types | Fallback to `Sort::Int` | Rich types are collapsed to integers |

## Understanding the Limitation

### Why Constant Bounds Work

```rust
let mut i: u32 = 0;
while i < 100 {  // Constant bound
    i += 1;
}
assert!(i == 100);
```

**Result**: PASS in ~0.016s

The solver can enumerate frames up to the constant bound and reach a fixed point.

### Symbolic Bounds: Now Working for Common Patterns

Simple counting and accumulation loops with symbolic bounds now verify
successfully, thanks to ay-chc improvements (TIC — Template-directed
Inductive Checking, and enhanced invariant synthesis):

```rust
let n: u32 = kani::any();
kani::assume(n < 1_000_000);

let mut i: u32 = 0;
while i < n {  // Symbolic bound — now PROOF
    i += 1;
}
assert!(i == n);
```

**Result**: PROOF in the last recorded tier2 run (AY@a70a12da, 2026-03-20)

That run recorded 7/7 symbolic-bound harnesses as
PROOF (`tier2_unbounded` 5/5, `tier2_loop_for` 2/2). This covers counting
loops, accumulation, conditional accumulation, and for-range iteration with
symbolic bounds. Re-run the tier2 canaries after AY bumps before treating this
as the current pin's status.

### When Symbolic Bounds Still Struggle

Loops requiring **complex nonlinear invariants** (polynomial, factorial, GCD
with multiple induction variables) may still timeout. The limitation is in
invariant synthesis complexity, not in symbolic parameters themselves:

1. **Nonlinear arithmetic (NLA)**: Invariants like `i * (i+1) / 2` require NLA reasoning
2. **Multi-variable induction**: GCD-style loops with coupled variables are harder
3. **Nested symbolic loops**: Inner/outer loop interaction complicates invariant discovery

## Workarounds

### Use Constant Bounds When Possible

If your verification goal allows it, use concrete bounds:

```rust
// Instead of:
for i in 0..kani::any() { ... }

// Use:
for i in 0..100 { ... }
```

### Strengthen Loop Invariants

Add explicit assumptions that guide the solver:

```rust
let mut i: u32 = 0;
while i < n {
    kani::assume(i <= n);  // Help solver
    i += 1;
}
```

### Use the Bounded (BMC) Lane

BMC is the default lane, so for time-bounded verification simply omit `--ay-chc`:

```bash
trust-mc --unwind 100 your_file.rs
```

### Split Into Multiple Proofs

Partition the symbolic space into concrete ranges:

```rust
#[kani::proof]
fn verify_small_n() {
    let n: u32 = kani::any_where(|n| *n <= 100);
    // ... verification logic
}

#[kani::proof]
fn verify_medium_n() {
    let n: u32 = kani::any_where(|n| *n > 100 && *n <= 1000);
    // ... verification logic
}
```

## AY CHC Engine Portfolio

trust-mc's CHC backend uses AY's 11-engine portfolio solver (all run in parallel by default):

| Engine | Scope | Notes |
|--------|-------|-------|
| Decomposition | Multi-predicate | Splits complex problems into independent SCCs |
| PDR (default) | General | IC3-style engine, negated equality splits OFF |
| PDR (splits) | General | IC3-style engine, negated equality splits ON |
| BMC | Bounded | Bounded model checking fallback |
| PDKIND | K-induction | Handles bounded properties |
| IMC | Single-predicate, linear | Interpolation-based, limited scope |
| DAR | General | Dual approximation reachability |
| TPA | Transition Power Abstraction | Acceleration-based |
| CEGAR | General | Counterexample-guided abstraction refinement |
| TRL | Transition Relation Learning | Learning-based |
| Kind | K-induction variant | Alternative induction |

### IMC Engine Limitations

The IMC (Interpolation-based Model Checking) engine has specific scope restrictions:

- **Single-predicate only**: Multi-predicate CHC systems fall back to PDR
- **Linear-integer state**: Arrays and non-Int state sorts return `NotApplicable`
- **Soundness validation**: IMC validates interpolants via SMT before reporting results

When IMC cannot handle a problem, AY's portfolio automatically falls back to other engines. No user action is required, but verification may take longer.

### Iterator Soundness Diagnostics

When iterator verification encounters sort mismatches, the CHC backend emits explicit failure messages and forces verification to fail:

```
UNSOUND: IntoIterNext has non-datatype sort Sort(BitVec(...)) (hit #1) - forcing verification failure
```

This explicit failure is a soundness safeguard. When the iterator's sort doesn't match expected datatype structure, verification cannot proceed safely, so it fails explicitly rather than silently dropping constraints.

## Current Status

**The last recorded tier2 symbolic-bound run was green** (`7/7 PROOF` at
`AY@a70a12da`, 2026-03-20). That predates the AY pin now in `Cargo.toml`, so
it is not the current pin's status. Remaining enhancements tracked for complex
invariant patterns:

- **Abstract interpretation (CRAB)**: Generate candidate invariants via abstract domains (for NLA loops)
- **Loop acceleration**: Compute closed-form expressions for loop effects
- **Template-based interpolation**: Guide solver toward invariant shapes

See [Debugging slow proofs](./debugging-slow-proofs.md#loops-with-symbolic-bounds)
for user-facing guidance on the remaining timeout patterns.

## Related

- [Debugging slow proofs](./debugging-slow-proofs.md) for general slowness issues
- [Loop unwinding tutorial](./tutorial-loop-unwinding.md) for BMC-style loop handling
