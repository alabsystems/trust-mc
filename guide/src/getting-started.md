# Getting started

trust-mc is a verification tool that uses [model checking](./tool-comparison.md) to analyze Rust programs.
trust-mc is derived from [Kani](https://github.com/model-checking/kani) and keeps the `kani::` proof API, while using the [AY backend](https://github.com/alabsystems/ay) exclusively for verification. AY is trust-mc's sole solver, powering CHC unbounded verification and the Phase 5 (beyond-CBMC) workstream.

trust-mc is useful for checking both safety and correctness of Rust code.
- *Safety*: trust-mc automatically checks for many kinds of [undefined behavior](./undefined-behaviour.md).
This makes it particularly useful for verifying unsafe code blocks in Rust, where the "[unsafe superpowers](https://doc.rust-lang.org/stable/book/ch19-01-unsafe-rust.html#unsafe-superpowers)" are unchecked by the compiler.
- *Correctness*: trust-mc automatically checks panics (e.g. `unwrap()` on `None`), arithmetic overflows, and custom correctness properties, either in the form of assertions (`assert!(...)`) or [function contracts](./reference/experimental/contracts.md).

Since trust-mc uses model checking, trust-mc will either prove the property, disprove the property (with a counterexample), or may run out of resources.

trust-mc uses proof harnesses to analyze programs.
Proof harnesses are similar to test harnesses, especially property-based test harnesses.

## Project Status

trust-mc is currently under active development.
The AY backend targets code that CBMC cannot handle, including:
- Arbitrary-precision integers (BigInt) - Phase 5 capability under active validation
- HashMap-heavy data structures - Phase 5 capability with stale historical evidence; replacement-quality evidence still requires the authority tuple and gates in the replacement proof standard
- Complex theory solver code - active CHC workstream

Note: trust-mc currently uses `kani::` macros (e.g., `#[kani::proof]`). These will be renamed to `trust-mc::` in a future release.

There is support for a fair amount of Rust language features, but not all (e.g., concurrency).
Please see [Limitations](./limitations.md) for a detailed list of supported features.

If you encounter issues when using trust-mc, we encourage you to [report them to us](https://github.com/alabsystems/trust-mc/issues/new).
