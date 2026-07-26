# trust-mc — Software Model Checker for Rust (Model Checking)

**Author:** Andrew Yates <andrewyates.name@gmail.com>
**Version:** 0.67.0
**License:** MIT OR Apache-2.0
**Copyright:** 2026 Andrew Yates

## What is trust-mc?

**trust-mc** is a bit-precise software model checker for Rust. The **mc** suffix stands for **Model Checking**, the process of exhaustively verifying whether a system meets a given specification by exploring its state space.

Derived from Kani, trust-mc uses the [AY](https://github.com/alabsystems/ay) SMT solver as its primary verification backend.

## How It Works

**trust-mc** takes Rust compiler MIR (Mid-level Intermediate Representation), transforms it into logical constraints, and asks the solver whether "bad states" are reachable.

- **Bounded Model Checking (BMC):** Unrolls loops to a fixed depth to find bugs.
- **Constrained Horn Clauses (CHC):** Uses inductive reasoning to prove unbounded properties.

The harness surface stays Kani-compatible: keep using `#[kani::proof]`, `kani::any()`, and `kani::assume()`.

## Quick Start

```bash
cargo build
cargo install --path .
```
