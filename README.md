# trust-mc — a bit-precise software model checker for Rust

**Author:** Andrew Yates <andrewyates.name@gmail.com>
**Version:** 0.3.0
**License:** MIT OR Apache-2.0
**Copyright:** 2026 Andrew Yates

## What is trust-mc?

The **mc** is **model checking**: verifying a program against a specification by
exhaustively exploring its state space. Derived from
[Kani](https://github.com/model-checking/kani), trust-mc uses the
[AY](https://github.com/alabsystems/ay) SMT solver as its only verification
backend; there is no CBMC. Not fuzzing, not property testing — it proves the
assertion for **every** input of its type, or hands you one that breaks it.

```rust
fn add(a: u8, b: u8) -> u8 { a + b }

#[kani::proof]
fn add_never_overflows() {
    let a: u8 = kani::any();      // every u8, symbolically
    let b: u8 = kani::any();
    let _ = add(a, b);
}
```

```console
$ trust-mc bug.rs
Checking harness add_never_overflows...
Failed Checks: attempt to add with overflow
VERIFICATION:- FAILED                             # exit 1, bug.rs:15:5
```

`-Z concrete-playback --concrete-playback print` turns that counterexample into a
runnable `#[test]` carrying the values that broke it. Widen the return to `u16`
and state the bound, and the same command proves it for all 65,536 pairs:

```rust
fn add(a: u8, b: u8) -> u16 { a as u16 + b as u16 }

#[kani::proof]
fn add_never_overflows() {
    let a: u8 = kani::any();
    let b: u8 = kani::any();
    assert!(add(a, b) <= 510);
}
```

```console
$ trust-mc ok.rs
VERIFICATION:- SUCCESSFUL                         # exit 0
```

Simply removing the `+` is NOT a proof, and trust-mc says so rather than going
green: with nothing left to discharge, the harness reports
`INCONCLUSIVE (no checks)` and exits 1. Zero obligations is not zero bugs.

## How It Works

**trust-mc** takes Rust compiler MIR (Mid-level Intermediate Representation),
turns it into logical constraints, and asks the solver whether "bad states" are
reachable. Bounded model checking (BMC) is the default: loops are unrolled to a
fixed depth. `--ay-chc` is unbounded, proving loops by induction over
constrained Horn clauses (CHC) instead of unrolling them. The harness surface
stays Kani-compatible: `#[kani::proof]`, `kani::any()`, `kani::assume()`,
`kani::cover!`.

## Quick Start

With nothing else installed, the binary explains itself and hands you a harness:

```bash
cargo install --path .            # trust-mc, cargo-trust-mc, targo-trust-mc
trust-mc --help                   # commands, verify options, exit codes
trust-mc explain                  # how it works; `explain chc`, `explain results`, ...
trust-mc quickstart               # a five-minute walkthrough
trust-mc example --list           # sample harnesses that prove or fail as labelled
```

To verify, build the engine and its library sysroot once, and put the
[AY](https://github.com/alabsystems/ay) solver binary on `PATH`:

```bash
cargo run --release -p build-trust-mc -- build-dev --release
(cd ../ay && cargo build --release -p ay --features cli) && export PATH="$PWD/../ay/target/release:$PATH"

# Found automatically from inside the checkout; elsewhere, name the build:
export TRUST_MC_SYSROOT="$PWD/target/trust-mc"

trust-mc doctor                   # every piece, and the command that fixes a missing one
trust-mc example > demo.rs
trust-mc demo.rs                  # two harnesses, VERIFICATION:- SUCCESSFUL, exit 0
trust-mc example bug > bug.rs
trust-mc bug.rs                   # an overflow counterexample, exit 1
```

Everyday flags: `--harness NAME`, `--unwind N`, `--timeout 30s`, `--ay-chc`,
`--summary` (a sorted verdict table for the run), `--output-format terse`, `-v`.
Everything else is forwarded to the engine unchanged; `trust-mc flags` prints
that reference. Inside a Cargo package use `cargo trust-mc`
(`trust-mc explain cargo`).

## In CI

The exit code is the contract: **0** every selected harness verified, **1** a
harness failed or was inconclusive (or the engine errored), **2** usage error,
**3** not installed. Nothing else needs parsing.

```yaml
- run: cargo trust-mc --timeout 60s --sarif trust-mc.sarif
- uses: github/codeql-action/upload-sarif@v3
  if: always()
  with: { sarif_file: trust-mc.sarif }
```

Run from a workspace root this verifies every member and fails if any one of them
does; `-p <package>` narrows it to one crate. Artifacts stay under `target/`,
never beside your sources. Each finding carries a rule id, a level and its line
(`trust_mc.ay.overflow | error | src/lib.rs:15:5`), and a harness that fails
without any single property failing still leaves one — so an empty report means
an empty report. `trust-mc doctor --json` reports readiness as one object
(`ready`, `exit_code`, `engine`, `solver`, `warnings`, `fixes`) to gate a job on.

Runs are reproducible: the same source gives the same verdict and the same
counterexample every time, so a red build can be triaged from what it printed.

## What it will not do quietly

A verifier is only worth the failures it refuses to hide, so trust-mc fails
closed and says which case it hit:

- a proof that relied on an encoding approximation is **demoted**, not reported;
  one in a logic AY cannot validate reports `SUCCESSFUL (UNVALIDATED)`
- a harness whose every check is unreachable is `VACUOUS` when its assumptions
  are contradictory and `INCONCLUSIVE` when the checks sit on dead code, never
  `SUCCESSFUL`
- a harness that produced no obligations is `INCONCLUSIVE (no checks)`
- a solver that could not decide says so, and names `--ay-chc`
- an insufficient `--unwind` reports the unwinding assertion instead of passing

The vacuity and no-checks gates hold under `--ay-chc` exactly as under the
default bounded mode: one claim, both modes. `trust-mc explain soundness` is the
full account; `explain kani` lists the deliberate differences from Kani, whose
harness language this keeps.
