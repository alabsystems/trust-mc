# Usage on a single file

`trust-mc` verifies one Rust source file with no project, no configuration and
no Cargo. This page is a worked session; `trust-mc quickstart` prints the same
walkthrough from the binary, and `trust-mc explain` covers the concepts.

## Check the installation

```
$ trust-mc doctor
trust-mc 0.3.0 (aarch64-apple-darwin)

verification engine
  [ ] $TRUST_MC_SYSROOT is not set  (TRUST_MC_SYSROOT)
  [x] /work/trust-mc/target/trust-mc/bin/trust-mc-driver  (local build)
  [ ] /home/me/.kani/kani-0.3.0/bin/trust-mc-driver  (release bundle)
  using: /work/trust-mc/target/trust-mc/bin/trust-mc-driver (local build)
  [x] trust-mc-compiler beside it
  [x] engine reports: trust-mc 0.3.0
  [x] linked AY 0.13.0 @ 5bd746693491 (the pinned commit)

library sysroot  /work/trust-mc/target/trust-mc
  [x] lib           verification (std + kani crate compiled for proofs)
  [x] no_core/lib   verify-std
  [x] playback/lib  concrete playback

rust toolchain (the compiler is a rustc driver)
  [x] trust-mc-compiler starts: rustc 1.93.0-nightly (646a3f8c1 2025-12-02)

SMT solver (bounded runs shell out to it; CHC solves in-process)
  [x] ay  /work/ay/target/release/ay
      ay 0.13.0+build.8212.5bd74669349190eae57027c91c0430b4980046ac@...
  [x] the binary is the same AY commit the engine links

ready. Try:

    trust-mc example > demo.rs
    trust-mc demo.rs
```

When something is missing, `doctor` exits 3 and prints the command that
produces it (`cargo run --release -p build-trust-mc -- build-dev --release` for
the engine and sysroot; a sibling `ay` checkout built with
`cargo build --release -p ay --features cli` for the solver).

## Run a harness

```
$ trust-mc example > demo.rs
$ trust-mc demo.rs
trust_mc Rust Verifier 0.3.0 (standalone)
[AY:CODEGEN_COMPLETE:harnesses=2]
Checking harness double_never_shrinks...
[AY:PROOF_QUALIFIERS:clean]

RESULTS:
Check 1: double_never_shrinks.assertion.1
	 - Status: SUCCESS
	 - Description: "assertion failed: double(x) >= x"
	 - Location: ... in function double_never_shrinks

SUMMARY:
 ** 0 of 1 failed

VERIFICATION:- SUCCESSFUL
Verification Time: 0.1s
...
Manual Harness Summary:
Complete - 2 successfully verified harnesses, 0 failures, 2 total.
```

`kani::any()` gives a symbolic value, so each assertion is proved for every
input of its type. `[AY:PROOF_QUALIFIERS:clean]` is the strongest result: a
proof with no encoding fallback.

## See a failure

```
$ trust-mc example bug > bug.rs
$ trust-mc bug.rs
...
Checking harness add_never_overflows...
[AY:CTREX_CAT:Genuine]

RESULTS:
Check 1: add_never_overflows.overflow.1
	 - Status: FAILURE
	 - Description: "attempt to add with overflow"
	 - Location: bug.rs:15:5 in function add_never_overflows

SUMMARY:
 ** 1 of 1 failed
Failed Checks: attempt to add with overflow

VERIFICATION:- FAILED
...
$ echo $?
1
```

`[AY:CTREX_CAT:Genuine]` says the counterexample is real — not an artefact of
an encoding fallback. `trust-mc explain results` lists every status, verdict
and marker. The other examples (`trust-mc example --list`) show an index out
of bounds in safe code, a raw-pointer read past the end, a precondition stated
with `kani::assume`, `kani::cover!`, and a loop with an unwind bound.

## Write your own

```rust
fn clamp_to_byte(x: u32) -> u8 {
    if x > 255 { 255 } else { x as u8 }
}

#[kani::proof]
fn clamp_never_exceeds_input() {
    let x: u32 = kani::any();            // every u32
    kani::assume(x != 0);                // preconditions, if any
    let y = clamp_to_byte(x);            // the code under verification
    kani::cover!(y == 255, "saturates"); // is this branch reachable?
    assert!(u32::from(y) <= x);          // what must hold
}
```

A single file needs no `#[cfg(kani)]` guard and no `extern crate`; the `kani`
crate is in scope. Loops are unrolled to a bound — `#[kani::unwind(N)]` on the
harness or `--unwind N` on the command line; the bound you need is the maximum
number of iterations plus one, and an input that needs more fails the
unwinding assertion (`trust-mc explain bmc`). To prove a loop for every
iteration count, run with `--ay-chc` (`trust-mc explain chc`).

## Everyday commands

```
trust-mc --list file.rs                  which harnesses are there
trust-mc --harness NAME file.rs          just one (substring match)
trust-mc --unwind 8 file.rs              raise the loop bound
trust-mc --timeout 60s file.rs           cap each harness's solve
trust-mc --ay-chc file.rs                unbounded mode
trust-mc --output-format terse file.rs   verdicts only
trust-mc --summary file.rs               a sorted verdict table for the run
trust-mc -v file.rs                      every stage and the engine command
trust-mc flags                           the engine's full flag reference
```

Exit status: 0 verified, 1 a harness failed or was inconclusive (or the
engine errored), 2 usage error, 3 engine/sysroot/solver not installed
(`trust-mc explain exit-codes`).
For a Cargo package, use `cargo trust-mc` ([Usage on a package](./cargo-trust-mc.md)).
