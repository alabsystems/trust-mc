# trust-mc — a bit-precise software model checker for Rust

**Author:** Andrew Yates <andrewyates.name@gmail.com>
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
quietly green. With nothing left to discharge the harness has no checks, and
what happens next depends on whether the compiler could CERTIFY that: when its
walk has seen every reachable statement and terminator and found no obligation
site, the harness exits 0 as it does under Kani — but visibly, as
`VERIFICATION:- SUCCESSFUL (no checks — compiler-certified obligation-free)`
with `[AY:VACUOUS:no-checks]` and a non-clean proof qualifier, never a bare
SUCCESSFUL. When it could not (a `kani::any()`, a body it cannot read), an
obligation may have been dropped, and the harness reports
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

`rust-toolchain.toml` pins the `trust` toolchain. Install
[aterm](https://github.com/alabsystems/aterm#install); atpkg installs Trust and
links it into rustup as `trust` (`aterm pkg install trust` does it by hand;
atpkg ships Trust for Apple-silicon macOS only; no other platform has a public
Trust package or supported install path today).

Build in an isolated tree with `trust-mc`, `ay`, and `trust-ir` as siblings.
Use detached worktrees for AY and TrustIR at the exact revisions in
`tools/tuple.toml`; the workspace path patches resolve `../ay` and `../trust-ir`.
Clean and trust-vc remain exact Git dependencies recorded in the tuple and
lockfile. The build gate checks the frozen tuple and never moves a sibling
checkout. See the maintained Trust route
for setup and provenance details.

With those checkouts prepared, the front door explains itself and provides
example harnesses:

```bash
targo --unverified install --path . # trust-mc, cargo-trust-mc, targo-trust-mc
trust-mc --help                   # commands, verify options, exit codes
trust-mc explain                  # how it works; `explain chc`, `explain results`, ...
trust-mc quickstart               # a five-minute walkthrough
trust-mc example --list           # sample harnesses that prove or fail as labelled
```

Package managers can place the front door and engine together in a bundle's
`bin/` directory, with its `lib/`, `no_core/`, and `playback/` trees beside that
directory. `trust-mc` finds this bundle through its executable path, including
when launched through a package-manager symlink from outside a checkout. An
explicit `TRUST_MC_SYSROOT` still takes priority.

The front door reads the engine's AY runtime choice once from
`--version-authority`: new release engines select their private `libexec/ay`
relative to the actual driver, including through a package-manager symlink.
They require no global AY on PATH. `TRUST_MC_AY_BIN` remains an explicit override;
the driver still validates the selected solver. Older engines without the
`ay_runtime_default` field retain legacy PATH discovery. For an older private-AY
bundle, select its matching helper explicitly with `TRUST_MC_AY_BIN`, or rebuild
the bundle to obtain automatic discovery.

To verify your Rust programs, build the engine backend and its keyed Kani
library with the exact Trust seal recorded in [tools/tuple.toml](tools/tuple.toml). The compiler API
port has landed; this route uses the seal's `rustc-dev` libraries and the
library sources of the seal's own commit: its `trust-src` component, or, for a
seal that ships none (9192), a trust checkout holding that commit.
`TRUST_PRIVATE_SYSROOTS` normally stays unset; its
optional overlay only accepts a matching compiler driver. The development
sysroot (`targo --unverified build-dev`) takes the same sources, in this order:
`--trust-checkout <trust checkout>` (given before any cargo argument), then
`TRUST_MC_TRUST_CHECKOUT`, then the seal's own, then the trust superproject of
a `first-party/trust-mc` checkout. The frozen nightly in
`rust-toolchain.legacy.toml` builds nothing; it records the stock toolchain of
the Kani-comparison baseline, a stock-as-oracle kept by the owner's ruling of 2026-09-29.

**Trust verification of trust-mc itself is enabled but does not pass yet.**
The blanket compiler and rustdoc off-switches are removed. The manifest
selects hardened L2 verification; the full gate below additionally requires
certification and verification of dependencies, including host compiler units. Its
scope is the workspace's default features and targets:

```bash
export TRUST_MC_TRUST_TOOLCHAIN="$HOME/Library/Application Support/aterm/pkg/store/trust/9192"
scripts/check-trust-verification.sh --build
```

On seal 9192 (re-measured 2026-09-28, exit 2), as on 8595, this fails closed at
the procedural-macro boundary (`serde_derive`). Smaller diagnostic runs also leave unresolved obligations.
See the measured verification status
for exact scope, source fixes and remaining work. Saved reports are diagnostic
records; only the live authenticated gate carries verification authority.
Development commands below explicitly select `--unverified`.

The `ay` binary must be the AY commit this workspace pins — the `rev` of `ay`
in `Cargo.toml`'s `[workspace.dependencies]`. The engine runs `$TRUST_MC_AY_BIN`
when it is set and `ay` on `PATH` otherwise, reads the commit from
`ay --version`, and refuses any other build: bounded verdicts, cover checks and
the external CHC fallback all come from that binary, so an off-pin one produces
verdicts nobody can attribute. `trust-mc doctor` reports an off-pin binary as
not ready and prints the fix. `--allow-unpinned-ay` (or
`TRUST_MC_ALLOW_UNPINNED_AY=1`) runs one anyway: every harness then prints
`[AY:SOLVER_PIN_MISMATCH:found=…:pin=…]`, and no success is reported as more
than `SUCCESSFUL (UNVALIDATED)`.

```bash
# Use the numbered seal matching tools/tuple.toml (9192 in this example).
S="$HOME/Library/Application Support/aterm/pkg/store/trust/9192"
export TRUST_MC_TRUST_TOOLCHAIN="$S"
scripts/check-trust-lane-build.sh  # explicit unverified build; jobs sized to the host

# 9192 ships no trust-src component: name a trust checkout at the commit
# `"$S/bin/trustc" -vV` reports. A seal that ships one takes --trust-src.
target/debug/build-trust-mc build-keyed --trustc "$S/bin/trustc" \
  --trust-checkout <trust checkout> --std build-std \
  --backend target/debug/librustc_codegen_trust_mc.dylib
export TRUST_MC_AY_BIN="$(scripts/build-pinned-ay-cli.sh)"

# Derive the library path from the same compiler's identity.
export TRUST_MC_SYSROOT="$(target/debug/build-trust-mc build-keyed \
  --trustc "$S/bin/trustc" --print-key | tail -n 1)"

target/debug/trust-mc example > demo.rs
target/debug/trust-mc-driver demo.rs --compiler-route trustc --trustc "$S/bin/trustc" \
  --backend-dylib "$TRUST_MC_SYSROOT/codegen-backends/librustc_codegen_trust_mc.dylib"
```

`scripts/trust-lane-smoke.sh` exercises successful and failing harnesses in both
BMC and CHC modes, plus compiler-route refusal cases, against these artifacts.

Everyday flags: `--harness NAME`, `--unwind N`, `--timeout 30s`, `--ay-chc`,
`--summary` (a sorted verdict table for the run), `--output-format terse`, `-v`.
Everything else is forwarded to the engine unchanged; `trust-mc flags` prints
that reference. Inside a Cargo package use `targo trust-mc` with the Trust
toolchain, or `cargo trust-mc` with stock Rust (`trust-mc explain cargo`).

## In CI

The exit code is the contract: **0** every selected harness verified, **1** a
harness failed or was inconclusive (or the engine errored), **2** usage error,
**3** not installed. Nothing else needs parsing.

```yaml
- run: targo trust-mc --timeout 60s --sarif trust-mc.sarif   # stock Rust: cargo trust-mc ...
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
- a harness that produced no obligations is `INCONCLUSIVE (no checks)` unless
  the compiler certified it obligation-free, and then it is
  `SUCCESSFUL (no checks — compiler-certified obligation-free)`: exit 0, but
  never a clean proof
- a solver that could not decide says so, and names `--ay-chc`
- a harness that reached no verdict prints exactly one
  `[AY:UNKNOWN_REASON:<why>]` — `Timeout`, `BudgetExhausted` (its own deadline
  was spent before the deciding stage could start), `DriverTimeout` /
  `CompileTimeout` (the process watchdog fired), `SolverError`, ... — and every
  stage that was forfeited to stay inside that deadline says so with
  `[AY:STAGE_SKIPPED:<stage>:BudgetExhausted]`; `trust-mc explain output`
  lists them
- an insufficient `--unwind` reports the unwinding assertion instead of passing

The vacuity and no-checks gates hold under `--ay-chc` exactly as under the
default bounded mode: one claim, both modes. `trust-mc explain soundness` is the
full account; `explain kani` lists the deliberate differences from Kani, whose
harness language this keeps.
