# Using trust-mc

At present, trust-mc can used in two ways:

 * [On a single crate](#usage-on-a-single-crate) with the `trust-mc` command.
 * [On a Cargo package](#usage-on-a-package) with the `targo trust-mc` command.

If you plan to integrate trust-mc in your projects, the recommended approach is to use `targo trust-mc`.
This will handle dependencies automatically, and it can be configured (if needed) in `Cargo.toml`.
But `trust-mc` is useful for small examples/tests.

> **Back-compat:** `targo trust-mc` remains a working alias for `targo trust-mc`
> — the tool ships both a `targo-trust-mc` and a `cargo-trust-mc` proxy, so every
> existing script and command line keeps working. New docs use the Trust-native
> `targo trust-mc` spelling.

## Usage on a package

trust-mc is integrated with `targo` and can be invoked from a package as follows:

```bash
targo trust-mc [OPTIONS]
```

This works like `targo test` except that it will analyze all proof harnesses instead of running all test harnesses.
The proof source surface is Kani-compatible: keep using `#[kani::proof]`,
`#[kani::proof_for_contract]`, `kani::any()`, and `kani::assume()`. The
execution path is trust-mc through AY; there is no Rust execution fallback that can
turn a harness into replacement evidence.

## Common command line flags

Common to both `trust-mc` and `targo trust-mc` are many command-line flags:

 * `--concrete-playback=[print|inplace]`: _Experimental_ feature that generates a Rust unit test case
 that plays back a failing proof harness using a concrete counterexample.
 If used with `print`, trust-mc will only print the unit test to stdout.
 If used with `inplace`, trust-mc will automatically add the unit test to the user's source code, next to the proof harness. For more detailed instructions, see the [concrete playback](./reference/experimental/concrete-playback.md) section.

 * `--tests`: Build in "[test mode](https://doc.rust-lang.org/rustc/tests/index.html)", i.e. with `cfg(test)` set and `dev-dependencies` available (when using `targo trust-mc`).

 * `--harness <name>`: By default, trust-mc checks all proof harnesses it finds.
   You can switch to checking a single harness using this flag.

 * `--harnesses`: List contracts and proof harnesses using the default terminal
   table, then exit. This is a shortcut for the pretty form of the `list`
   subcommand: use `targo trust-mc list --format json` or
   `targo trust-mc list --format markdown` for machine-readable or file-oriented
   listing output.

 * `--backend=<auto|ay>`: Select the verification backend. `auto` (default) resolves
   to the AY backend. Use `--backend=ay` to force the AY backend explicitly.

 * `--proof-summary-json <path>`: After verification, write an informational
   JSON summary of the harness results. This artifact is for CLI-facing review
   and triage. It is not replacement-audit evidence and does not run the
   replacement proof gate; use the flow in `replacement-proof.md` (repository
   root) for that.

   For repository-level replacement accounting, use the Rust progress reporter:
   `cargo run --manifest-path tools/replacement-audit/Cargo.toml --bin replacement-progress --`.
   Use `--require-complete --report <proof-report>` when the command should
   fail unless the supplied evidence reaches the 100% Kani replacement gate.
   It complements the strict replacement audit; it does not weaken the
   authority tuple requirements.

 * `--version-authority`: Print one machine-readable evidence line containing
   the trust-mc version, trust-mc git SHA and dirty flag, AY package version,
   declared AY pin, linked AY build revision, and the `ay_authority` lane that
   relation was established in, then exit. The lane is read out of `Cargo.lock`,
   not asserted: `matched` when the lock resolves AY from the pinned git
   revision, in which case the linked build must equal the pin exactly;
   `contains-pin` when the root manifest `[patch]`es AY to a sibling checkout and
   Cargo accepted that patch, in which case the linked build must contain the
   declared pin. The command fails closed without printing an authority row when
   the AY inventory is malformed, the linked build is dirty, the linked build
   does not satisfy its lane's relation, or the manifest declares an AY `[patch]`
   that Cargo silently declined.

 * `--default-unwind <n>`: Set a default global upper [loop unwinding](./tutorial-loop-unwinding.md) bound for proof harnesses.
   This can force termination when the solver tries to unwind loops indefinitely.

## AY Backend Options

The AY backend is trust-mc's default verification backend. These options configure AY behavior:

 * `--ay-solver=<solver>` (or `--smt-solver=<solver>`): Select the underlying SMT solver.
   Available choices: `auto` (default), `ay`. The `auto` setting uses the native
   `ay-chc` solver.

   AY is the only supported verification backend. A proof result is produced by
   the AY path, not by rerunning the harness as Rust or falling back to another
   solver family.

 * `--ay-chc`: Enable Constrained Horn Clause (CHC) mode for unbounded verification.
   Use this for proofs that require induction over unbounded loops. CHC mode uses the
   PDR/IC3 algorithm to find inductive invariants.

 * `--ay-chc-track=<level>`: Control memory tracking in CHC mode.
   | Level | Description | Use Case |
   |-------|-------------|----------|
   | `reg` | Register-only (default) | Pure computation without pointer reasoning |
   | `ptr` | Pointer validity tracking | Bounds/OOB checking without full memory |
   | `mem` | Full memory tracking | Complete pointer verification |

   Example: `trust-mc --ay-chc --ay-chc-track=mem your_file.rs`

 * `--ay-wide-mem` (alias: `--wide-mem`): Enable the wide memory model for additional heap
   bounds checks (`is_dereferenceable`). Requires `--ay-chc` and is most effective with
   `--ay-chc-track=mem`.

For more details on CHC solver configuration, see [CHC Solver Paths](./chc-solver-paths.md).
For debugging slow proofs with solver selection, see [Debugging Slow Proofs](./debugging-slow-proofs.md).

Run `targo trust-mc --help` to see a complete list of arguments.

## Usage on a single crate

For small examples or initial learning, it's very common to run trust-mc on just one source file.
The command line format for invoking trust-mc directly is the following:

```
trust-mc filename.rs [OPTIONS]
```

This will build `filename.rs` and run all proof harnesses found within.

The `trust-mc` binary documents itself, and everything below works with nothing
else installed:

```
trust-mc --help                 commands, verify options, exit codes
trust-mc explain [TOPIC]        how it works: harness, bmc, chc, results,
                                soundness, cargo, kani, flags, install, exit-codes
trust-mc quickstart             a five-minute walkthrough
trust-mc example [NAME] [PATH]  sample harnesses (--list shows them); each
                                says what it proves or which bug it finds
trust-mc doctor                 what verification needs and whether it is here
trust-mc flags [--all]          the engine's complete flag reference
trust-mc version -v             engine and solver provenance
```

Front-door flags `--harness`, `--unwind`, `--timeout`, `--list` and `--solver`
are translated onto the engine's flags, and `--summary` is handled by the front
door itself (the engine never sees it); every other flag is forwarded unchanged.
See [Usage on a single file](./trust-mc-single-file.md) for a worked session.

## Configuration in `Cargo.toml`

Users can add a default configuration to the `Cargo.toml` file for running harnesses in a package.
trust-mc extracts arguments from these tables (later tables override earlier):

 * `[workspace.metadata.kani]` - workspace-wide defaults
 * `[package.metadata.kani]` - package-specific (overrides workspace)
 * `[kani]` - top-level shorthand (highest precedence)

Each table supports two subtables:

### flags

Regular CLI flags as key-value pairs:

```toml
[package.metadata.kani.flags]
default-unwind = "1"
harness = ["check_foo", "check_bar"]
```

### unstable

Unstable features (maps to `-Z` flags):

```toml
[package.metadata.kani.unstable]
function-contracts = true
stubbing = true
```

Example complete configuration:

```toml
[package.metadata.kani]
flags = { default-unwind = "2" }
unstable = { function-contracts = true }
```

The options here are the same as on the command line (`targo trust-mc --help`), and flags (that is, command line arguments that don't take a value) are enabled by setting them to `true`.

Starting with Rust 1.80 (or nightly-2024-05-05), every reachable #[cfg] will be automatically checked that they match the expected config names and values.
To avoid warnings on `cfg(kani)`, we recommend adding the `check-cfg` lint config in your crate's `Cargo.toml` as follows:

```toml
[lints.rust]
unexpected_cfgs = { level = "warn", check-cfg = ['cfg(kani)'] }
```

For more information please consult this [blog post](https://blog.rust-lang.org/2024/05/06/check-cfg.html).

## The build process

When trust-mc builds your code, it does three important things:

1. It sets `cfg(kani)` for target crate compilation (including dependencies).
2. It injects the `kani` crate.
3. It sets `cfg(kani_host)` for host build targets such as any build script and procedural macro crates.

A proof harness (which you can [learn more about in the tutorial](./trust-mc-tutorial.md)), is a function annotated with `#[kani::proof]` much like a test is annotated with `#[test]`.
But you may experience a similar problem using trust-mc as you would with `dev-dependencies`: if you try writing `#[kani::proof]` directly in your code, `cargo build` will fail because it doesn't know what the `kani` crate is.

This is why we recommend the same conventions as are used when writing tests in Rust: wrap your proof harnesses in `cfg(kani)` conditional compilation:

```rust
#[cfg(kani)]
mod verification {
    use super::*;

    #[kani::proof]
    pub fn check_something() {
        // ....
    }
}
```

This will ensure that a normal build of your code will be completely unaffected by anything trust-mc-related.

This conditional compilation with `cfg(kani)` (as seen above) is still required for trust-mc proofs placed under `tests/`.
When this code is built by `cargo test`, the `kani` crate is not available, and so it would otherwise cause build failures.
(Whereas the use of `dev-dependencies` under `tests/` does not need to be gated with `cfg(test)` since that code is already only built when testing.)

## Using dev-dependencies in library proofs

A proof harness that lives inside your library target (`src/`) and imports a
`[dev-dependencies]` crate — typically as an *oracle* for cross-validating a
hand-rolled implementation against a reference crate — needs both a stricter
`cfg` gate **and** the `--tests` flag:

```toml
# Cargo.toml
[dev-dependencies]
unicode-width = "0.2"  # oracle for a hand-rolled width table
```

```rust
// src/verification.rs
#[cfg(all(kani, test))] // NOTE: `test` is required in addition to `kani`
mod verification {
    use unicode_width::UnicodeWidthChar;

    #[kani::proof]
    fn width_matches_reference() {
        let c: char = kani::any();
        kani::assume(c.is_ascii());
        assert_eq!(
            crate::my_width(c),
            c.width().unwrap_or(0),
        );
    }
}
```

Then invoke trust-mc with `--tests`:

```bash
targo trust-mc --tests
```

**Why is this necessary?** Cargo only resolves `[dev-dependencies]` when at
least one test, bench, or example target is in the build graph. `targo trust-mc`
without `--tests` builds the library alone (`cargo rustc --lib`), which does
not pull in dev-deps — so `use unicode_width::...` fails with
`error[E0432]: unresolved import unicode_width` even though the crate is
listed in `Cargo.toml`. Gating the proof with `cfg(all(kani, test))` and
passing `--tests` puts the library on the same resolution path as
`cargo test`, which does resolve dev-deps.

If trust-mc sees an `unresolved import` error for a crate that matches one of your
`[dev-dependencies]`, it will print a hint pointing back to this section. See
upstream Kani issue [#1258] for the underlying cargo behavior.

[#1258]: https://github.com/model-checking/kani/issues/1258

## Rust Analyzer Setup

If you are using Rust Analyzer (e.g. in VS Code), we recommend using the following setup to allow Rust Analyzer to analyze trust-mc-specific code (e.g. trust-mc annotations, APIs, etc.) and get proper code completion and error:

1. Add the following to your package's `Cargo.toml`:
```toml
[target.'cfg(kani_ra)'.dependencies]
kani = { git = "https://github.com/alabsystems/trust-mc" }
```

This adds the kani dependency as a dependency that is conditional on `kani_ra`.

2. Add the following to your Rust Analyzer configuration file (e.g. `settings.json` for VS Code):
```
    "rust-analyzer.cargo.extraEnv": {
        "RUSTFLAGS": "--cfg kani_ra --cfg kani",
        "RUSTUP_TOOLCHAIN": "nightly"
    },
```
Explanation:
- Enabling the `kani_ra` configuration allows Rust Analyzer to see the kani definitions in the crate added in the `Cargo.toml` file.
- Enabling the `kani` configuration enables blocks guarded by `#[cfg(kani)]`.
- Finally, using the nightly toolchain is necessary for Rust Analyzer to be able to handle the code in the kani dependency, many of which requires nightly features.
