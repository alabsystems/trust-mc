// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `trust-mc explain [TOPIC]`: how the tool works, from inside the tool.
//!
//! Every statement below describes the engine as it is in this tree. The
//! facts ledger — where each claim comes from, so a reader can re-check it
//! after a change — is this list:
//!
//! * pipeline, BMC/CHC selection, unwind resolution (`--unwind` >
//!   `#[kani::unwind]` > `--default-unwind` > 1), unwinding assertions:
//!   `trust-mc-compiler/src/codegen_ay/compiler_interface.rs` (`codegen_crate`),
//!   `codegen_ay/codegen_function.rs`, `codegen_ay/loop_unroll/`;
//!   `trust-mc-core/src/{bmc,chc}.rs`.
//! * which path needs the `ay` binary (BMC subprocess, CHC in-process, the
//!   session gate): `trust-mc-driver/src/call_ay.rs`, `call_ay/chc/native.rs`,
//!   `args/solver.rs` (`Backend::resolve`), `session/mod.rs`.
//! * verdict words, check statuses, markers, warnings:
//!   `trust-mc-driver/src/verification_result.rs`, `result_summary.rs`,
//!   `harness_runner.rs`, `verification_provenance.rs`, `unsoundness_counts.rs`,
//!   `demotion.rs`, `ctrex_classify.rs`, `main.rs` (`report_*_warnings`).
//! * soundness classes and what is / is not checked: `soundness.md` (repo
//!   root), `trust-mc-core/src/violation.rs`, `guide/src/undefined-behaviour.md`.
//! * library surface: `library/trust-mc/src/lib.rs`, `library/kani_core/src/`,
//!   `library/kani_macros/src/lib.rs`, `library/std/src/lib.rs` (assert shim).
//! * flags: `trust-mc-driver/src/args/*.rs`; `kani-cli-parity.md`.
//! * install and discovery: `tools/build-trust-mc/src/`, `src/setup.rs`,
//!   `trust-mc-driver/src/session/install.rs`, and `super::engine`.

use std::ffi::OsString;
use std::process::ExitCode;

use super::{Fail, Front, VERSION, closest};

pub(crate) struct Topic {
    pub(crate) name: &'static str,
    pub(crate) aliases: &'static [&'static str],
    pub(crate) title: &'static str,
    pub(crate) body: &'static str,
}

pub(crate) const TOPICS: &[Topic] = &[
    Topic {
        name: "harness",
        aliases: &["harnesses", "proof", "api", "library"],
        title: "writing harnesses: kani::any, assume, assert, cover, attributes",
        body: HARNESS,
    },
    Topic {
        name: "bmc",
        aliases: &["bounded", "unwind", "unwinding", "loops"],
        title: "bounded model checking (default), --unwind, unwinding checks",
        body: BMC,
    },
    Topic {
        name: "chc",
        aliases: &["unbounded", "pdr", "horn", "invariants"],
        title: "unbounded proofs with --ay-chc (inductive invariants / PDR)",
        body: CHC,
    },
    Topic {
        name: "results",
        aliases: &["output", "verdicts", "verdict", "markers", "reading"],
        title: "reading the output: statuses, verdicts, [AY:...] markers",
        body: RESULTS,
    },
    Topic {
        name: "soundness",
        aliases: &["sound", "unsound", "checks", "trust"],
        title: "what a PROOF means, what is checked, what fails closed",
        body: SOUNDNESS,
    },
    Topic {
        name: "cargo",
        aliases: &["package", "cargo-trust-mc", "targo"],
        title: "verifying a Cargo package with `cargo trust-mc`",
        body: CARGO,
    },
    Topic {
        name: "kani",
        aliases: &["compat", "compatibility", "migrating", "differences"],
        title: "compatibility with Kani, and the deliberate differences",
        body: KANI,
    },
    Topic {
        name: "flags",
        aliases: &["options", "engine"],
        title: "the engine's flag families and how to see them all",
        body: FLAGS,
    },
    Topic {
        name: "install",
        aliases: &["installation", "setup-guide", "sysroot", "discovery", "build"],
        title: "engine, sysroot, solver: where they live, how they are found",
        body: INSTALL,
    },
    Topic {
        name: "exit-codes",
        aliases: &["exit", "exit-status", "status"],
        title: "the exit status contract",
        body: EXIT_CODES,
    },
    Topic {
        name: "limits",
        aliases: &["limitations", "known-limits", "unsupported"],
        title: "what does not verify yet, and how to tell that from a real bug",
        body: LIMITS,
    },
    Topic {
        name: "quickstart",
        aliases: &["guide", "tutorial", "start", "getting-started"],
        title: "a five-minute walkthrough (also `trust-mc quickstart`)",
        body: QUICKSTART,
    },
];

pub(crate) fn names() -> impl Iterator<Item = &'static str> {
    TOPICS.iter().map(|t| t.name)
}

pub(crate) fn find(name: &str) -> Option<&'static Topic> {
    let name = name.to_ascii_lowercase();
    TOPICS.iter().find(|t| t.name == name || t.aliases.contains(&name.as_str()))
}

/// The rendered page for `name` (a topic name or alias, or `overview`).
pub(crate) fn render(name: &str) -> Option<String> {
    if matches!(name, "overview" | "pipeline" | "how" | "how-it-works") {
        return Some(overview());
    }
    find(name).map(|t| format!("{}\n{}\n{}", t.title_line(), t.body, footer(t)))
}

impl Topic {
    fn title_line(&self) -> String {
        let heading = format!("trust-mc explain {}", self.name);
        format!("{heading}\n{}\n", "=".repeat(heading.len()))
    }
}

fn footer(t: &Topic) -> String {
    let mut out = String::from("See also: trust-mc explain {");
    let mut col = out.len();
    let others: Vec<&str> = TOPICS.iter().map(|o| o.name).filter(|n| *n != t.name).collect();
    for (i, other) in others.iter().enumerate() {
        let last = i + 1 == others.len();
        let item = if last { format!("{other}}}") } else { format!("{other},") };
        if col + item.len() + 1 > 80 {
            out.push_str("\n          ");
            col = 10;
        } else if i > 0 {
            out.push(' ');
            col += 1;
        }
        out.push_str(&item);
        col += item.len();
    }
    out.push('\n');
    out
}

/// The lines listing every topic, used by the overview and the help pages.
pub(crate) fn list_lines() -> String {
    let mut out = String::from("Topics (trust-mc explain <TOPIC>):\n");
    for t in TOPICS {
        out.push_str(&format!("    {:<12} {}\n", t.name, t.title));
    }
    out
}

/// `trust-mc explain [TOPIC]`.
pub(crate) fn command(rest: &[OsString]) -> Front<ExitCode> {
    let mut subject: Option<String> = None;
    for arg in rest {
        let text = arg.to_string_lossy();
        if text.starts_with('-') {
            return Err(Fail::usage(format!(
                "error: `explain` takes a topic name, not {text}\n\n{}",
                list_lines()
            )));
        }
        if subject.is_some() {
            return Err(Fail::usage(format!(
                "error: `explain` takes one topic at a time\n\n{}",
                list_lines()
            )));
        }
        subject = Some(text.into_owned());
    }
    match subject {
        None => {
            print!("{}", overview());
            Ok(ExitCode::SUCCESS)
        }
        Some(name) => match render(&name) {
            Some(page) => {
                print!("{page}");
                Ok(ExitCode::SUCCESS)
            }
            None => {
                let mut msg = format!("error: no topic named `{name}`\n");
                if let Some(near) = closest(&name, names()) {
                    msg.push_str(&format!("       did you mean `trust-mc explain {near}`?\n"));
                }
                msg.push('\n');
                msg.push_str(&list_lines());
                Err(Fail::usage(msg))
            }
        },
    }
}

pub(crate) fn overview() -> String {
    format!(
        "How trust-mc works (trust-mc {VERSION})
=========================================

trust-mc is a model checker for Rust. You write a proof harness — a function
marked #[kani::proof] — that builds inputs with kani::any(), calls your code,
and states what must hold with assert!. trust-mc then proves the assertions
for EVERY input the harness allows, or names a check that fails and where.
(To get the offending input values as a runnable unit test, add
-Z concrete-playback --concrete-playback print.)

What happens on `trust-mc file.rs`:

  1. compile   trust-mc-compiler (a rustc driver) compiles file.rs with the
               `kani` crate in scope and collects every #[kani::proof].
  2. encode    for each harness, the MIR of everything it reaches becomes a
               verification condition: a formula over fixed-width bit-vectors
               in which \"some check fails\" is reachable exactly when the
               formula is satisfiable. Loops are unrolled to a bound (bounded
               model checking, the default) or kept as recursive predicates
               (CHC, with --ay-chc).
  3. solve     the AY solver decides the formula. unsat: every check holds.
               sat: a concrete counterexample. unknown: inconclusive — never
               reported as a proof.
  4. report    every check is listed as SUCCESS / FAILURE / UNREACHABLE /
               UNDETERMINED, then one verdict per harness: VERIFICATION:-
               SUCCESSFUL or FAILED (or INCONCLUSIVE, VACUOUS, UNVALIDATED).
               Wherever the encoding could not model the program exactly,
               the tool says so, and a proof that relied on it is demoted
               instead of reported.

Bit-precise means: every integer is exactly as wide as in Rust, overflow and
wrapping are modeled as the hardware does them, pointers are 64-bit values
over a byte-addressed memory, and panics, arithmetic, bounds, division and
pointer checks are all properties the solver sees.

{}
Try: trust-mc quickstart        trust-mc example --list        trust-mc doctor
",
        list_lines()
    )
}

// ---------------------------------------------------------------------------
// Topic bodies. Keep every line at or under 80 columns (there is a test).
// ---------------------------------------------------------------------------

const HARNESS: &str = "\
A harness is a zero-argument function marked #[kani::proof]. Inside it you:

    let x: u32 = kani::any();        // 1. inputs: every u32, not a sample
    kani::assume(x < 4096);          // 2. preconditions (optional)
    let y = estimate_size(x);        // 3. call the code under verification
    assert!(y < 10);                 // 4. what must hold

trust-mc then checks that no input satisfying the assumptions makes an
assertion — or any built-in check — fail. `cargo build` never sees the
harness if you guard it with #[cfg(kani)]; a single file needs no guard.

Inputs
  kani::any::<T>()      a symbolic value of T: any VALID value (never an
                        invalid bit pattern). Implemented for integers, bool,
                        char, floats (unconstrained: NaN/inf included),
                        arrays [T; N], Option, Result, tuples, ranges,
                        NonZero*, Box, Duration, and for your own types with
                          #[cfg_attr(kani, derive(kani::Arbitrary))]
  kani::any_where(|v| p) any() followed by assume(p)
  kani::bounded_any::<T, N>()   Vec, String, HashMap, ... of size at most N;
                        such a proof is only valid up to that bound
  kani::vec::any_vec::<T, N>(), kani::vec::exact_vec::<T, N>()
  kani::slice::any_slice_of_array(&arr)   a symbolic sub-slice

Constraints and properties
  kani::assume(cond)    drop every input where cond is false. assume(false)
                        makes everything after it UNREACHABLE; a harness whose
                        checks are all unreachable is reported VACUOUS when the
                        harness itself cannot run, INCONCLUSIVE when it can and
                        the checks are simply dead code. Neither is a pass.
  assert!, assert_eq!, panic!, unwrap(), indexing, arithmetic, division,
                        raw-pointer use: every panic path and every built-in
                        check is a property. You get those without writing
                        an assertion.
  kani::cover!(cond)    \"can cond ever hold here?\": SATISFIED or
                        UNSATISFIABLE. Use it to prove you have not assumed
                        the interesting inputs away.
  kani::implies!(p => q)

Attributes (on the harness function, after #[kani::proof])
  #[kani::unwind(N)]          loop bound for this harness (explain bmc)
  #[kani::should_panic]       the harness must panic on some input; a run
                              with only panic failures is SUCCESSFUL
  #[kani::stub(orig, repl)]   call repl instead of orig (-Z stubbing)
  #[kani::proof_for_contract(f)] with #[kani::requires(..)],
      #[kani::ensures(|result| ..)], #[kani::modifies(..)] on f
                              function contracts (-Z function-contracts)
  #[kani::loop_invariant(c)]  loop contracts (-Z loop-contracts)
  #[kani::solver(..)]         accepted for Kani compatibility; ignored
  #[kani::harness]            trust-mc's own spelling: fn f(x: u32, b: bool)
                              — the parameters ARE the symbolic inputs

Reading assertions back: assert! inside a harness is trust-mc's own macro, so
a check is described by the stringified condition (\"assertion failed:
y < 10\"). Its reported Location may point at trust-mc's std shim rather than
your line; built-in checks (overflow, bounds, pointers) point at your code.
";

const BMC: &str = "\
By default every harness is checked by BOUNDED MODEL CHECKING: each loop is
unrolled a fixed number of times, which makes the program acyclic, and the
acyclic program is encoded as one bit-precise formula that the AY solver
decides in a single query (the `ay` binary on PATH answers it).

How many times is a loop unrolled? The first of these that is given:
    --unwind N  (with --harness)  >  #[kani::unwind(N)]  >  --default-unwind N
and if none is given, ONCE. From the front door, `--unwind N` alone sets the
crate-wide default and `--harness H --unwind N` sets H's bound.

The unwinding assertion. After the last unrolled copy, trust-mc asserts that
the loop would have exited. If some input needs more iterations, that check
fails and the harness is FAILED with a failure at the loop header (described
as \"panic reached\" / an unwinding assertion). That is the bound being too
small, not a bug in the code — raise it. The bound you need is the maximum
number of iterations PLUS ONE for the final exit test; with break/continue it
can be one or two more.

What a bounded proof means: every property holds for every input that stays
within the bound. Inputs needing more iterations were not explored — the
unwinding assertion exists precisely so that this is reported, never
silently accepted. --no-unwinding-checks removes that check; do not use it
without another argument for the bound.

Cost. The formula grows with the bound and with the width of what the loop
touches. A handful of iterations over small types is usually a second; a wide
accumulator (u32 sums, wide arrays) can take minutes or end INCONCLUSIVE
(the solver gave up before deciding). When the bound is the problem:
    * bound the INPUT (kani::assume(n <= 8)) so a small unwind is exact;
    * narrow the types the harness uses;
    * prove the loop for every iteration count with --ay-chc (explain chc);
    * -Z loop-contracts with #[kani::loop_invariant] keeps BMC but replaces
      the unroll by an invariant you supply.

Try it:  trust-mc example loop > loop.rs && trust-mc loop.rs
";

const CHC: &str = "\
With --ay-chc, loops are not unrolled. Each basic block becomes a predicate
over the program state, each control-flow edge becomes a Horn clause, and
every assertion failure becomes a clause that derives `error`. The ay-chc
engine, linked into trust-mc-driver, then searches for an INDUCTIVE
INVARIANT — a fact about the state that holds on entry, is preserved by every
iteration, and rules out `error` — using PDR/IC3 and a portfolio of related
engines (BMC, k-induction, interpolation, ...).

Outcomes
  PROOF    an invariant was found: the harness holds for EVERY iteration
           count. Printed as [AY:PROOF] CHC verification: property proven,
           then the usual SUCCESSFUL verdict.
  CTREX    a concrete path to `error`: [AY:CTREX] ... counterexample with N
           steps, verdict FAILED, [AY:CTREX_CAT:...] says how trustworthy.
  UNKNOWN  out of time, or the invariant needs theories the engine cannot
           synthesize. Reported as FAILED with \"CHC verification: ay-chc
           inconclusive\", [AY:UNKNOWN_REASON:...] (Timeout, SolverError,
           FalseProofRejected, ...) and an [AY:UNKNOWN-CATEGORY] line naming
           the bucket: PDR invariant synthesis timeout, >=2 Array-sorted state
           parameters (memory-heavy loops), solver error, no error rule
           encoded, uncategorized. Never a proof.

When to use it
  * loops whose trip count comes from kani::any() (while i < n)
  * properties that must hold for every size, not up to a bound
  * as a second opinion when BMC is INCONCLUSIVE at the bound you need
When BMC is the better tool
  * loop-free or small-bound harnesses: BMC is usually much faster
  * data-structure-heavy loops: invariants over arrays and memory are the
    hard case for invariant synthesis today (see [AY:UNKNOWN-CATEGORY])

Flags (every --ay-chc-* flag requires --ay-chc)
  --timeout 60s                  per-harness budget (--harness-timeout)
  --ay-chc-engine auto|pdr|bmc   one engine instead of the adaptive portfolio
  --ay-chc-track reg|ptr|mem     memory precision; mem (default) tracks
                                 contents, ptr only validity, reg nothing
  --ay-chc-int-lift              reason about loop counters as mathematical
                                 integers (helps PDR; trades bit-precision)
  --ay-chc-bounded-unroll        unroll to the unwind bound, then CHC
  --export-chc-comp <FILE>       write the Horn clauses (CHC-COMP format)

Mixing with a bound: if a harness under --ay-chc also has #[kani::unwind(N)]
(or --unwind / --default-unwind), its loops are unrolled to N BEFORE the CHC
encoding — a bounded CHC run. Leave the bound off for an unbounded proof.

Solver binary: the CHC solve itself runs in-process, but the engine still
checks for `ay` on PATH at startup and uses it for cover checks and for an
external proof fallback after an UNKNOWN.

Try it:  trust-mc --ay-chc --timeout 60s file.rs
";

const RESULTS: &str = "\
A run prints, in order:

  trust_mc Rust Verifier 0.3.0 (standalone)     engine banner (commit, sha)
  warning: UNSOUND: ... / CONSERVATIVE: ...     encoding fallbacks, if any
  [AY:CODEGEN_COMPLETE:harnesses=2]             compilation done
  Checking harness double_never_shrinks...      one block per harness:
  [AY:...]                                        marker lines (below)
  RESULTS:
  Check 1: double_never_shrinks.assertion.1
     - Status: SUCCESS
     - Description: \"assertion failed: double(x) >= x\"
     - Location: demo.rs:17:5 in function double_never_shrinks
  SUMMARY:
   ** 0 of 1 failed
  VERIFICATION:- SUCCESSFUL
  Verification Time: 0.1s
  Manual Harness Summary:                       at the end, over all harnesses
  Complete - 2 successfully verified harnesses, 0 failures, 2 total.

Check statuses
  SUCCESS        the property holds for every input (within the bound, in BMC)
  FAILURE        an input violates it; the harness is FAILED
  UNREACHABLE    no input reaches the check (it holds vacuously). For a
                 kani::cover it means the cover point itself is unreachable.
  UNDETERMINED   not decided: another check failed first, or an unsupported
                 construct was hit
  SATISFIED / UNSATISFIABLE   kani::cover only: reachable / provably not

Verdict line, one per harness
  VERIFICATION:- SUCCESSFUL                every check SUCCESS or UNREACHABLE
  VERIFICATION:- SUCCESSFUL (UNVALIDATED)  proved in a logic (non-linear
                 arithmetic, datatypes with bit-vectors) the solver cannot
                 fully validate; exit 0 unless --fail-on-unvalidated-success
  VERIFICATION:- FAILED                    a counterexample — OR a demoted
                 proof — OR a CHC UNKNOWN. The marker lines tell them apart.
  VERIFICATION:- INCONCLUSIVE (no checks)  the harness produced NO
                 obligations at all, so nothing was verified — not a pass
  VERIFICATION:- INCONCLUSIVE (solver undecided ...)
                 real obligations, but no verdict inside the budget (bounded
                 runs). Try --ay-chc.
  VERIFICATION:- VACUOUS (...)             every check is UNREACHABLE and the
                 harness itself cannot run: contradictory assumptions, nothing
                 was verified (--allow-vacuous turns it into a pass, loudly)
  VERIFICATION:- INCONCLUSIVE (every check is unreachable ...)
                 every check is UNREACHABLE but the harness DOES run — the
                 checks sit on dead code, so nothing was exercised. No
                 assumption is being blamed (--allow-vacuous also relaxes this)
  VERIFICATION:- UNVALIDATED (DT+BV)       a non-success in a logic the
                 solver cannot validate

Marker lines ([AY:...], machine-readable, printed even with --quiet)
  [AY:CTREX_CAT:Genuine]           a real counterexample, no encoding doubt
  [AY:CTREX_CAT:OverApproximation] may be spurious: the encoding was looser
                                   than the program somewhere
  [AY:CTREX_CAT:EncodingGap]       probably caused by a construct that could
                                   not be encoded (see the UNSOUND lines)
  [AY:CTREX_NOT_CERTIFIED]         the same two cases in words, next to the
                                   failure: this counterexample was not
                                   certified as YOUR bug, and names what the
                                   encoding fell back for. A `FAILED` carrying
                                   this line is the one to check against the
                                   `warning:` lines before you go hunting.
  [AY:CTREX_CAT:Unknown]           no counterexample at all: inconclusive;
                                   [AY:UNKNOWN_REASON:Timeout|UndecidedModel|
                                   SolverError|PreSolveDeadline|...] says why
  [AY:DEMOTION_REASONS:...]        a PROOF was downgraded to FAILED because
                                   the encoding fell back somewhere it must
                                   not; the \"warning: UNSOUND:\" lines before
                                   the first harness name the cause
  [AY:PROOF_QUALIFIERS:clean]      the strongest result: a proof with no
                                   fallback at all
  [AY:SOUND_FALLBACK:n], [AY:UNKNOWN_QUALITY:...], [AY:VACUOUS:...],
  [AY:PROOF] / [AY:CTREX] / [AY:UNKNOWN] (CHC only)

\"warning: UNSOUND: ...\" means the compiler could not encode something exactly
in a way that could hide a bug; proofs in the affected harnesses are demoted.
\"CONSERVATIVE: ...\" means it added a check that always fails instead; that
can only add failures. A clean run prints neither.

Less or more: --output-format terse (no per-check block), --quiet, --verbose
(every stage and command), --sarif <FILE>, --proof-summary-json <FILE>,
-Z concrete-playback --concrete-playback print (a unit test that replays the
counterexample). Exit status: explain exit-codes.
";

const SOUNDNESS: &str = "\
A proof from trust-mc means: under the harness's assumptions no input can
make any check fail — within the unwind bound for bounded runs, for every
iteration count with --ay-chc. The tool is built to fail closed:

  * Anything the encoder cannot translate exactly is counted. Fallbacks that
    could hide a bug — hard-coded widths, dropped stores, zeroed constants,
    synthesized pointee values, unsupported constructs, floats as plain
    bit-vectors, ... — DEMOTE a PROOF to FAILED and are printed as
    \"warning: UNSOUND: ...\". Fallbacks that can only make the encoding
    stricter (havocked values) may stay in a proof but are counted
    ([AY:SOUND_FALLBACK:n]); untranslatable assertions become checks that
    always fail (CONSERVATIVE).
  * A solver UNKNOWN, timeout or error is never a proof.
  * Proofs in logics the solver cannot validate are marked UNVALIDATED.
  * The AY revision linked into the engine is pinned; `trust-mc version -v`
    and `trust-mc doctor` print it, and the engine refuses to attest a dirty
    or off-pin build.

Checked by default: assertions and every panic path (unwrap, expect,
unreachable!, index, ...); arithmetic overflow; division and remainder by
zero; array and slice bounds; pointer validity (null, out of bounds,
misaligned, use after free, double free, size mismatch); shift distances;
enum discriminants; the unwinding assertion. -Z uninit-checks and
-Z valid-value-checks add uninitialized-memory and invalid-value checks.

Not checked, or approximated: data races and concurrency (code is analysed
as if sequential); aliasing-model (Stacked/Tree Borrows) violations;
lifetimes; invalid values built with transmute (without -Z valid-value-
checks); inline assembly; IEEE rounding of floats (modeled as bit-vectors —
a proof that depends on it is demoted); platform-specific behaviour.
Verification assumes the program is free of undefined behaviour it does not
model.

Ways to fool yourself
  * over-constraining with kani::assume — use kani::cover! to confirm the
    branches you care about are reachable; an all-unreachable harness is
    reported VACUOUS (the harness cannot run) or INCONCLUSIVE (it runs, but
    every check is dead code), never SUCCESSFUL
  * bounded inputs (bounded_any, a small unwind) prove only up to the bound
  * stubs (-Z stubbing) and contracts are assumptions about the stubbed code
  * --no-*-checks, --ignore-global-asm, --extra-pointer-checks trade soundness
    or precision exactly as their help says
";

const CARGO: &str = "\
Inside a Cargo package the same engine verifies the whole crate graph:

    cargo trust-mc                     every harness in the package
    cargo trust-mc --harness NAME      one harness (substring match)
    cargo trust-mc list                harnesses and contracts
    cargo trust-mc --tests             also compile #[cfg(test)] code and
                                       dev-dependencies (harnesses in tests/)
    cargo trust-mc --workspace / -p NAME / --features ...   as in cargo

Dependencies are compiled by trust-mc-compiler as well (with cfg(kani) set),
so harnesses can reach into them. Guard harnesses so plain builds ignore them:

    #[cfg(kani)]
    mod verification {
        use super::*;
        #[kani::proof]
        fn check_something() { /* ... */ }
    }

Persistent flags go in Cargo.toml (package or workspace; the command line
wins over both):

    [package.metadata.kani.flags]
    default-unwind = \"4\"
    [package.metadata.kani.unstable]
    function-contracts = true

`cargo trust-mc --help` lists every option; the verify options and
subcommands are the same as the single-file form. `targo trust-mc` is the
Trust-toolchain spelling of the same command.

Engine discovery is shared with `trust-mc`: a local build
(cargo run --release -p build-trust-mc -- build-dev --release) serves both,
and `cargo trust-mc setup` installs a release bundle (explain install).
";

const KANI: &str = "\
trust-mc is derived from Kani and keeps its harness language and CLI shape:
#[kani::proof], kani::any / assume / cover!, #[kani::unwind],
#[kani::should_panic], #[cfg(kani)], the `kani` crate name, --harness /
--unwind / --default-unwind / --output-format / --tests, the list /
autoharness / playback subcommands, and the output shape (Checking harness,
RESULTS, VERIFICATION:- SUCCESSFUL / FAILED). Existing Kani harnesses compile
unchanged.

Deliberate differences
  * One backend: AY, an SMT/CHC solver linked into the engine. There is no
    CBMC, no goto program, no SAT-solver selection. --solver <cbmc solver>,
    --cbmc-args, --gen-c, --print-llbc, --synthesize-loop-contracts and
    friends are rejected with the alternative; #[kani::solver] is accepted
    and ignored.
  * Unbounded proofs: --ay-chc (explain chc). Kani has no equivalent.
  * Fail-closed verdicts: proofs that relied on encoding fallbacks are
    demoted; all-unreachable harnesses are VACUOUS or INCONCLUSIVE; one
    that produced NO checks is INCONCLUSIVE rather than a pass (Kani
    reports success);
    logics AY cannot validate are UNVALIDATED; every run carries [AY:...]
    marker lines. A run with no input file exits 2, not 0 -- nothing was
    verified, so nothing succeeded.
  * Reports agree with the exit code: a harness that fails without any single
    property failing (VACUOUS, INCONCLUSIVE) still leaves a finding in
    --sarif, under trust_mc.harness.vacuous / .no_checks. An empty report
    means an empty report, never a run that failed elsewhere.
  * --fail-fast counts what it already verified. Stopping at the first
    failure does not un-verify the harnesses that passed before it, so they
    stay in the summary; only the failure that triggered the stop is
    reported, since under --jobs N which others failed is a race.
  * Loop bound default: Kani (CBMC) keeps unwinding a loop until it is
    exhausted, which may never finish; trust-mc unrolls ONCE unless told
    otherwise and reports the unwinding assertion (explain bmc).
  * Extra flags: --timeout, --ay-chc*, --sarif, --proof-summary-json,
    --config-free, --fail-on-unvalidated-success, --allow-vacuous,
    --strict-vacuity, --conformance-harness, --version-authority.
  * Binaries: trust-mc, cargo-trust-mc, targo-trust-mc. `kani` and
    `cargo kani` are not installed (the engine still understands those
    identities for Kani's own test corpus).
  * trust-mc additions: #[kani::harness] (parameters are the inputs),
    kani::value_view, TrustMcMap (-Z symbolic-collections), stub sets.

Migrating a Kani project: replace `cargo kani` with `cargo trust-mc`; drop
CBMC-only flags; for unbounded loops try --ay-chc before raising bounds.
";

const FLAGS: &str = "\
The front door translates a few friendly flags and forwards everything else
to the engine unchanged, so the engine's whole surface stays reachable:

    front door                engine
    --unwind N                --default-unwind N, or --unwind N with --harness
    --timeout T               -Z unstable-options --harness-timeout T
    --list / --harnesses      --harnesses   (no solver needed)
    --solver auto|ay          --smt-solver ...
    -v / -q / --debug         the same

Engine flag families (`trust-mc flags` prints the common ones, `flags --all`
every one; `trust-mc list --help`, `autoharness --help`, ... for subcommands)
  selection    --harness NAME (repeatable), --exact, --tests, --config-free
  bounds       --default-unwind N, --unwind N, --harness-timeout T (gated by
               -Z unstable-options), --tool-timeout T
  backend      --ay-chc and --ay-chc-engine / -track / -step / -int-lift /
               -bounded-unroll / -transform / -skip-verify / -no-retry,
               --ay-wide-mem, --smt-solver, --backend, --export-smtlib FILE,
               --export-chc-comp FILE
  checks       --no-default-checks, --no-memory-safety-checks,
               --no-overflow-checks, --no-unwinding-checks,
               --no-undefined-function-checks, --no-assertion-reach-checks,
               --extra-pointer-checks (-Z unstable-options)
  output       --output-format regular|terse|old, --quiet, --verbose,
               --debug, --sarif FILE, --proof-summary-json FILE,
               --output-into-files, --keep-temps, --message-format human|json
  policy       --fail-fast, --fail-on-unvalidated-success, --allow-vacuous,
               --strict-vacuity, --conformance-harness NAME
  features     -Z <feature>: unstable-options, concrete-playback,
               source-coverage (--coverage), stubbing, function-contracts,
               loop-contracts, autoharness, quantifiers, uninit-checks,
               valid-value-checks, mem-predicates, ghost-state, async-lib,
               float-lib, c-ffi, symbolic-collections, restrict-vtable, ...
  parallelism  -j [N]   (requires --output-format terse)
  provenance   --version-authority (the linked AY revision; fails closed on
               a dirty or off-pin build)

Rejected by name, with the alternative (CBMC-era): --cbmc-args,
--solver <cbmc solver>, --solver-args, --gen-c, --print-llbc,
--write-json-symtab, --synthesize-loop-contracts, --no-slice-formula,
--run-sanity-checks, --visualize, --enable-unstable, --dry-run.
";

const INSTALL: &str = "\
Three pieces must be present for a verification run:

  1. the engine: trust-mc-driver and, beside it, trust-mc-compiler (a rustc
     driver that links the pinned nightly's librustc_driver)
  2. the library sysroot, built by that compiler: lib/ (std and the kani
     crate compiled for verification), playback/lib (concrete playback),
     no_core/lib (verify-std)
  3. the AY solver binary `ay` on PATH — bounded runs shell out to it, and
     the engine checks for it before every verification (CHC solves
     in-process)

trust-mc looks for the engine, in this order, and `trust-mc doctor` shows
what it found:

    $TRUST_MC_SYSROOT/bin/trust-mc-driver
    <dir>/target/trust-mc/bin/trust-mc-driver   for each ancestor of the
        working directory, then of this executable   (a local build)
    ${KANI_HOME:-~/.kani}/kani-<VERSION>/bin/trust-mc-driver   (a release
        bundle, installed by `trust-mc setup`)

Building from a checkout (needs rustup; rust-toolchain.toml pins the nightly
and the rustc-dev / rust-src components it needs):

    cargo run --release -p build-trust-mc -- build-dev --release
    cargo install --path .      # trust-mc, cargo-trust-mc, targo-trust-mc

The solver: build `ay` in a sibling checkout of alabsystems/ay

    cd ../ay && cargo build --release -p ay --features cli
    export PATH=\"$PWD/target/release:$PATH\"

`trust-mc doctor` checks that the binary's commit matches the AY the engine
links (bounded verdicts come from the binary, CHC verdicts from the link).

Environment: TRUST_MC_SYSROOT (engine + sysroot directory), KANI_HOME (bundle
root), TRUST_MC_LOG=trust_mc_driver=debug (engine logging),
TRUST_MC_DRIVER_WATCHDOG_DISABLE (no wall-clock watchdog).
";

const EXIT_CODES: &str = "\
What `trust-mc` exits with:

    0   every selected harness verified (VERIFICATION:- SUCCESSFUL), or a
        listing / help / explain / example / doctor-ready run completed
    1   at least one harness FAILED, was INCONCLUSIVE, VACUOUS or UNVALIDATED
        (non-success); or the engine hit an error (compile error, no harness
        matched the filter, ...)
    2   usage error: unknown command or flag, missing or nonexistent input,
        a flag trust-mc cannot honor
    3   not ready: engine, sysroot or solver not found (`trust-mc doctor`)

One exception, on purpose: a crate that declares NO #[kani::proof] harnesses
reports VERIFICATION:- INCONCLUSIVE (no proof harnesses were found to verify)
and still exits 0. Nothing was verified, so it is not a proof and is not
labelled one -- but Kani exits 0 here, and a workspace where one member has no
harnesses should not fail the build. Look for [AY:NO_HARNESSES] to detect it.

Inside the engine: SUCCESSFUL (UNVALIDATED) exits 0 unless
--fail-on-unvalidated-success; --fail-fast stops at the first failure; a
wall-clock watchdog kill prints VERIFICATION:- FAILED and exits 1.
";

const QUICKSTART: &str = "\
1. Check the installation
       trust-mc doctor
   It names the engine, the library sysroot and the `ay` solver it will use,
   and prints the command that fixes anything missing.

2. Run a harness
       trust-mc example > demo.rs
       trust-mc demo.rs
   Expect two \"Checking harness\" blocks, each ending VERIFICATION:-
   SUCCESSFUL, then \"Complete - 2 successfully verified harnesses\".

3. See a failure and its counterexample
       trust-mc example bug > bug.rs
       trust-mc bug.rs
   The overflow check is FAILURE with its source location, the marker
   [AY:CTREX_CAT:Genuine] says it is real, and the exit status is 1.
   Then: trust-mc example --list  (bounds, unsafe, assume, cover, loop).

4. Write your own
   - put the code under test and a #[kani::proof] fn in one .rs file
   - kani::any() for inputs, kani::assume for preconditions, assert! for
     properties (explain harness)
   - loops need a bound: #[kani::unwind(N)] on the harness or --unwind N
     (explain bmc) — or prove them for every N with --ay-chc (explain chc)

5. Everyday commands
       trust-mc --list file.rs                  which harnesses are there
       trust-mc --harness NAME file.rs          just one
       trust-mc --unwind 8 file.rs              raise the loop bound
       trust-mc --timeout 60s file.rs           cap each harness's solve
       trust-mc --ay-chc file.rs                unbounded mode
       trust-mc --output-format terse file.rs   verdicts only
       trust-mc -v file.rs                      every stage and command

6. Read the result (explain results). When the verdict is FAILED, the
   [AY:CTREX_CAT:...] line says whether it is a real counterexample, a
   demoted proof, or an inconclusive solve.

7. Moving to a Cargo package: cargo trust-mc (explain cargo).
";

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "a panicking assertion is the point in tests")]
mod tests {
    use super::*;

    #[test]
    fn every_topic_renders_within_eighty_columns() {
        for t in TOPICS {
            let page = render(t.name).unwrap();
            for line in page.lines() {
                assert!(line.len() <= 80, "`{}`: overlong line ({}): {line}", t.name, line.len());
                assert!(!line.ends_with(' '), "`{}`: trailing space: {line:?}", t.name);
            }
        }
        for line in overview().lines() {
            assert!(line.len() <= 80, "overview: overlong line ({}): {line}", line.len());
        }
    }

    #[test]
    fn names_and_aliases_are_unique() {
        let mut seen: Vec<&str> = Vec::new();
        for t in TOPICS {
            for n in std::iter::once(&t.name).chain(t.aliases) {
                assert!(!seen.contains(n), "duplicate topic name or alias `{n}`");
                seen.push(n);
            }
        }
    }

    #[test]
    fn aliases_resolve_and_unknown_topics_suggest() {
        assert_eq!(find("unbounded").unwrap().name, "chc");
        assert_eq!(find("UNWIND").unwrap().name, "bmc");
        assert!(render("overview").is_some());
        let err = command(&[OsString::from("resutls")]).unwrap_err();
        assert_eq!(err.code, super::super::EXIT_USAGE);
        assert!(err.msg.contains("did you mean `trust-mc explain results`"), "{}", err.msg);
    }

    #[test]
    fn the_overview_lists_every_topic_and_the_pipeline_stages() {
        let page = overview();
        for t in TOPICS {
            assert!(page.contains(t.name), "overview omits `{}`", t.name);
        }
        for stage in ["compile", "encode", "solve", "report"] {
            assert!(page.contains(stage), "overview omits the `{stage}` stage");
        }
    }

    #[test]
    fn the_pages_state_the_load_bearing_facts() {
        // These are the facts a reader most needs to have right; if the engine
        // changes them, the text (and this test) must change with it.
        let bmc = render("bmc").unwrap();
        assert!(bmc.contains("ONCE"), "default unwind bound is 1");
        assert!(bmc.contains("PLUS ONE"), "iterations plus one");
        let chc = render("chc").unwrap();
        assert!(chc.contains("--ay-chc"));
        assert!(chc.contains("Never a proof"));
        let results = render("results").unwrap();
        assert!(results.contains("VERIFICATION:- INCONCLUSIVE (no checks)"));
        assert!(results.contains("[AY:CTREX_CAT:Genuine]"));
        let exit = render("exit-codes").unwrap();
        for code in ["0", "1", "2", "3"] {
            assert!(exit.contains(&format!("    {code}   ")), "exit code {code} missing");
        }
    }
}

const LIMITS: &str = "\
Verification that does not go through yet. Every entry here was measured, and
every one FAILS CLOSED — you get a demotion or an inconclusive verdict,
never a false proof. The point of this page is that you can check it before
spending an afternoon on a bug that is ours rather than yours.

How to tell a limitation from your bug — the marker lines say which:

  [AY:CTREX_CAT:Genuine]              a real counterexample. This one is yours.
  [AY:DEMOTED_NOT_A_COUNTEREXAMPLE]   NOTHING was disproved. The harness was
                                      proved and then downgraded because the
                                      encoding approximated something.
  [AY:CTREX_NOT_CERTIFIED]            a counterexample the classifier could not
                                      certify; may be yours, may be an artifact.
  VERIFICATION:- INCONCLUSIVE (solver undecided ...)
                                      real obligations, no verdict in budget.
                                      Try --ay-chc.

Known limitations
  recursion     A recursive function is not modelled. The inliner will not
                inline a function into itself, so the call falls back and its
                result is unconstrained, and the failure you get looks
                unrelated (`fn f(n) { 1 + f(n-1) }` reports an arithmetic
                overflow, because 1 + <unconstrained> can). --unwind will not
                help; it bounds loops. --ay-chc proves a recursive call whose
                argument is a compile-time CONSTANT, by folding the call away
                before the solver sees it — but a SYMBOLIC argument still
                fails in both modes, so do not read that as recursion support.
  maps          HashMap/BTreeMap CONTENTS are not modelled; the LENGTH is.
                Under --ay-chc len() and is_empty() prove. A lookup by
                reference (get / contains_key / remove with `&key`) declines
                rather than answers: it comes back FAILED carrying
                [AY:CTREX_NOT_CERTIFIED] and a `CONSERVATIVE:` warning, which
                is a labelled non-answer rather than a claim about your code.
                Under BMC every map operation demotes
                (pointee_synthesis_fallback). -Z symbolic-collections does
                not change any of this.
  ? on None     Reading a `Some` payload on a branch that provably cannot run.
                With a statically-known None, `if let Some(v) = o` and
                `match o { Some(v) => ..v.. }` both come back FAILED and
                demoted (DEMOTION_REASONS:unconstrained_assignment); `x?`
                inside a function called with None instead spends the whole
                budget and returns INCONCLUSIVE, tagged
                UNKNOWN_QUALITY:EncodingGap:unconstrained_assignment. All
                three are BMC only: --ay-chc proves every one of them. A
                SYMBOLIC Option is fine in either mode.
                `None.map(..)` demotes under BMC for the reason above, but
                --ay-chc PROVES it, and so does `and_then`, a bare
                `let f = |x| ..; f(n)`, an FnMut that mutates its capture, a
                closure passed through a higher-order fn, and a Box<dyn Fn>.
                Closures are no longer the --ay-chc boundary they once were.
                What still declines is a closure inside a stdlib ITERATOR
                chain: `a.iter().map(..).sum()` comes back FAILED with a
                translation drop, and that one BMC gets right. Neither lane
                dominates the other here.
  Vec elements  Use --ay-chc. Under BMC `Vec::from(&[T])` carries its LENGTH
                but leaves the ELEMENTS over-approximated, so proofs about
                what a Vec contains do not go through. --ay-chc models the
                elements, symbolic ones included.
  String bytes  `bounded_any::<String, N>()` gives you `len() <= N`; the bytes
                are unconstrained rather than guaranteed-valid UTF-8.
  iterators     Some stdlib iterator internals have no MIR here and are stubbed;
                the run warns with the exact function names.
  uninit-checks -Z uninit-checks catches a genuine uninitialised read, but also
                flags reads that ARE initialised, so it cannot yet be used to
                clear code. The warnings name the constructs.

What is NOT on this list, because it works: integer and float arithmetic with
overflow, division and shift checks; pointer and slice bounds; enums including
explicit discriminants; structs and tuples; trait and dyn dispatch; function
contracts; stubbing; quantifiers; loops within their unwind bound.

Found one that is not here? That is worth reporting — the sweep that produced
this page pairs every claim with a control that must FAIL, and a gap it missed
is a gap nobody has measured.

See also: trust-mc explain {soundness, results, chc, kani}
";
