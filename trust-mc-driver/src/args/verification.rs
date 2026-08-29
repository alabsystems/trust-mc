// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Verification argument definitions for the trust-mc CLI.
//!
//! Contains [`VerificationArgs`], the common argument struct shared across all
//! trust-mc subcommands that perform verification.

use std::path::PathBuf;
use std::str::FromStr;

use clap::error::{Error, ErrorKind};

use super::cargo::CargoCommonArgs;
use crate::args::cargo::CargoTargetArgs;
use crate::args::common::*;
use crate::args::solver::{
    AYChcAutoInvariantsMode, AYChcEngine, AYChcProofCoreMode, AYSolver, Backend, CheckArgs,
    ConcretePlaybackMode, NumThreads, OutputFormat, Timeout,
};
use crate::util::warning;
use trust_mc_metadata::SolverOption;
pub(crate) use trust_mc_metadata::{ChcStepMode, ChcTrackLevel};

// Common arguments for invoking trust-mc for verification purpose. This gets put into KaniContext,
// whereas anything above is "local" to "main"'s control flow.
// When adding an argument to this struct, make sure that it's in alphabetical order as displayed to the user when running --help.
#[derive(Debug, clap::Args)]
#[clap(next_help_heading = "Verification Options")]
pub(crate) struct VerificationArgs {
    /// Link external C files referenced by Rust code.
    /// This is an experimental feature and requires `-Z c-ffi` to be used
    #[arg(long, hide = true, num_args(1..))]
    pub c_lib: Vec<PathBuf>,

    /// Verify a trust_vc MergeBundle JSON artifact directly, without compiling a Rust crate.
    #[arg(long, value_name = "PATH")]
    pub trust_vc_bundle: Option<PathBuf>,

    /// Generate concrete playback unit test.
    /// If value supplied is 'print', trust-mc prints the unit test to stdout.
    /// If value supplied is 'inplace', trust-mc automatically adds the unit test to your source code.
    /// This option does not work with `--output-format old`.
    #[arg(long, ignore_case = true, value_enum)]
    pub concrete_playback: Option<ConcretePlaybackMode>,

    /// Run only "config-free" proof harnesses: those annotated with a bare
    /// `#[kani::proof]` and no per-harness configuration (`#[kani::unwind]`,
    /// `#[kani::stub]`, `#[kani::solver]`, or a proof-for-contract target).
    /// These verify with trust-mc's defaults and need no manual tuning, so they
    /// are the set executed BY DEFAULT during Trust compilation (batteries-on
    /// verification). Config-requiring harnesses are reported and skipped, never
    /// silently dropped — a skipped proof is not a proved proof.
    #[arg(long)]
    pub config_free: bool,

    /// Enable trust-mc coverage output alongside verification result
    #[arg(long, hide_short_help = true)]
    pub coverage: bool,

    /// Specify the value used for loop unwinding for bounded verification
    #[arg(long)]
    pub default_unwind: Option<u32>,

    /// When specified, the harness filter will only match the exact fully qualified name of a harness
    #[arg(long, requires("harnesses"))]
    pub exact: bool,

    /// Enable extra pointer checks such as invalid pointers in relation operations and pointer
    /// arithmetic overflow.
    /// This feature is unstable and it may yield false counter examples. It requires
    /// `-Z unstable-options` to be used
    #[arg(long, hide_short_help = true)]
    pub extra_pointer_checks: bool,

    /// Stop the verification process as soon as one of the harnesses fails.
    #[arg(long)]
    pub fail_fast: bool,

    /// Exit with failure if any harness succeeds without validation.
    #[arg(long)]
    pub fail_on_unvalidated_success: bool,

    /// Relax the vacuity gate (V4): by default a harness whose every non-cover check
    /// is provably UNREACHABLE is a FAILURE — its assumptions were contradictory
    /// (`kani::assume(false)` / over-constrained preconditions), so the "proof"
    /// discharged its assertions only vacuously. Pass this to treat such a harness as
    /// a pass instead (a loud `[AY:VACUOUS:allowed]` marker is still emitted).
    #[arg(long)]
    pub allow_vacuous: bool,

    /// Escalate vacuity WARNINGS to hard failures (V5): a declared `kani::cover(...)`
    /// the solver PROVED unsatisfiable/unreachable means the harness claims to
    /// exercise a behavior it provably never reaches. Off by default (warning only).
    #[arg(long)]
    pub strict_vacuity: bool,

    /// Mark a harness as a CONFORMANCE harness (V5, the manifest tier). A conformance
    /// harness claims to *exercise* a binding, so it MUST demonstrate it by reaching at
    /// least one SATISFIED `kani::cover(...)`; none satisfied ⇒ it proved nothing about
    /// behavior and is a hard failure (VACUOUS), regardless of `--strict-vacuity`.
    /// Repeatable; matched against the harness's pretty name. This is the CLI form of
    /// the design's `role = "conformance"` harness-manifest tag.
    #[arg(long = "conformance-harness", value_name = "NAME")]
    pub conformance_harnesses: Vec<String>,

    /// Force trust-mc to rebuild all packages before the verification.
    #[arg(long)]
    pub force_build: bool,

    /// If specified, only run harnesses that match this filter. This option can be provided
    /// multiple times, which will run all tests matching any of the filters.
    /// If used with --exact, the harness filter will only match the exact fully qualified name of a harness.
    #[arg(long = "harness", num_args(1), value_name = "HARNESS_FILTER")]
    pub harnesses: Vec<String>,

    /// Timeout for each harness with optional suffix ('s': seconds, 'm': minutes, 'h': hours). Default is seconds. This option is experimental and requires `-Z unstable-options` to be used.
    #[arg(long)]
    pub harness_timeout: Option<Timeout>,

    /// Timeout for tool processes (compiler, linker, etc.) with optional suffix ('s': seconds, 'm': minutes, 'h': hours).
    /// Default is 10 minutes. Set to 0 to disable timeout (not recommended).
    /// This prevents runaway processes from hanging indefinitely.
    #[arg(long, hide_short_help = true)]
    pub tool_timeout: Option<Timeout>,

    /// Do not error out for crates containing `global_asm!`.
    /// This option may impact the soundness of the analysis and may cause false proofs and/or counterexamples
    #[arg(long, hide_short_help = true)]
    pub ignore_global_asm: bool,

    /// Number of threads to spawn to verify harnesses in parallel.
    /// Omit the flag entirely to run sequentially (i.e. one thread).
    /// Pass -j to run with the thread pool's default number of threads.
    /// Pass -j <N> to specify N threads.
    #[arg(short, long, hide_short_help = true)]
    jobs: Option<Option<usize>>,

    /// Keep temporary files generated throughout trust-mc process. This is already the default
    /// behavior for `cargo-trust-mc`.
    #[arg(long, hide_short_help = true)]
    pub keep_temps: bool,

    /// Do not assert the function contracts of dependencies. Requires -Z function-contracts.
    #[arg(long, hide_short_help = true)]
    pub no_assert_contracts: bool,

    /// Turn off assertion reachability checks
    #[arg(long)]
    pub no_assertion_reach_checks: bool,

    /// Run trust-mc without codegen. Useful for quick feedback on whether the code would compile successfully (similar to `cargo check`).
    /// This feature is unstable and requires `-Z unstable-options` to be used
    #[arg(long, hide_short_help = true)]
    pub no_codegen: bool,

    /// Rust edition to compile the input with, forwarded to `rustc --edition`.
    ///
    /// Unset means rustc's own default (2015), which is what Kani's compiletest
    /// also uses when neither a `// compile-flags: --edition ...` header nor its
    /// `--edition` option supplies one — so leaving this unset keeps trust-mc
    /// compiling the same program Kani does. Defaulting it to 2021 was measured
    /// at -4 parity and +9 compile errors on the corpus, because edition
    /// controls closure capture granularity, array `IntoIterator`, and `panic!`
    /// macro semantics.
    ///
    /// Without this flag there was NO way to select an edition on the command
    /// line: `--edition 2021` was rejected as an unexpected argument, so a file
    /// using edition-gated syntax (e.g. `c"..."` C-string literals, edition
    /// >= 2021) could not be verified at all.
    #[arg(long, value_name = "EDITION")]
    pub edition: Option<String>,

    /// Internal mode used by `cargo trust-mc list`/`trust-mc list`: run the compiler
    /// backend far enough to emit metadata, but skip per-harness verification
    /// condition generation.
    #[arg(skip)]
    pub list_metadata_only: bool,

    /// Disable restricting the targets of virtual table function pointer calls
    #[arg(long, hide_short_help = true)]
    pub no_restrict_vtable: bool,

    /// trust-mc will only compile the crate. No verification will be performed
    #[arg(long, hide_short_help = true)]
    pub only_codegen: bool,

    /// Toggle between different styles of output
    #[arg(long, default_value = "regular", ignore_case = true, value_enum)]
    pub output_format: OutputFormat,

    /// Write verification results into per-harness files, rather than to stdout
    #[arg(long, hide_short_help = true)]
    pub output_into_files: bool,

    /// Compute verification results under the assumption that no panic occurs.
    /// This feature is unstable, and it requires `-Z unstable-options` to be used
    #[arg(long, hide_short_help = true)]
    pub prove_safety_only: bool,

    /// Write an informational proof summary JSON artifact to the given path.
    ///
    /// This is a pointer artifact for reviewers. It summarizes ordinary trust_mc
    /// verification results and names the authoritative replacement proof flow:
    /// `scripts/extract_replacement_proof_report.py` plus `tools/replacement-audit`.
    /// It does not validate replacement-audit criteria.
    #[arg(long, value_name = "PATH")]
    pub proof_summary_json: Option<PathBuf>,

    /// Randomize the layout of structures. This option can help catching code that relies on
    /// a specific layout chosen by the compiler that is not guaranteed to be stable in the future.
    /// If a value is given, it will be used as the seed for randomization
    /// See the `-Z randomize-layout` and `-Z layout-seed` arguments of the rust compiler.
    #[arg(long)]
    pub randomize_layout: Option<Option<u64>>,

    /// Restrict the targets of virtual table function pointer calls.
    /// This feature is unstable and it requires `-Z restrict-vtable` to be used
    #[arg(long, hide = true, conflicts_with = "no_restrict_vtable")]
    pub restrict_vtable: bool,

    /// Directory for all generated artifacts.
    #[arg(long)]
    pub target_dir: Option<PathBuf>,

    /// Enable test function verification. Only use this option when the entry point is a test function
    #[arg(long)]
    pub tests: bool,

    /// Specify the value used for loop unwinding for the specified harness
    #[arg(long, requires("harnesses"))]
    pub unwind: Option<u32>,

    /// Select the verification backend.
    /// Auto (default) and ay currently resolve to the same backend.
    #[arg(long, default_value = "auto", value_enum)]
    pub backend: Backend,

    /// Select the SMT solver used by the AY backend.
    /// Auto (default) uses ay native.
    /// Alias: --smt-solver (preferred for new code)
    #[arg(
        long,
        visible_alias = "smt-solver",
        default_value = "auto",
        value_enum,
        hide_short_help = true
    )]
    pub ay_solver: AYSolver,

    /// Use the abstract IR emission path for AY backend (experimental).
    ///
    /// When enabled, uses `emit_bmc(bmc_vc)` to generate the AY program from the
    /// abstract BMC verification condition instead of direct program construction.
    /// This is the target architecture for cleaner MIR → trust_mc_core IR → AY separation.
    #[arg(long, hide_short_help = true)]
    pub ay_emit_bmc: bool,

    /// Use CHC/Horn clause mode for AY backend (experimental).
    ///
    /// When enabled, uses `mir_to_chc()` and `emit_chc()` to translate MIR to
    /// Horn clauses for unbounded verification. Uses ay-chc portfolio solver
    /// (native CHC engine).
    /// This avoids loop unrolling by expressing loops as recursive predicates.
    /// See #28 and #574 for CHC implementation progress.
    #[arg(long)]
    pub ay_chc: bool,
    /// Enable auto-invariant candidate generation for CHC (experimental).
    ///
    /// Modes:
    /// - `off`: disabled (default)
    /// - `range`: generate range-style candidates from recursive transitions
    /// - `houdini`: generate candidate seeds for Houdini-style refinement
    ///
    /// Requires `--ay-chc` and a binary built with `ay-chc-native`.
    #[arg(
        long,
        value_enum,
        default_value_t = AYChcAutoInvariantsMode::Off,
        hide_short_help = true
    )]
    pub ay_chc_auto_invariants: AYChcAutoInvariantsMode,

    /// Enable proof-core distillation for CHC (experimental).
    ///
    /// Adds a pre-solve stage that builds bounded obligations for canonical
    /// range-loop predicates, extracts unsat cores, lifts them into
    /// predicate-variable hints, and injects validated formulas before the
    /// portfolio solve.
    ///
    /// Modes:
    /// - `off`: disabled (default)
    /// - `range`: distill proof cores from canonical range-loop predicates
    ///
    /// Only effective when `--ay-chc` is enabled.
    /// Part of #2875 (lane #20).
    #[arg(
        long,
        value_enum,
        default_value_t = AYChcProofCoreMode::Off,
        hide_short_help = true
    )]
    pub ay_chc_proof_core: AYChcProofCoreMode,

    /// Select the CHC fixedpoint engine for ay-chc HORN logic solving.
    ///
    /// - `auto` (default): ay-chc adaptive portfolio (PDR/IC3, BMC, k-induction, etc.)
    /// - `pdr`: Force the PDR engine only
    /// - `bmc`: Force BMC engine (best for non-loop BV-heavy harnesses)
    ///
    /// Override with env var `AY_CHC_ENGINE=bmc|pdr|auto`.
    /// Part of #3688.
    #[arg(
        long,
        value_enum,
        default_value_t = AYChcEngine::Auto,
        hide_short_help = true
    )]
    pub ay_chc_engine: AYChcEngine,

    /// Disable CHC UNKNOWN retry and CTREX-recovery follow-up strategies.
    ///
    /// Equivalent to `TRUST_MC_CHC_NO_RETRY=1`, but available as a real CLI flag so
    /// compiletest files can request stable base-engine verdicts without
    /// depending on shell environment.
    #[arg(long, hide_short_help = true)]
    pub ay_chc_no_retry: bool,

    /// Enable verbose CHC debug tracing in the compiler (experimental).
    ///
    /// Prints CHC encoding details to stderr for troubleshooting.
    #[arg(long, hide_short_help = true)]
    pub ay_chc_debug: bool,

    /// Override the SMT-LIB logic for AY backend (advanced).
    ///
    /// By default, trust-mc selects logic automatically:
    /// - CHC mode: HORN
    /// - BMC mode: QF_AUFBV (or ALL with datatypes)
    ///
    /// Use this option to force a specific logic for experimentation.
    /// Common values: HORN, QF_AUFBV, QF_ABV, ALL, QF_DT
    #[arg(long, hide_short_help = true)]
    pub ay_logic: Option<String>,

    /// Export the SMT-LIB query to a file for external solver cross-check.
    ///
    /// Use this to validate trust_mc's translation against Z3 or other solvers:
    /// ```
    /// trust-mc --export-smtlib query.smt2 test.rs
    /// z3 query.smt2  # Compare with trust_mc's verdict
    /// ```
    ///
    /// For CHC mode queries, use SeaHorn or other CHC solvers.
    /// Part of oracle cross-check (#1908, #1910).
    #[arg(long)]
    pub export_smtlib: Option<PathBuf>,

    /// Export CHC query in CHC-COMP compatible SMT-LIB/HORN format.
    ///
    /// This requires `--ay-chc`. The compiler emits SMT-LIB/HORN for CHC
    /// harnesses; this export path filters model-query commands so the file is
    /// consumable by external CHC solvers.
    ///
    /// Part of #659. Fix: #3865.
    #[arg(long, hide = true)]
    pub export_chc_comp: Option<PathBuf>,

    /// Write SARIF output (Static Analysis Results Interchange Format) to the given path.
    ///
    /// Produces machine-readable verification results compatible with CI/code-scanning
    /// workflows. The output follows SARIF v2.1.0 and includes all failed and
    /// undetermined properties with source locations.
    /// Not compatible with `--output-format=old` or `--only-codegen`.
    #[arg(long, value_name = "PATH")]
    pub sarif: Option<PathBuf>,

    /// CHC memory tracking precision level.
    ///
    /// Controls how memory operations are modeled in CHC encoding:
    /// - `reg`: Register-only, loads havoc, stores no-op (loses ref chains)
    /// - `ptr`: Pointer validity, loads havoc but emits r_ok checks
    /// - `mem` (default): Full memory, uses select/store for complete modeling
    ///
    /// Only effective when `--ay-chc` is enabled.
    /// Part of #2214: Default changed from `reg` to `mem`.
    #[arg(long, value_enum, default_value_t = ChcTrackLevel::Mem, hide_short_help = true)]
    pub ay_chc_track: ChcTrackLevel,

    /// CHC encoding step granularity (#112).
    ///
    /// Controls predicate density in CHC encoding:
    /// - `small`: one predicate per MIR basic block
    /// - `large`: one predicate per cut point (loop headers + entry/exit)
    /// - `auto` (default): `large` for functions with loops, `small` for acyclic
    ///
    /// Large-step encoding reduces predicate count for loops, helping PDR
    /// converge on inductive proofs. Only effective when `--ay-chc` is enabled.
    #[arg(long, value_enum, default_value_t = ChcStepMode::Auto, hide_short_help = true)]
    pub ay_chc_step: ChcStepMode,

    /// Lift bitvector sorts to integer sorts for loop-header CHC predicates.
    ///
    /// When enabled, loop-header relation parameters use Int sorts instead of
    /// BitVec, letting PDR synthesize invariants in LIA (linear integer
    /// arithmetic) instead of BV theory. Only effective when `--ay-chc` is enabled.
    ///
    /// Part of #112: designs/2026-03-03-loop-invariant-synthesis.md Direction 2.
    #[arg(long, hide_short_help = true)]
    pub ay_chc_int_lift: bool,

    /// Apply bounded loop unrolling before CHC encoding.
    ///
    /// When enabled with --ay-chc, loops with a known unwind bound
    /// (`#[kani::unwind(N)]` or `--unwind N`) are unrolled into acyclic
    /// straight-line code before CHC encoding. This eliminates the need for
    /// PDR to synthesize loop invariants, which is critical for BV32+ types
    /// where invariant synthesis times out.
    #[arg(long, hide_short_help = true)]
    pub ay_chc_bounded_unroll: bool,

    /// Enable CHC transformation pipeline (experimental).
    ///
    /// When enabled with --ay-chc, applies transformations to CHC problems
    /// before solving. Available transforms: inline, scalarize, split-ite, split-or.
    /// Default without --ay-chc-transforms: scalarize, split-ite, split-or (safe set).
    /// Inline preprocessing is opt-in only (can cause PROOF→UNKNOWN regressions).
    #[arg(long, hide_short_help = true)]
    pub ay_chc_transform: bool,

    /// Select specific CHC transformations to apply (experimental).
    ///
    /// Comma-separated list: inline, scalarize, split-ite, split-or, all
    /// Requires --ay-chc-transform. Default: scalarize, split-ite, split-or.
    #[arg(long, value_delimiter = ',', hide_short_help = true)]
    pub ay_chc_transforms: Vec<String>,

    /// Disable post-solve verification for CHC results (opt-out).
    ///
    /// Skips model/counterexample verification after ay-chc-native produces results.
    /// Use for performance-sensitive runs where the solver is trusted.
    /// By default, verification is ON to catch spurious solver results.
    #[arg(long, hide_short_help = true)]
    pub ay_chc_skip_verify: bool,

    /// Use wide memory model with integrated bounds checking (experimental).
    ///
    /// When enabled, uses WideMemManager which embeds allocation sizes in pointers,
    /// enabling efficient bounds checking without separate allocation tracking.
    /// Size information travels with pointers through GEP operations.
    ///
    /// Benefits:
    /// - Bounds check at allocation time (size known when pointer created)
    /// - No lookup needed (size travels with pointer)
    /// - GEP preserves bounds (size decreases as pointer advances)
    /// - Cleaner CHC encoding (fewer auxiliary variables)
    ///
    /// Part of #1678: WideMemManager implementation.
    #[arg(long, visible_alias = "wide-mem", hide_short_help = true)]
    pub ay_wide_mem: bool,

    /// Use panic=unwind strategy instead of panic=abort.
    ///
    /// By default, trust-mc compiles with -C panic=abort which eliminates all unwind
    /// cleanup paths from MIR. When this flag is enabled, -C panic=unwind is used
    /// instead, preserving cleanup blocks with Resume/Abort terminators. This
    /// allows verification of Drop impls executed during panic unwinding.
    ///
    /// Part of #3301: Resume/Abort terminator CHC encoding.
    #[arg(long, hide_short_help = true)]
    pub ay_panic_unwind: bool,

    /// CBMC-only compatibility flag: SAT solver selection in upstream Kani.
    /// trust-mc uses AY so this flag is accepted for drop-in scripts and ignored with a warning.
    /// Hidden from --help.
    #[arg(long, hide = true, value_parser = parse_kani_solver_compat, value_name = "SOLVER")]
    pub solver: Option<String>,

    /// CBMC-only compatibility flag: variadic passthrough of CBMC arguments in upstream Kani.
    /// trust-mc discards these with a warning (Kani scripts may pass harmless flags). Hidden from --help.
    /// Matches upstream Kani's `--cbmc-args` signature: `num_args(0..)` + `allow_hyphen_values`.
    #[arg(long, hide = true, num_args = 0.., allow_hyphen_values = true)]
    pub cbmc_args: Vec<String>,

    /// CBMC-only compatibility flag: C-code generation in upstream Kani.
    /// trust-mc has no C backend so this flag is rejected with a friendly error. Hidden from --help.
    #[arg(long = "gen-c", hide = true)]
    pub gen_c: bool,

    /// CBMC-only compatibility flag: loop-contract synthesis in upstream Kani.
    /// trust-mc uses PDR invariant synthesis instead, so this flag is a no-op (warn).
    /// Hidden from --help.
    #[arg(long, hide = true)]
    pub synthesize_loop_contracts: bool,

    /// Kani compatibility flag: print LLBC (Lean backend) output. trust-mc has no Lean
    /// backend, so this flag is rejected with a friendly error. Hidden from --help.
    #[arg(long, hide = true)]
    pub print_llbc: bool,

    /// CBMC-only compatibility flag: disable CBMC formula slicing for debugging traces.
    /// trust-mc has no CBMC formula slicer, so this is a no-op (warn). Hidden from --help.
    #[arg(long, hide = true)]
    pub no_slice_formula: bool,

    /// CBMC-only compatibility flag: execute CBMC goto-program sanity checks.
    /// trust-mc has no CBMC goto-program, so this is a no-op (warn). Hidden from --help.
    #[arg(long, hide = true)]
    pub run_sanity_checks: bool,

    /// Obsolete Kani/CBMC debug flag for JSON symbol-table output.
    /// trust-mc has no CBMC symbol table, so this is rejected with a friendly error.
    #[arg(long, hide = true)]
    pub write_json_symtab: bool,

    #[command(flatten)]
    pub checks: CheckArgs,

    #[command(flatten)]
    pub common_args: CommonArgs,

    /// Arguments to pass down to Cargo
    #[command(flatten)]
    pub cargo: CargoCommonArgs,

    /// Arguments used to select Cargo target.
    #[command(flatten)]
    pub target: CargoTargetArgs,
}

impl VerificationArgs {
    pub(crate) fn restrict_vtable(&self) -> bool {
        self.common_args.unstable_features.contains(UnstableFeature::RestrictVtable)
            && !self.no_restrict_vtable
    }

    /// Assertion reachability checks should be disabled
    pub(crate) fn assertion_reach_checks(&self) -> bool {
        !self.no_assertion_reach_checks
    }

    /// Computes how many threads should be used to verify harnesses.
    pub(crate) fn jobs(&self) -> NumThreads {
        match self.jobs {
            None => NumThreads::NoMultithreading, // no argument, default 1
            Some(None) => NumThreads::ThreadPoolDefault, // -j
            Some(Some(x)) => NumThreads::UserSpecified(x), // -j=x
        }
    }

    fn is_function_contracts_enabled(&self) -> bool {
        self.common_args.unstable_features.contains(UnstableFeature::FunctionContracts)
    }

    /// Is experimental stubbing enabled?
    pub(crate) fn is_stubbing_enabled(&self) -> bool {
        self.common_args.unstable_features.contains(UnstableFeature::Stubbing)
            || self.is_function_contracts_enabled()
    }

    /// Reject CBMC-only compatibility flags with friendly errors (Kani drop-in CLI parity).
    ///
    /// - `--cbmc-args`:                 WARN and continue — Kani scripts may pass harmless CBMC flags, so we
    ///   discard them without aborting.
    /// - `--synthesize-loop-contracts`: WARN and continue — trust-mc uses PDR invariant synthesis,
    ///   so the CBMC loop-contract synthesizer is a no-op.
    /// - `--solver`:                    WARN and continue — trust-mc always uses its AY solver selection.
    /// - `--gen-c`:                     ERROR (exit 2) — trust-mc has no C-code backend.
    /// - `--print-llbc`:                ERROR (exit 2) — trust-mc has no Lean backend.
    /// - CBMC debug flags:              WARN and continue unless they request a missing artifact.
    ///
    /// Part of #4308, #4309, #4310, #4311, #4312.
    pub(crate) fn validate_cbmc_only_flags(&self) -> Result<(), Error> {
        // POSITIVE RECEIPT for --c-lib. A path that does not resolve used to be
        // accepted silently, so the C front-end ingested an EMPTY translation
        // unit and every extern call fell back to "undefined foreign function".
        // The verdict then looked like an ordinary encoder result, and a corpus
        // row could not distinguish "the C-body lane is inert" from "the C-body
        // lane was never reached" — a measurement that cannot fail is not
        // evidence. Fail loudly instead, naming the cwd, because these paths are
        // conventionally written RELATIVE to the crate/test root.
        for lib in &self.c_lib {
            if !lib.exists() {
                let cwd = std::env::current_dir()
                    .map(|d| d.display().to_string())
                    .unwrap_or_else(|_| "<unknown>".to_string());
                return Err(Error::raw(
                    clap::error::ErrorKind::ValueValidation,
                    format!(
                        "--c-lib path does not exist: {}\n                                  resolved relative to cwd: {cwd}\n                                  (a missing C library would otherwise be ingested as empty,                          silently turning every extern call into an undefined-function error)\n",
                        lib.display()
                    ),
                ));
            }
        }
        if !self.cbmc_args.is_empty() {
            warning(
                "--cbmc-args is CBMC-only and has been discarded by trust-mc.\n         \
                Use --ay-* flags for solver tuning.",
            );
        }
        if self.synthesize_loop_contracts {
            warning(
                "--synthesize-loop-contracts is a no-op in trust-mc (AY uses PDR invariant synthesis instead of CBMC loop contracts)",
            );
        }
        if let Some(solver) = &self.solver {
            warning(&format_args!(
                "--solver {solver} is CBMC-only and has been ignored by trust-mc. \
                Use --smt-solver (or --ay-solver) to configure AY solver selection.",
            ));
        }
        if self.gen_c {
            return Err(Error::raw(
                ErrorKind::InvalidValue,
                "--gen-c is CBMC-only (C-code generation) and not supported in trust-mc.\n",
            ));
        }
        if self.print_llbc {
            return Err(Error::raw(
                ErrorKind::InvalidValue,
                "--print-llbc is not supported: Lean backend not in trust-mc (see https://github.com/alabsystems/trust-mc)\n",
            ));
        }
        if self.no_slice_formula {
            warning("--no-slice-formula is CBMC-only and has been ignored by trust-mc.");
        }
        if self.run_sanity_checks {
            warning("--run-sanity-checks is CBMC-only and has been ignored by trust-mc.");
        }
        if self.write_json_symtab {
            return Err(Error::raw(
                ErrorKind::ValueValidation,
                "--write-json-symtab is obsolete and not supported in trust-mc.\n",
            ));
        }
        Ok(())
    }
}

fn parse_kani_solver_compat(value: &str) -> Result<String, String> {
    let is_binary_solver = value
        .strip_prefix("bin=")
        .is_some_and(|binary| !binary.is_empty() && !binary.contains('='));
    let is_named_solver = !value.contains('=') && SolverOption::from_str(value).is_ok();

    if is_binary_solver || is_named_solver {
        Ok(value.to_owned())
    } else {
        Err(
            "expected one of bitwuzla, cadical, cvc5, kissat, minisat, z3, or bin=<SAT_SOLVER_BINARY>"
                .to_owned(),
        )
    }
}
