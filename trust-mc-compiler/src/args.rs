// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

use strum_macros::{AsRefStr, EnumString, VariantNames};
use tracing_subscriber::filter::Directive;
pub(crate) use trust_mc_metadata::{ChcStepMode, ChcTrackLevel};

#[derive(Debug, Default, Clone, Copy, AsRefStr, EnumString, VariantNames, PartialEq, Eq)]
#[strum(serialize_all = "snake_case")]
pub(crate) enum ReachabilityType {
    /// Start the cross-crate reachability analysis from all harnesses in the local crate.
    Harnesses,
    /// Don't perform any reachability analysis. This will skip codegen for this crate.
    #[default]
    None,
    /// Start the cross-crate reachability analysis from all public functions in the local crate.
    PubFns,
    /// Start the cross-crate reachability analysis from all functions in the local crate.
    /// Currently, this mode is only used for automatic harness generation.
    AllFns,
}

/// Command line arguments that this instance of the compiler run was called
/// with. Usually stored in and accessible via [`crate::kani_queries::QueryDb`].
#[derive(Debug, Default, Clone, clap::Parser)]
pub(crate) struct Arguments {
    /// Option used to disable asserting function contracts.
    #[clap(long)]
    pub no_assert_contracts: bool,
    /// Option name used to enable assertion reachability checks.
    #[clap(long = "assertion-reach-checks")]
    pub check_assertion_reachability: bool,
    /// Option name used to enable coverage checks.
    #[clap(long = "coverage-checks")]
    pub check_coverage: bool,
    /// Option name used to dump function pointer restrictions.
    #[clap(long = "restrict-vtable-fn-ptrs")]
    pub emit_vtable_restrictions: bool,
    /// Option name used to use json pretty-print for output files.
    #[clap(long = "pretty-json-files")]
    pub output_pretty_json: bool,
    /// When specified, the harness filter will only match the exact fully qualified name of a harness.
    // (Passed here directly from [CargoKaniArgs] in `args_toml.rs`)
    #[arg(long, requires("harnesses"))]
    pub exact: bool,
    /// If specified, only run harnesses that match this filter. This option can be provided
    /// multiple times, which will run all tests matching any of the filters.
    /// If used with --exact, the harness filter will only match the exact fully qualified name of a harness.
    // (Passed here directly from [CargoKaniArgs] in `args_toml.rs`)
    #[arg(long = "harness", num_args(1), value_name = "HARNESS_FILTER")]
    pub harnesses: Vec<String>,
    /// Specify the value used for loop unwinding (default for all harnesses).
    ///
    /// Used by the AY backend for bounded loop unrolling.
    #[arg(long)]
    pub default_unwind: Option<u32>,
    /// Specify the value used for loop unwinding for the specified harness.
    ///
    /// Requires `--harness` to select the target harness. Used by the AY backend for bounded loop unrolling.
    #[arg(long, requires("harnesses"))]
    pub unwind: Option<u32>,
    /// Option used for suppressing global ASM error.
    #[clap(long)]
    pub ignore_global_asm: bool,
    /// Emit compiler metadata for list commands without generating per-harness
    /// verification conditions.
    #[clap(long)]
    pub list_metadata_only: bool,
    /// Compute verification results under the assumption that no panic occurs.
    /// This feature is unstable, and it requires `-Z unstable-options` to be used
    #[clap(long)]
    pub prove_safety_only: bool,
    /// Option name used to select which reachability analysis to perform.
    #[clap(long = "reachability", default_value = "none")]
    pub reachability_analysis: ReachabilityType,
    #[clap(long = "enable-stubbing")]
    pub stubbing_enabled: bool,
    /// Option name used to define unstable features.
    #[clap(short = 'Z', long = "unstable")]
    pub unstable_features: Vec<String>,
    #[clap(long)]
    /// Option used for building standard library.
    ///
    /// Flag that indicates that we are currently building the standard library.
    /// Note that `kani` library will not be available if this is `true`.
    pub build_std: bool,
    #[clap(long)]
    /// Option name used to set log level.
    pub log_level: Option<Directive>,
    #[clap(long)]
    /// Option name used to set the log output to a json file.
    pub json_output: bool,
    #[clap(long, conflicts_with = "json_output")]
    /// Option name used to force logger to use color output. This doesn't work with --json-output.
    pub color_output: bool,
    #[clap(long)]
    /// Pass the kani version to the compiler to ensure cache coherence.
    check_version: Option<String>,
    #[clap(long)]
    pub ub_check: Vec<ExtraChecks>,
    /// Turn off all default checks.
    ///
    /// Used by the AY backend to disable unwinding assertions when default checks are disabled.
    #[arg(long)]
    pub no_default_checks: bool,
    /// Turn off default memory safety checks.
    #[arg(long)]
    pub no_memory_safety_checks: bool,
    /// Turn off default arithmetic overflow checks.
    #[arg(long)]
    pub no_overflow_checks: bool,
    /// Turn off undefined foreign function checks.
    #[arg(long)]
    pub no_undefined_function_checks: bool,
    /// C source/library files supplied with `--c-lib` (requires `-Z c-ffi`).
    ///
    /// The encoder uses these only to answer a GATING question: does a
    /// definition for an `extern "C"` symbol exist somewhere on this run? A
    /// symbol nobody supplied keeps Kani's fail-closed `assert(false)`; a
    /// symbol the user did supply is modelled with a sound effect frame.
    #[arg(long = "c-lib", num_args(1), value_name = "C_LIB")]
    pub c_lib: Vec<String>,
    /// Emit NaN-generation obligations for float arithmetic (opt-in).
    ///
    /// OFF by default. Kani's default is ON (kani-driver passes CBMC
    /// `--nan-check` whenever overflow checks are on); trust-mc's differs
    /// deliberately, see the driver's `--nan-check`. Producing a NaN is
    /// DEFINED behaviour in Rust, not UB.
    #[arg(long = "nan-check")]
    pub nan_checks: bool,
    /// Turn off default unwinding checks.
    ///
    /// Used by the AY backend to disable unwinding assertions.
    #[arg(long)]
    pub no_unwinding_checks: bool,
    /// Use the abstract IR emission path for AY backend.
    ///
    /// When enabled, uses `emit_bmc(bmc_vc)` to generate the AY program from the
    /// abstract BMC verification condition instead of direct program construction.
    /// This is the target architecture for cleaner MIR → trust_mc_core IR → AY separation.
    /// Experimental feature for testing the new codegen path.
    #[arg(long)]
    pub ay_emit_bmc: bool,
    /// Enable CHC (Constrained Horn Clause) mode for AY backend.
    ///
    /// When enabled, emits CHC relations and Horn rules (per-block relations with
    /// per-edge rules plus an `error` relation) and sets `(set-logic HORN)` in the
    /// SMT output (unless overridden by `--ay-logic`), targeting CHC solvers like
    /// PDR/PDR for unbounded verification.
    ///
    /// **Current status (experimental):**
    /// - Uses true CHC encoding (relations + Horn rules)
    /// - Solver limitations still apply (e.g., some fixedpoint engines may require
    ///   concrete bounds for certain patterns), which is a solver constraint, not
    ///   a codegen fallback
    #[arg(long)]
    pub ay_chc: bool,
    /// Enable CHC debug tracing (prints verbose CHC encoding details).
    ///
    /// Intended for debugging CHC encoding issues; avoid enabling in CI runs.
    #[arg(long, hide_short_help = true)]
    pub ay_chc_debug: bool,
    /// Override the SMT-LIB logic for AY backend.
    ///
    /// By default, logic is selected automatically based on mode and features.
    /// Use this option to force a specific logic for experimentation.
    #[arg(long)]
    pub ay_logic: Option<String>,
    /// CHC memory tracking precision level.
    ///
    /// Controls how memory operations are modeled in CHC encoding:
    /// - `reg`: Register-only, loads havoc, stores no-op (loses ref chains)
    /// - `ptr`: Pointer validity, loads havoc but emits r_ok checks
    /// - `mem` (default): Full memory, uses select/store for complete modeling
    ///
    /// Only effective when `--ay-chc` is enabled.
    /// Part of #2214: Default changed from `reg` to `mem`. Reg-level havoces
    /// loads through references, producing spurious counterexamples for any
    /// code using iterator patterns (Range::next() takes &mut self).
    #[arg(long, value_enum, default_value_t = ChcTrackLevel::Mem)]
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
    #[arg(long, value_enum, default_value_t = ChcStepMode::Auto)]
    pub ay_chc_step: ChcStepMode,
    /// Lift bitvector sorts to integer sorts for loop-header CHC predicates.
    ///
    /// When enabled, loop-header relation parameters use Int sorts instead of
    /// BitVec, letting PDR synthesize invariants in LIA (linear integer
    /// arithmetic) instead of BV theory. Adds bv2int/int2bv conversions at
    /// rule boundaries. Only effective when `--ay-chc` is enabled.
    ///
    /// Part of #112: designs/2026-03-03-loop-invariant-synthesis.md Direction 2.
    #[arg(long)]
    pub ay_chc_int_lift: bool,
    /// Use wide memory model with integrated bounds checking.
    ///
    /// When enabled, uses WideMemManager which embeds allocation sizes in pointers,
    /// enabling efficient bounds checking without separate allocation tracking.
    /// Size information travels with pointers through GEP operations.
    ///
    /// Part of #1678: WideMemManager implementation.
    #[arg(long)]
    pub ay_wide_mem: bool,
    /// Enable extra pointer checks (offset overflow). Part of #3176.
    #[arg(long)]
    pub extra_pointer_checks: bool,
    /// Apply bounded loop unrolling before CHC encoding.
    ///
    /// When enabled in CHC mode (`--ay-chc`), loops with a known unwind bound
    /// (`#[kani::unwind(N)]` or `--unwind N`) are unrolled into acyclic
    /// straight-line code before CHC encoding, eliminating the need for PDR
    /// to synthesize loop invariants. This is critical for BV32+ types where
    /// PDR's invariant synthesis times out.
    ///
    /// Without this flag, CHC mode always encodes loops as recursive predicates,
    /// relying on the solver for invariant synthesis.
    #[arg(long)]
    pub ay_chc_bounded_unroll: bool,
    /// Per-harness translation budget, in milliseconds.
    ///
    /// trust-mc-driver derives it from `--harness-timeout`. Codegen of one
    /// harness (reachability, MIR transforms, MIR-to-CHC translation, emit-time
    /// optimization) that outlives its budget stops, and the harness is
    /// reported UNKNOWN with reason `TranslationTimeout` instead of the whole
    /// process running into the driver's watchdog. Absent means no budget.
    /// See `codegen_ay::translation_deadline::per_harness_budget`.
    #[arg(long)]
    pub translation_timeout_ms: Option<u64>,
    /// If we are running the autoharness subcommand, the paths to include.
    /// See kani_driver::autoharness_args for documentation.
    #[arg(long = "autoharness-include-pattern", num_args(1))]
    pub autoharness_included_patterns: Vec<String>,
    /// If we are running the autoharness subcommand, the paths to exclude.
    /// See kani_driver::autoharness_args for documentation.
    #[arg(long = "autoharness-exclude-pattern", num_args(1))]
    pub autoharness_excluded_patterns: Vec<String>,
}

#[derive(Debug, Clone, Copy, AsRefStr, EnumString, VariantNames, PartialEq, Eq)]
#[strum(serialize_all = "snake_case")]
pub(crate) enum ExtraChecks {
    /// Check that produced values are valid except for uninitialized values.
    /// See <https://github.com/model-checking/kani/issues/920>.
    Validity,
    /// Check for using uninitialized memory.
    Uninit,
}

impl Arguments {
    /// The `--check-version` trust-mc-driver always sends; `None` when the
    /// arguments did not come from the driver.
    pub(crate) fn check_version(&self) -> Option<&str> {
        self.check_version.as_deref()
    }
}

/// Why `-C llvm-args` did not yield engine [`Arguments`].
#[derive(Debug)]
pub(crate) enum LlvmArgsError {
    /// A malformed `pct1` group (`trust_mc_metadata::engine_args`).
    Channel(trust_mc_metadata::engine_args::EngineArgsError),
    /// The decoded argv is not a valid engine command line.
    Clap(clap::Error),
}

/// Parse the engine arguments from rustc's `-C llvm-args` values, after a
/// synthetic program name, exactly as the old `Callbacks::config` did.
///
/// The values are first decoded with
/// [`trust_mc_metadata::engine_args::decode_llvm_args`]: trust-mc-driver's
/// Trustc route sends each engine argv as a counted `pct1` group, so a path with
/// whitespace survives rustc's `split_whitespace`. Tokens outside a group (the
/// DevCli form, which never encodes) come back unchanged.
///
/// Returns the error instead of exiting, so the backend can report it as a
/// fatal rustc diagnostic inside a host compiler.
pub(crate) fn parse_llvm_args(llvm_args: &[String]) -> Result<Arguments, LlvmArgsError> {
    use clap::Parser;
    let argv = trust_mc_metadata::engine_args::decode_llvm_args(llvm_args)
        .map_err(LlvmArgsError::Channel)?;
    Arguments::try_parse_from(
        std::iter::once("trust_mc-compiler").chain(argv.iter().map(String::as_str)),
    )
    .map_err(LlvmArgsError::Clap)
}

/// An engine-argument error as the text of one rustc diagnostic: without clap's
/// own `error: ` prefix (rustc prints one) and without trailing blank lines.
pub(crate) fn render_llvm_args_error(err: &LlvmArgsError) -> String {
    match err {
        LlvmArgsError::Channel(err) => err.to_string(),
        LlvmArgsError::Clap(err) => {
            let text = err.to_string();
            let text = text.trim_end();
            text.strip_prefix("error: ").unwrap_or(text).to_owned()
        }
    }
}

/// What rustc hands the engine in `cg.llvm_args` on trust-mc-driver's Trustc
/// route (`tests/trust-lane/engine-args/<name>.llvm-args`), recorded from the
/// driver's own argv composition. The driver test
/// `compiler_route_trustc_llvm_args_match_the_engine_fixtures` fails when the
/// driver stops producing exactly these lists, so the two sides cannot drift.
#[cfg(test)]
pub(crate) fn trustc_route_llvm_args_fixture(name: &str) -> Vec<String> {
    let text = match name {
        "standalone" => include_str!("../../tests/trust-lane/engine-args/standalone.llvm-args"),
        "cargo-dependency" => {
            include_str!("../../tests/trust-lane/engine-args/cargo-dependency.llvm-args")
        }
        "cargo-local" => include_str!("../../tests/trust-lane/engine-args/cargo-local.llvm-args"),
        _ => unreachable!("no fixture {name}"),
    };
    text.lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| line.replace("@CARGO_PKG_VERSION@", env!("CARGO_PKG_VERSION")))
        .collect()
}

#[cfg(test)]
mod llvm_args_tests {
    use super::*;
    use clap::Parser;

    /// What `trust-mc-driver` puts in `-Cllvm-args` for a single-file run
    /// (`util::encode_as_rustc_arg` joins them with spaces; rustc splits them
    /// back into `cg.llvm_args`), in the BMC and the `--ay-chc` lane.
    const DRIVER_FLAG_LISTS: &[&str] = &[
        "--check-version=0.7.0 --log-level=warn --assertion-reach-checks --reachability=harnesses",
        "--check-version=0.7.0 --log-level=warn --assertion-reach-checks --reachability=harnesses --ay-chc --harness check_u8 --exact",
        "--ignore-global-asm --build-std",
    ];

    #[test]
    fn init_parses_llvm_args() {
        for list in DRIVER_FLAG_LISTS {
            let llvm_args: Vec<String> = list.split_whitespace().map(str::to_owned).collect();
            let parsed = parse_llvm_args(&llvm_args).expect("the driver's flag list parses");
            let config = Arguments::parse_from(
                std::iter::once("trust_mc-compiler").chain(llvm_args.iter().map(String::as_str)),
            );
            assert_eq!(format!("{parsed:?}"), format!("{config:?}"), "for {list}");
        }
    }

    #[test]
    fn unknown_llvm_arg_is_returned_not_exited() {
        let err = parse_llvm_args(&["--no-such-flag".to_owned()])
            .expect_err("an unknown engine argument is an error");
        let text = render_llvm_args_error(&err);
        assert!(text.contains("--no-such-flag"), "{text}");
        assert!(!text.starts_with("error: "), "{text}");
    }

    fn assert_driver_fixture_args(args: &Arguments, what: &str) {
        assert_eq!(args.c_lib, ["/opt/Application Support/stub.o"], "{what}: {args:?}");
        assert_eq!(args.harnesses, ["check_add"], "{what}: {args:?}");
        assert_eq!(args.default_unwind, Some(3), "{what}: {args:?}");
        assert!(args.check_assertion_reachability, "{what}: {args:?}");
        assert_eq!(args.reachability_analysis, ReachabilityType::Harnesses, "{what}: {args:?}");
        assert_eq!(args.check_version(), Some(env!("CARGO_PKG_VERSION")), "{what}: {args:?}");
    }

    #[test]
    fn init_decodes_the_trustc_route_standalone_llvm_args() {
        let llvm_args = trustc_route_llvm_args_fixture("standalone");
        let args = parse_llvm_args(&llvm_args).expect("the driver's Trustc argv parses");
        assert_driver_fixture_args(&args, "standalone");
    }

    #[test]
    fn init_decodes_the_trustc_route_cargo_groups_in_either_order() {
        let dependency = trustc_route_llvm_args_fixture("cargo-dependency");
        let local = trustc_route_llvm_args_fixture("cargo-local");
        for (first, second) in [(&dependency, &local), (&local, &dependency)] {
            let llvm_args: Vec<String> = first.iter().chain(second).cloned().collect();
            let args = parse_llvm_args(&llvm_args).expect("the concatenated groups parse");
            assert_driver_fixture_args(&args, "cargo");
        }
    }

    #[test]
    fn malformed_pct1_group_is_returned_not_exited() {
        for llvm_args in [
            vec!["--trust-mc-engine-args=pct1".to_owned(), "--log-level=warn".to_owned()],
            vec!["--trust-mc-engine-args=pct1:2".to_owned(), "--log-level=warn".to_owned()],
            vec!["--trust-mc-engine-args=pct1:1".to_owned(), "%zz".to_owned()],
        ] {
            let err = parse_llvm_args(&llvm_args).expect_err("a malformed group is an error");
            assert!(matches!(err, LlvmArgsError::Channel(_)), "{llvm_args:?}: {err:?}");
            assert!(!render_llvm_args_error(&err).is_empty());
        }
    }
}
