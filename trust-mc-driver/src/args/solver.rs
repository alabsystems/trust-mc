// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT
//! Solver backend types and timeout parsers for trust-mc CLI arguments.

use std::str::FromStr;
use std::time::Duration;

use clap::ValueEnum;

/// Verification backend selection.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub(crate) enum Backend {
    /// Compatibility/default spelling for the current backend; currently resolves to AY
    #[default]
    Auto,
    /// AY SMT/CHC solver backend
    AY,
}

impl Backend {
    /// Resolve `Auto` to the concrete backend it aliases today.
    ///
    /// AY is the only verification backend today, so `auto` and `ay` resolve to
    /// the same backend.
    ///
    /// # Arguments
    /// * `ay_solver` - The configured AY solver.
    ///
    /// Returns an error if no backend is available.
    pub(crate) fn resolve(self, ay_solver: AYSolver) -> Result<Self, String> {
        match self {
            Backend::Auto | Backend::AY => {
                if which::which("ay").is_ok() || !ay_solver.requires_ay_binary() {
                    Ok(Backend::AY)
                } else {
                    #[cfg(feature = "ay-direct")]
                    let hint = "(direct available for testing via --ay-solver=direct)";
                    #[cfg(not(feature = "ay-direct"))]
                    let hint = "";
                    Err(format!(
                        "AY solver not found in PATH. Install ay for the AY backend.\n{hint}"
                    ))
                }
            }
        }
    }

    /// Check if this is the auto-select variant.
    pub(crate) fn is_auto(&self) -> bool {
        matches!(self, Backend::Auto)
    }
}

/// CHC auto-invariant candidate generation mode.
///
/// Controls whether trust-mc synthesizes additional PDR lemma-hint candidates from
/// range-style recursive CHC transitions before solving.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub(crate) enum AYChcAutoInvariantsMode {
    /// Disable driver-side auto-invariant candidate generation.
    #[default]
    Off,
    /// Generate range-style candidates from recursive transition constraints.
    Range,
    /// Generate the same candidate seeds as `range` for Houdini refinement.
    ///
    /// The CEGAR/Houdini filtering loop is implemented separately; this mode
    /// enables seed generation and diagnostics now.
    Houdini,
}

/// CHC proof-core distillation mode.
///
/// Controls whether trust-mc runs a pre-solve proof-core distillation stage
/// for canonical range-loop predicates. When enabled, bounded obligations
/// are solved with activation literals; unsat cores are lifted into
/// predicate-variable formulas and injected as hints after inductiveness
/// screening.
///
/// Part of #2875 (lane #20).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub(crate) enum AYChcProofCoreMode {
    /// Disable proof-core distillation (default). No behavior change.
    #[default]
    Off,
    /// Enable proof-core distillation for canonical range-loop predicates.
    Range,
}

/// ay-chc engine selection.
///
/// Controls which ay-chc engine is used for HORN logic files.
/// Auto (default) uses the adaptive portfolio solver. Pdr forces
/// the PDR engine only. BMC forces bounded model checking — more
/// effective for non-loop harnesses with heavy BV reasoning where
/// PDR invariant synthesis is overwhelmed.
///
/// Part of #3688.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub(crate) enum AYChcEngine {
    /// Auto-select: ay-chc adaptive portfolio (PDR/IC3, BMC, k-induction, etc.).
    #[default]
    Auto,
    /// Force the ay-chc PDR engine only.
    Pdr,
    /// Force BMC (Bounded Model Checking) engine.
    /// Best for non-loop harnesses with complete BV encodings.
    Bmc,
}

/// SMT solver selection for the AY backend.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub(crate) enum AYSolver {
    /// Select solver automatically (uses ay native - the only production solver).
    #[default]
    Auto,
    /// Force ay native (default production solver).
    AY,
    /// Use direct AY linking (requires ay-direct feature).
    /// Eliminates subprocess spawning and text file interchange.
    #[cfg(feature = "ay-direct")]
    Direct,
}

impl AYSolver {
    /// Returns true if this solver selection requires the ay binary to be installed.
    ///
    /// - `Auto` and `AY` require the ay binary
    /// - `Direct` uses direct linking (no subprocess) — only available with `ay-direct` feature
    pub(crate) fn requires_ay_binary(self) -> bool {
        match self {
            AYSolver::Auto | AYSolver::AY => true,
            #[cfg(feature = "ay-direct")]
            AYSolver::Direct => false,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, strum_macros::EnumString)]
pub(super) enum TimeUnit {
    #[strum(serialize = "s")]
    Seconds,
    #[strum(serialize = "m")]
    Minutes,
    #[strum(serialize = "h")]
    Hours,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Timeout {
    value: u32,
    unit: TimeUnit,
}

impl FromStr for Timeout {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let last_char = s.chars().last().ok_or("Empty timeout value")?;
        let (value_str, unit_str) = if last_char.is_ascii_digit() {
            // no suffix
            (s, "s")
        } else {
            s.split_at(s.len() - 1)
        };
        let value = value_str.parse::<u32>().map_err(|_| "Invalid timeout value")?;

        let unit = TimeUnit::from_str(unit_str).map_err(
            |_| "Invalid time unit. Use 's' for seconds, 'm' for minutes, or 'h' for hours",
        )?;

        Ok(Timeout { value, unit })
    }
}

impl From<Timeout> for Duration {
    fn from(timeout: Timeout) -> Self {
        match timeout.unit {
            TimeUnit::Seconds => Duration::from_secs(timeout.value as u64),
            TimeUnit::Minutes => Duration::from_secs(timeout.value as u64 * 60),
            TimeUnit::Hours => Duration::from_secs(timeout.value as u64 * 3600),
        }
    }
}

#[derive(PartialEq, Debug, Clone, Copy)]
pub(crate) enum NumThreads {
    /// The user specified a specific number of threads to use (the `-j [COUNT]` option).
    UserSpecified(usize),
    /// The user asked for multithreading, but didn't specify exactly how much (the `-j` option).
    ThreadPoolDefault,
    /// The user didn't ask for any multithreading (default).
    NoMultithreading,
}

impl NumThreads {
    pub(crate) fn will_multithread(&self) -> bool {
        matches!(self, Self::UserSpecified(x) if *x != 1) || matches!(self, Self::ThreadPoolDefault)
    }
}

/// Mode for concrete playback test generation.
///
/// When verification finds a counterexample, concrete playback generates
/// a unit test that reproduces the failure with concrete input values.
/// Requires `-Z concrete-playback` unstable feature.
#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum)]
pub(crate) enum ConcretePlaybackMode {
    /// Print generated tests to stdout.
    ///
    /// Displays the unit test code for manual copy/paste into source files.
    /// Useful for reviewing tests before adding them to the codebase.
    Print,
    /// Automatically insert tests into source files.
    ///
    /// Modifies the original source file to add the generated unit test.
    /// The test is inserted near the harness that produced the counterexample.
    #[value(name = "inplace")]
    InPlace,
}

/// Output format for verification results.
///
/// Controls how verification results are displayed to the user.
/// The default is `Regular` which shows formatted property verification results.
#[derive(Clone, Debug, PartialEq, Eq, ValueEnum)]
pub(crate) enum OutputFormat {
    /// Standard formatted output (default).
    ///
    /// Shows formatted verification results including property names, status,
    /// and diagnostic messages. Provides the most readable output for
    /// interactive use.
    Regular,
    /// Minimal output for parallel execution.
    ///
    /// Suppresses most messages to reduce output noise when running
    /// multiple harnesses in parallel with `--jobs`. Required when
    /// using `--jobs` with more than one thread.
    Terse,
    /// Raw backend output (legacy mode).
    ///
    /// Passes through raw AY output without formatting.
    /// Not compatible with `--concrete-playback`.
    /// Primarily for debugging backend integration.
    Old,
}

#[derive(Debug, clap::Args)]
#[clap(next_help_heading = "Memory Checks")]
pub(crate) struct CheckArgs {
    /// Turn off all default checks
    #[arg(long)]
    pub no_default_checks: bool,

    /// Turn off default memory safety checks
    #[arg(long)]
    pub no_memory_safety_checks: bool,

    /// Turn off default overflow checks
    #[arg(long)]
    pub no_overflow_checks: bool,

    /// Turn off undefined function checks
    #[arg(long)]
    pub no_undefined_function_checks: bool,

    /// Turn off default unwinding checks
    #[arg(long)]
    pub no_unwinding_checks: bool,

    /// Check that floating-point operations do not GENERATE NaN (Kani's
    /// `--nan-check`). Opt-in, matching Kani: NaN generation is legal Rust, so
    /// it is only a defect when the program intends otherwise.
    ///
    /// The compiler has always had this flag (`nan_checks`), but nothing
    /// forwarded it, so it was unreachable from the driver — which silently
    /// made `tools/soundness-duals/fastmath_dual_nan.rs` and
    /// `fastmath_dual_mul_div.rs` VACUOUS: they verified because the NaN
    /// obligation was never emitted at all (`grep -i nan` over their check
    /// lists returns nothing), not because the program was proven safe.
    #[arg(long)]
    pub nan_check: bool,
}
