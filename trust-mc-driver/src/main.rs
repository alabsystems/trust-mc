// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

// Copyright Kani Contributors
// SPDX-License-Identifier: Apache-2.0 OR MIT

// Test code uses unwrap/panic freely — only enforce in production code
#![cfg_attr(test, allow(clippy::unwrap_used, clippy::panic))]

use std::ffi::OsString;
use std::process::ExitCode;

use anyhow::{Context, Result};
use autoharness::{autoharness_cargo, autoharness_standalone};
use time::{OffsetDateTime, format_description};

use args::{CargoKaniSubcommand, check_is_valid};
use args_toml::join_args;

use crate::args::StandaloneSubcommand;
use crate::args::list_args::Format;
use crate::concrete_playback::playback::{playback_cargo, playback_standalone};
use crate::list::collect_metadata::{
    list_cargo, list_cargo_with_format, list_standalone, list_standalone_with_format,
};
use crate::project::Project;
use crate::session::KaniSession;
use crate::util::warning;
use crate::version::{print_kani_version, print_machine_readable_sha, print_version_authority};
use clap::{CommandFactory, Parser};
use tracing::debug;
// Cargo passes the package library to the binary when both targets are built.
// The CLI is intentionally still a standalone driver while the library exposes
// the native integration facade for embedders.
use trust_mc_driver as _;

mod args;
mod args_toml;
mod autoharness;
#[cfg(feature = "ay-direct")]
mod ay_direct;
mod ay_parse;
mod call_ay;
// Shared CHC auto-invariant implementation (same file the LIBRARY crate
// compiles as `trust_mc_driver::chc_auto_hints`); the CLI's
// `call_ay::chc::{auto_invariants, sort_helpers}` shims re-export from it.
mod call_cargo;
mod call_single_file;
#[cfg(feature = "ay-chc-native")]
mod chc_auto_hints;
mod concrete_playback;
mod coverage;
mod ctrex_classify;
#[cfg(test)]
mod ctrex_classify_tests;
mod deadline;
mod demotion;
mod harness_runner;
mod list;
mod metadata;
mod project;
mod proof_summary;
mod property_model;
mod raw_io;
mod result_summary;
mod sarif;
mod session;
mod smt_io;
#[cfg(test)]
mod soundness_ledger_tests;
mod subprocess_tracker;
#[cfg(test)]
mod test_support;
mod trust_vc_bundle;
mod unknown_quality;
mod unsoundness_counts;
mod unsoundness_extract;
mod unsoundness_extract_fail_closed;
#[cfg(test)]
mod unsoundness_extract_tests;
mod util;
mod verification_provenance;
mod verification_result;
mod version;
mod wall_clock_watchdog;

/// The main function for the `trust-mc-driver`.
/// The driver can be invoked via `cargo trust-mc` and `trust-mc` commands, which determines what kind of
/// project should be verified. Legacy `cargo kani`/`kani` invocations are also supported.
fn main() -> ExitCode {
    // Reset SIGPIPE to default behavior to avoid panic when piping to head/tail (#663)
    // This allows graceful exit when the consumer closes stdout early.
    #[cfg(unix)]
    {
        // SAFETY: signal() is safe to call with valid signal number (SIGPIPE) and handler
        // (SIG_DFL). This runs before any other threads are spawned, ensuring no races.
        unsafe {
            libc::signal(libc::SIGPIPE, libc::SIG_DFL);
        }
    }

    // Activate ay's process-wide RSS memory guard. Without this, the in-process
    // CHC solver (AdaptivePortfolio with 12 parallel engines) has no memory bound
    // and concurrent trust-mc-driver processes can OOM the system.
    #[cfg(all(feature = "ay-chc-native", feature = "ay-memory-limit"))]
    {
        let limit = ay_sys::default_memory_limit();
        if limit > 0 {
            ay_sys::set_process_memory_limit(limit);
        }
    }

    // Intercept the machine-readable version probe BEFORE clap parsing so
    // the `scripts/cargo-trust-mc` staleness check can query an installed
    // binary without depending on any particular clap configuration, and so
    // this flag works even if clap would otherwise reject it in the current
    // subcommand context. Consumed by `scripts/cargo-trust-mc`.
    //
    // This is a hidden flag — do not document it in user-facing help.
    if std::env::args().any(|arg| arg == "--trust_mc-version-sha") {
        print_machine_readable_sha();
        return ExitCode::SUCCESS;
    }

    let argv: Vec<OsString> = std::env::args_os().collect();

    // Install the driver-side wall-clock watchdog BEFORE any subprocess work
    // begins (rustc, trust-mc-compiler, ay). Some MIR→CHC translation paths and
    // post-AY cleanup paths can hang indefinitely; `--harness-timeout` alone
    // is only honored at the AY call boundary, so a translation-time loop
    // would otherwise be SIGKILL'd by the test runner and produce a spurious
    // ERROR (missing_verdict). The watchdog emits a clean UNKNOWN final
    // marker and exits.
    wall_clock_watchdog::install_from_argv(&argv);

    let invocation_type = determine_invocation_type(argv);

    let result = match invocation_type {
        InvocationType::CargoKani { args, identity } => cargokani_main(args, identity),
        InvocationType::Standalone { identity } => standalone_main(identity),
    };

    if let Err(error) = result {
        // We are using the debug format for now to print the all the context.
        // We should consider creating a standard for error reporting.
        debug!(?error, "main_failure");
        util::error(&format_args!("{error:#}"));
        ExitCode::FAILURE
    } else {
        ExitCode::SUCCESS
    }
}

/// The main function for the `cargo trust-mc` (or legacy `cargo kani`) command.
fn cargokani_main(input_args: Vec<OsString>, identity: CliIdentity) -> Result<()> {
    if print_clap_identity_output_if_requested::<args::CargoKaniArgs>(
        &input_args,
        identity.cargo_binary_name(),
    )? {
        return Ok(());
    }
    let input_args = join_args(input_args)?;
    let args = args::CargoKaniArgs::parse_from(&input_args);
    if args.version_authority {
        print_version_authority(InvocationType::CargoKani { args: input_args, identity })?;
        return Ok(());
    }
    check_is_valid(&args);

    if args.list_harnesses {
        return list_cargo_with_format(Format::Pretty, args.verify_opts, identity);
    }

    let mut session = match args.command {
        Some(CargoKaniSubcommand::Autoharness(autoharness_args)) => {
            return autoharness_cargo(*autoharness_args, identity);
        }
        Some(CargoKaniSubcommand::List(list_args)) => {
            return list_cargo(*list_args, args.verify_opts, identity);
        }
        Some(CargoKaniSubcommand::Playback(args)) => {
            return playback_cargo(*args);
        }
        None => session::KaniSession::new(args.verify_opts)?,
    };

    if !session.args.common_args.quiet {
        print_kani_version(InvocationType::CargoKani { args: input_args, identity });
    }

    if let Some(bundle_path) = session.args.trust_vc_bundle.clone() {
        return trust_vc_bundle::verify_trust_vc_bundle(session, &bundle_path);
    }

    let project = project::cargo_project(&mut session, false)?;
    if session.args.only_codegen { Ok(()) } else { verify_project(project, session) }
}

/// The main function for the `kani` command.
fn standalone_main(identity: CliIdentity) -> Result<()> {
    let input_args: Vec<OsString> = std::env::args_os().collect();
    if print_clap_identity_output_if_requested::<args::StandaloneArgs>(
        &input_args,
        identity.standalone_binary_name(),
    )? {
        return Ok(());
    }
    let args = args::StandaloneArgs::parse_from(&input_args);
    if args.version_authority {
        print_version_authority(InvocationType::Standalone { identity })?;
        return Ok(());
    }
    check_is_valid(&args);

    if args.list_harnesses {
        let input = args.input.context("standalone mode requires input file")?;
        return list_standalone_with_format(
            input,
            args.crate_name,
            false,
            Format::Pretty,
            args.verify_opts,
            identity,
        );
    }

    let (session, project) = match args.command {
        Some(StandaloneSubcommand::Autoharness(args)) => {
            return autoharness_standalone(*args, identity);
        }
        Some(StandaloneSubcommand::Playback(args)) => return playback_standalone(*args),
        Some(StandaloneSubcommand::List(list_args)) => {
            return list_standalone(*list_args, args.verify_opts, identity);
        }
        Some(StandaloneSubcommand::VerifyStd(args)) => {
            let session = KaniSession::new(args.verify_opts)?;
            if !session.args.common_args.quiet {
                print_kani_version(InvocationType::Standalone { identity });
            }

            let project = project::std_project(&args.std_path, &session)?;
            (session, project)
        }
        None => {
            let session = KaniSession::new(args.verify_opts)?;
            if !session.args.common_args.quiet {
                print_kani_version(InvocationType::Standalone { identity });
            }

            if let Some(bundle_path) = session.args.trust_vc_bundle.clone() {
                return trust_vc_bundle::verify_trust_vc_bundle(session, &bundle_path);
            }

            let input = args.input.context("standalone mode requires input file")?;
            let project = project::standalone_project(&input, args.crate_name, &session)?;
            (session, project)
        }
    };
    if session.args.only_codegen { Ok(()) } else { verify_project(project, session) }
}

/// Report iterator unsoundness warnings if any counters are non-zero (#1929).
///
/// Checks the project metadata for iterator verification that was skipped due to
/// sort mismatches. Non-zero counts indicate UNSOUND verification results.
///
/// This function is called BEFORE verification results are displayed to ensure
/// users see the unsoundness warning before interpreting results.
fn report_iterator_unsoundness_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.iterator_unsoundness
            && info.has_unsoundness()
        {
            let total = info.total_skip_count();
            warning(&format_args!(
                "UNSOUND: Iterator verification skipped {} time(s). \
                     Iterator constraints were lost due to sort mismatches - \
                     loops may explore fewer states than required. \
                     (CHC skipped: {}, BMC skipped: {}). \
                     Consider using explicit loop bounds or simpler iterator patterns.",
                total, info.chc_skip_count, info.bmc_skip_count
            ));
        }
    }
}

/// Report BigInt unsoundness warnings if any counters are non-zero (#1989).
///
/// Checks the project metadata for BigInt verification that was skipped due to
/// sort mismatches. Non-zero counts indicate UNSOUND verification results.
///
/// This function is called BEFORE verification results are displayed to ensure
/// users see the unsoundness warning before interpreting results.
fn report_bigint_unsoundness_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.bigint_unsoundness
            && info.has_unsoundness()
        {
            warning(&format_args!(
                "UNSOUND: BigInt verification skipped {} time(s). \
                     BigInt constraints were lost due to sort mismatches or translation failures - \
                     BigInt arithmetic may not be properly verified. \
                     This may indicate a type inference issue in BigInt stub handling.",
                info.chc_skip_count
            ));
        }
    }
}

/// Report dropped `kani::assume` semantics warnings if any counters are non-zero (#2584).
///
/// Checks metadata for CHC paths where `kani::assume` guards were not enforced
/// and codegen fell back to unconstrained transitions.
fn report_assume_dropped_transition_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.assume_dropped_transitions
            && info.has_drops()
        {
            warning(&format_args!(
                "UNSOUND: CHC dropped {} kani::assume constraint(s). \
                     Some assume guards were not encoded and verification \
                     proceeded with unconstrained transitions. \
                     See metadata field `assume_dropped_transitions.count`.",
                info.count
            ));
        }
    }
}

/// Build a CHC fallback unsoundness warning message.
fn format_chc_fallback_warning(total_count: usize, harness_count: usize) -> String {
    format!(
        "UNSOUND: CHC type/size fallbacks triggered {} time(s) across {} harness(es). \
             Verification used hard-coded defaults for unresolved types/sizes, \
             which may miss bugs or prove incorrect properties. \
             See metadata field `chc_fallbacks.per_harness` for affected harnesses.",
        total_count, harness_count
    )
}

/// Report CHC fallback warnings if any fallback counters are non-zero (#2234).
///
/// Checks metadata for unresolved CHC type/size fallbacks. Non-zero counts indicate
/// verification proceeded with hard-coded defaults and may be unsound.
fn report_chc_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.chc_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_chc_fallback_warning(info.total_count, info.per_harness.len()));
        }
    }
}

/// Report CHC coerce-eq dropped constraint warnings if any drops occurred (#2235).
///
/// Checks metadata for call-result equality constraints that were silently dropped
/// due to sort mismatches. Non-zero counts indicate destination locals may be
/// unconstrained, potentially missing bugs.
fn report_chc_coerce_eq_drop_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.chc_coerce_eq_drops
            && info.has_drops()
        {
            warning(&format_args!(
                "UNSOUND: CHC coerce-eq constraints dropped {} time(s) across {} harness(es). \
                     Call-result equality constraints were lost due to sort mismatches — \
                     destination locals may be unconstrained. \
                     See metadata field `chc_coerce_eq_drops.per_harness` for affected harnesses.",
                info.total_count,
                info.per_harness.len()
            ));
        }
    }
}

/// Report constant zero-value fallback warnings if any occurred (#2463).
///
/// Checks metadata for MIR constants that were replaced with zero because their
/// actual values could not be extracted. Non-zero counts indicate potentially
/// unsound verification — non-zero constants silently became zero.
fn report_constant_zero_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.constant_zero_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_args!(
                "UNSOUND: {} MIR constant(s) replaced with zero-value fallback. \
                     Actual constant values could not be extracted — verification \
                     may produce false proofs if any replaced constant was non-zero. \
                     See metadata field `constant_zero_fallbacks.count`.",
                info.count,
            ));
        }
    }
}

/// Report statement IntoOption Result-drop warnings if any occurred (#2597).
///
/// Checks metadata for statement codegen paths where `Result::Err` values were
/// converted to `None`, which short-circuits translation and can skip constraints.
fn report_into_option_drop_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.into_option_drops
            && info.has_drops()
        {
            warning(&format_args!(
                "UNSOUND: statement codegen dropped {} Result::Err value(s) via IntoOption. \
                     Affected translation paths may have skipped constraint generation. \
                     See metadata field `into_option_drops.count`.",
                info.count,
            ));
        }
    }
}

/// Report pre-inlined collection internal workaround warnings (#1662).
fn report_internal_workaround_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.internal_workarounds
            && info.has_workarounds()
        {
            warning(&format_args!(
                "UNSOUND: statement codegen used {} symbolic workaround(s) for pre-inlined \
                     collection internals (BTree, RawVec). See `internal_workarounds.count`.",
                info.count,
            ));
        }
    }
}

/// Report abstracted stdlib fallback warnings (#1691).
fn report_abstracted_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.abstracted_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_args!(
                "UNSOUND: statement codegen used {} abstracted fallback(s) for pre-inlined \
                     stdlib internals (UTF8/Cow/String). See `abstracted_fallbacks.count`.",
                info.count,
            ));
        }
    }
}

/// Report unhandled function call warnings if any occurred (#2663).
///
/// Checks metadata for function calls that fell through all CHC dispatch stages,
/// leaving destination locals unconstrained. Non-zero counts indicate potentially
/// unsound verification — return values are treated as arbitrary.
fn report_unhandled_call_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.unhandled_calls
            && info.has_unhandled_calls()
        {
            warning(&format_args!(
                "UNSOUND: {} function call(s) fell through all dispatch stages — \
                     return values are unconstrained. Verification may produce false \
                     proofs. See metadata field `unhandled_calls.count`.",
                info.count,
            ));
        }
    }
}

/// Build warning text for fail-closed, untranslatable assertion counters.
fn format_assert_untranslatable_warning(count: usize) -> String {
    format!(
        "CONSERVATIVE: CHC emitted {} fail-closed assertion rule(s) for \
             untranslatable assertions. Verification may report extra failures. \
             See metadata field `assert_untranslatable.count`.",
        count
    )
}

/// Report untranslatable assertion counters if any occurred.
fn report_assert_untranslatable_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.assert_untranslatable
            && info.has_untranslatable()
        {
            warning(&format_assert_untranslatable_warning(info.count));
        }
    }
}

/// Build warning text for fail-closed, untranslatable heap-check counters.
fn format_heap_check_untranslatable_warning(count: usize) -> String {
    format!(
        "CONSERVATIVE: CHC emitted {} fail-closed heap-check rule(s) for \
             untranslatable heap predicates. Verification may report extra failures. \
             See metadata field `heap_check_untranslatable.count`.",
        count
    )
}

/// Report untranslatable heap-check counters if any occurred.
fn report_heap_check_untranslatable_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.heap_check_untranslatable
            && info.has_untranslatable()
        {
            warning(&format_heap_check_untranslatable_warning(info.count));
        }
    }
}

/// Build warning text for fail-closed, unknown-layout heap-check counters.
fn format_heap_check_unknown_layout_warning(count: usize) -> String {
    format!(
        "CONSERVATIVE: CHC emitted {} unknown-layout heap-check rule(s). \
             Verification may report extra failures for unsupported layouts. \
             See metadata field `heap_check_unknown_layout.count`.",
        count
    )
}

/// Report unknown-layout heap-check counters if any occurred.
fn report_heap_check_unknown_layout_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.heap_check_unknown_layout
            && info.has_unknown_layout()
        {
            warning(&format_heap_check_unknown_layout_warning(info.count));
        }
    }
}

/// Report store-dropped transition warnings (#2424).
fn report_store_dropped_transition_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.store_dropped_transitions
            && info.has_drops()
        {
            warning(&format_args!(
                "UNSOUND: {} memory-store transition(s) were dropped during CHC codegen. \
                     Subsequent reads may return stale/symbolic values, producing \
                     false proofs or false counterexamples.",
                info.count
            ));
        }
    }
}

/// Report CHC translation drop warnings (#2770).
fn report_chc_translation_drop_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.chc_translation_drops
            && info.has_drops()
        {
            let total = info.place_count + info.constant_count + info.field_projection_count;
            warning(&format_args!(
                "UNSOUND: {} CHC expression translation(s) dropped \
                     (places: {}, constants: {}, projections: {}). \
                     Dropped translations leave values unconstrained.",
                total, info.place_count, info.constant_count, info.field_projection_count
            ));
        }
        // Part of #3791 D2: emit drop fallback reason provenance for compiletest consumption.
        if let Some(ref info) = metadata.chc_translation_drops {
            for (fn_name, reasons) in &info.per_harness_reasons {
                for (reason, count) in reasons {
                    println!("[AY:DROP_FALLBACK_REASON:{fn_name}:{reason}={count}]");
                }
            }
            // Part of #3794 D1: emit translation-drop site reason provenance.
            for (fn_name, reasons) in &info.per_harness_translation_sites {
                for (reason, count) in reasons {
                    println!("[AY:TRANSLATION_DROP_REASON:{fn_name}:{reason}={count}]");
                }
            }
        }
    }
}

/// Report type-sort fallback warnings (#2705).
fn report_type_sort_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.type_sort_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_args!(
                "UNSOUND: {} type-sort resolution(s) fell back to hardcoded sort (bv32). \
                     Properties proved under the fallback sort may not hold for \
                     the real type widths.",
                info.count
            ));
        }
    }
}

/// Emit inferable summary provenance markers for compiletest consumption (Part of #4031).
fn report_inferable_summary_provenance(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.inferable_predicates {
            for (fn_name, summaries) in &info.per_harness_summaries {
                for (summary_name, count) in summaries {
                    println!("[AY:INFERABLE_SUMMARY:{fn_name}:{summary_name}={count}]");
                }
            }
        }
    }
}

/// Report signedness fallback warnings (#2749).
fn report_signedness_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.signedness_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_args!(
                "UNSOUND: {} signedness fallback(s) used operation-specific defaults. \
                     Division, remainder, and cast operations may use incorrect \
                     signed/unsigned semantics.",
                info.count
            ));
        }
    }
}

/// Report Vec field fallback warnings (#2733).
fn report_vec_field_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.vec_field_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_args!(
                "UNSOUND: {} Vec field access(es) returned fresh symbolic variables \
                     instead of real field values due to non-datatype sort. \
                     Actual field values are lost.",
                info.count
            ));
        }
    }
}

/// Report pointee synthesis fallback warnings (#3013).
fn report_pointee_synthesis_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.pointee_synthesis_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_args!(
                "UNSOUND: {} pointer dereference(s) created fresh unconstrained \
                     symbolic variables due to incomplete tracking. \
                     The solver can choose any value, potentially proving \
                     assertions that would fail at runtime.",
                info.count
            ));
        }
    }
}

/// Report unsupported construct fallback warnings (#3017).
fn report_unsupported_construct_fallback_warnings(project: &Project) {
    for metadata in &project.metadata {
        if let Some(ref info) = metadata.unsupported_construct_fallbacks
            && info.has_fallbacks()
        {
            warning(&format_args!(
                "UNSOUND: {} unsupported construct(s) used fallback data \
                     (e.g., defaulting to variant 0 for multi-variant enums). \
                     The verification model does not match actual Rust semantics.",
                info.count
            ));
        }
    }
}

/// Run verification on the given project.
fn verify_project(project: Project, session: KaniSession) -> Result<()> {
    debug!(?project, "verify_project");

    // Report unsoundness warnings BEFORE verification (#1929, #1989, #2234, #2235, #2463, #2663, #3018)
    // This ensures users see the warning before interpreting any results
    report_iterator_unsoundness_warnings(&project);
    report_bigint_unsoundness_warnings(&project);
    report_assume_dropped_transition_warnings(&project);
    report_store_dropped_transition_warnings(&project);
    report_chc_translation_drop_warnings(&project);
    report_chc_fallback_warnings(&project);
    report_chc_coerce_eq_drop_warnings(&project);
    report_constant_zero_fallback_warnings(&project);
    report_into_option_drop_warnings(&project);
    report_internal_workaround_warnings(&project);
    report_abstracted_fallback_warnings(&project);
    report_unhandled_call_warnings(&project);
    report_assert_untranslatable_warnings(&project);
    report_heap_check_untranslatable_warnings(&project);
    report_heap_check_unknown_layout_warnings(&project);
    report_type_sort_fallback_warnings(&project);
    report_signedness_fallback_warnings(&project);
    report_vec_field_fallback_warnings(&project);
    report_pointee_synthesis_fallback_warnings(&project);
    report_unsupported_construct_fallback_warnings(&project);
    report_inferable_summary_provenance(&project);

    // Metadata-derived harness count: keys the zero-harness success-with-note
    // verdict (task #49). Deliberately taken from the compiler-emitted
    // metadata, never from an empty result set, so a harness-discovery bug
    // can never become a silent false-pass channel.
    let metadata_harness_count = project.get_all_harnesses().len();
    let harnesses = session.determine_targets(project.get_all_harnesses())?;
    debug!(n = harnesses.len(), ?harnesses, "verify_project");

    // Residual-775 Wall-0: codegen is complete at this point (the project was
    // built above); stamp a machine-readable marker so DriverTimeout
    // adjudication can split compile-time from solve-time without rerunning.
    println!("[AY:CODEGEN_COMPLETE:harnesses={}]", harnesses.len());

    // The driver budgets --harness-timeout per harness, so the process
    // budget carries one extra harness-timeout per extra harness (mirrors
    // the outer runners' per-extra-harness scaling — see
    // wall_clock_watchdog::extend_for_extra_harnesses). P5.2: standalone
    // projects already armed this PRE-codegen from a source scan
    // (project.rs — codegen cost is per-harness too); the call here is an
    // idempotent top-up from the authoritative metadata count, covering
    // scan undercounts and cargo/std projects.
    wall_clock_watchdog::extend_for_extra_harnesses(
        session.args.harness_timeout.map(std::time::Duration::from),
        harnesses.len(),
    );

    // Verification
    let runner = harness_runner::HarnessRunner { sess: &session, project: &project };
    let results = runner.check_all_harnesses(&harnesses)?;

    if session.args.coverage {
        // We generate a timestamp to save the coverage data in a folder named
        // `kanicov_<date>` where `<date>` is the current date based on `format`
        // below. The purpose of adding timestamps to the folder name is to make
        // coverage results easily identifiable. Using a timestamp makes
        // coverage results not only distinguishable, but also easy to relate to
        // verification runs. We expect this to be particularly helpful for
        // users in a proof debugging session, who are usually interested in the
        // most recent results.
        let time_now = OffsetDateTime::now_utc();
        let format = format_description::parse("[year]-[month]-[day]_[hour]-[minute]")
            .context("failed to parse coverage timestamp format")?;
        let timestamp =
            time_now.format(&format).context("failed to format UTC timestamp for coverage")?;

        session.save_coverage_metadata(&project, &timestamp)?;
        session.save_coverage_results(&project, &results, &timestamp)?;
    }

    session.write_sarif(&results)?;
    session.write_proof_summary_json(&results)?;
    session.print_final_summary(&results, metadata_harness_count)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
// `trust_mc` mirrors the tool's CLI invocation identity.
#[allow(non_camel_case_types)]
pub(crate) enum CliIdentity {
    trust_mc,
    Kani,
}

impl CliIdentity {
    fn from_command_name(name: &str) -> Option<Self> {
        match name {
            "trust-mc" | "cargo-trust-mc" => Some(Self::trust_mc),
            "kani" | "cargo-kani" => Some(Self::Kani),
            _ => None,
        }
    }

    pub(crate) fn verifier_name(self) -> &'static str {
        match self {
            Self::trust_mc => "trust_mc Rust Verifier",
            Self::Kani => "Kani Rust Verifier",
        }
    }

    pub(crate) fn display_name(self) -> &'static str {
        match self {
            Self::trust_mc => "trust-mc",
            Self::Kani => "Kani",
        }
    }

    pub(crate) fn cargo_binary_name(self) -> &'static str {
        match self {
            Self::trust_mc => "cargo-trust-mc",
            Self::Kani => "cargo-kani",
        }
    }

    pub(crate) fn standalone_binary_name(self) -> &'static str {
        match self {
            Self::trust_mc => "trust-mc",
            Self::Kani => "kani",
        }
    }

    pub(crate) fn list_artifact_stem(self) -> &'static str {
        match self {
            Self::trust_mc => "trust_mc-list",
            Self::Kani => "kani-list",
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum InvocationType {
    CargoKani { args: Vec<OsString>, identity: CliIdentity },
    Standalone { identity: CliIdentity },
}

impl InvocationType {
    pub(crate) fn identity(&self) -> CliIdentity {
        match self {
            InvocationType::CargoKani { identity, .. }
            | InvocationType::Standalone { identity } => *identity,
        }
    }

    pub(crate) fn is_trust_mc_identity(&self) -> bool {
        self.identity() == CliIdentity::trust_mc
    }
}

fn print_clap_identity_output_if_requested<T: CommandFactory>(
    args: &[OsString],
    binary_name: &'static str,
) -> Result<bool> {
    if args.iter().skip(1).any(|arg| arg == "--version" || arg == "-V") {
        println!("{binary_name} {}", crate::version::KANI_VERSION);
        Ok(true)
    } else if matches!(args.get(1).and_then(|arg| arg.to_str()), Some("--help" | "-h"))
        && args.len() == 2
    {
        let mut command = identity_command::<T>(binary_name);
        command.print_help()?;
        println!();
        Ok(true)
    } else {
        Ok(false)
    }
}

fn identity_command<T: CommandFactory>(binary_name: &'static str) -> clap::Command {
    T::command().name(binary_name)
}

/// Peeks at command line arguments to determine if we're being invoked as 'trust_mc' or 'cargo-trust-mc'
/// (also supports legacy 'kani' and 'cargo-kani' for backward compatibility)
fn determine_invocation_type(mut args: Vec<OsString>) -> InvocationType {
    let exe = util::executable_basename(args.first());

    // Case 1: if 'trust_mc' or 'kani' is our first real argument, then we're being invoked as cargo-trust-mc
    // 'cargo trust-mc ...' will cause cargo to run 'cargo-trust-mc trust-mc ...' preserving argv1
    if let Some(identity) =
        args.get(1).and_then(|arg| CliIdentity::from_command_name(arg.to_string_lossy().as_ref()))
    {
        // Recreate our command line, but with 'trust_mc'/'kani' skipped
        args.remove(1);
        InvocationType::CargoKani { args, identity }
    }
    // Case 2: if 'trust_mc' or 'kani' is the name we're invoked as, then we're being invoked standalone
    // Note: we care about argv0 here, NOT std::env::current_exe(), as the later will be resolved
    else if let Some(identity) = exe
        .as_ref()
        .and_then(|name| CliIdentity::from_command_name(name.to_string_lossy().as_ref()))
    {
        let is_cargo_plugin = exe.as_ref().is_some_and(|name| {
            matches!(name.to_string_lossy().as_ref(), "cargo-trust-mc" | "cargo-kani")
        });
        if is_cargo_plugin {
            InvocationType::CargoKani { args, identity }
        } else {
            InvocationType::Standalone { identity }
        }
    }
    // Case 3: default fallback, act like standalone trust_mc.
    else {
        InvocationType::Standalone { identity: CliIdentity::trust_mc }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_invocation_type() {
        // conversions to/from OsString are rough, simplify the test code below
        fn x(args: Vec<&str>) -> Vec<OsString> {
            args.iter().map(|x| x.into()).collect()
        }

        // Case 1: 'cargo trust_mc'
        assert_eq!(
            determine_invocation_type(x(vec!["bar", "trust-mc", "foo"])),
            InvocationType::CargoKani {
                args: x(vec!["bar", "foo"]),
                identity: CliIdentity::trust_mc
            }
        );
        // Case 1 (legacy): 'cargo kani'
        assert_eq!(
            determine_invocation_type(x(vec!["bar", "kani", "foo"])),
            InvocationType::CargoKani { args: x(vec!["bar", "foo"]), identity: CliIdentity::Kani }
        );
        // Case 3: 'cargo-trust-mc'
        assert_eq!(
            determine_invocation_type(x(vec!["cargo-trust-mc", "foo"])),
            InvocationType::CargoKani {
                args: x(vec!["cargo-trust-mc", "foo"]),
                identity: CliIdentity::trust_mc
            }
        );
        // Case 3 (legacy): 'cargo-kani'
        assert_eq!(
            determine_invocation_type(x(vec!["cargo-kani", "foo"])),
            InvocationType::CargoKani {
                args: x(vec!["cargo-kani", "foo"]),
                identity: CliIdentity::Kani
            }
        );
        // Case 2: 'trust_mc'
        assert_eq!(
            determine_invocation_type(x(vec!["trust-mc", "foo"])),
            InvocationType::Standalone { identity: CliIdentity::trust_mc }
        );
        // Case 2 (legacy): 'kani'
        assert_eq!(
            determine_invocation_type(x(vec!["kani", "foo"])),
            InvocationType::Standalone { identity: CliIdentity::Kani }
        );
        // default
        assert_eq!(
            determine_invocation_type(x(vec!["foo"])),
            InvocationType::Standalone { identity: CliIdentity::trust_mc }
        );
        // weird case can be handled
        assert_eq!(
            determine_invocation_type(x(vec![])),
            InvocationType::Standalone { identity: CliIdentity::trust_mc }
        );
    }

    #[test]
    fn check_identity_command_help_names() {
        fn render_help<T: CommandFactory>(binary_name: &'static str) -> String {
            identity_command::<T>(binary_name).render_long_help().to_string()
        }

        let standalone_aliases = [(CliIdentity::Kani, "kani"), (CliIdentity::trust_mc, "trust-mc")];
        for (identity, expected_name) in standalone_aliases {
            let help = render_help::<args::StandaloneArgs>(identity.standalone_binary_name());
            assert!(
                help.starts_with("Verify a single Rust crate. For more information, see"),
                "{expected_name} help should render standalone help"
            );
            assert!(
                help.contains(&format!("Usage: {expected_name} [OPTIONS]")),
                "{expected_name} help should use the active standalone binary name"
            );
        }

        let cargo_aliases =
            [(CliIdentity::Kani, "cargo-kani"), (CliIdentity::trust_mc, "cargo-trust-mc")];
        for (identity, expected_name) in cargo_aliases {
            let help = render_help::<args::CargoKaniArgs>(identity.cargo_binary_name());
            assert!(
                help.starts_with("Verify a Rust crate. For more information, see"),
                "{expected_name} help should render cargo help"
            );
            assert!(
                help.contains(&format!("Usage: {expected_name} [OPTIONS]")),
                "{expected_name} help should use the active cargo binary name"
            );
        }
    }

    #[test]
    fn check_identity_output_fast_path_scope() {
        fn x(args: Vec<&str>) -> Vec<OsString> {
            args.iter().map(|x| x.into()).collect()
        }

        assert!(
            print_clap_identity_output_if_requested::<args::StandaloneArgs>(
                &x(vec!["kani", "list", "--help"]),
                "kani"
            )
            .is_ok_and(|handled| !handled),
            "subcommand help should remain delegated to clap"
        );
        assert!(
            print_clap_identity_output_if_requested::<args::CargoKaniArgs>(
                &x(vec!["cargo-kani", "list", "--help"]),
                "cargo-kani"
            )
            .is_ok_and(|handled| !handled),
            "cargo subcommand help should remain delegated to clap"
        );
    }

    #[test]
    fn test_format_chc_fallback_warning_includes_counts() {
        let message = format_chc_fallback_warning(7, 3);
        assert!(message.contains("7 time(s)"));
        assert!(message.contains("3 harness(es)"));
        assert!(message.contains("chc_fallbacks.per_harness"));
    }

    #[test]
    fn test_format_assert_untranslatable_warning_includes_count() {
        let message = format_assert_untranslatable_warning(5);
        assert!(message.contains("5"));
        assert!(message.contains("assert_untranslatable.count"));
    }

    #[test]
    fn test_format_heap_check_untranslatable_warning_includes_count() {
        let message = format_heap_check_untranslatable_warning(6);
        assert!(message.contains("6"));
        assert!(message.contains("heap_check_untranslatable.count"));
    }

    #[test]
    fn test_format_heap_check_unknown_layout_warning_includes_count() {
        let message = format_heap_check_unknown_layout_warning(7);
        assert!(message.contains("7"));
        assert!(message.contains("heap_check_unknown_layout.count"));
    }
}
