// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! AY Backend Compiler Interface.
//!
//! This module implements the `CodegenBackend` trait for the AY backend.
//! Function-level codegen is in `codegen_function.rs`; result aggregation
//! is in `codegen_results.rs`, file I/O in `codegen_file_io.rs`, and target
//! validation in `target_config.rs`.

use crate::args::{Arguments, ReachabilityType};
use crate::codegen_ay::abstraction_boundary::AYAbstractionBoundary;
use crate::codegen_ay::context::{AYConfig, AYCtx};
use crate::codegen_ay::diagnostics::print_stub_coverage_summary;
use crate::kani_middle::codegen_units::CodegenUnits;
use crate::kani_middle::reachability::collect_reachable_items;
use crate::kani_middle::transform::{BodyTransformation, GlobalPasses};
use crate::kani_queries::QUERY_DB;
use ay_bindings::AYProgram;
#[cfg(not(trust_toolchain))]
use rustc_codegen_ssa::CodegenResults;
use rustc_codegen_ssa::TargetConfig;
use rustc_codegen_ssa::back::link::link_binary;
use rustc_codegen_ssa::traits::CodegenBackend;
#[cfg(trust_toolchain)]
use rustc_codegen_ssa::{CompiledModules, CrateInfo};
#[cfg(not(trust_toolchain))]
use rustc_data_structures::fx::FxIndexMap;
#[cfg(not(trust_toolchain))]
use rustc_errors::DEFAULT_LOCALE_RESOURCE;
use rustc_metadata::EncodedMetadata;
#[cfg(trust_toolchain)]
use rustc_middle::dep_graph::WorkProductMap;
#[cfg(not(trust_toolchain))]
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_public::CrateDef;
use rustc_public::mir::mono::MonoItem;
use rustc_public::rustc_internal;
use rustc_session::Session;
#[cfg(not(all(trust_toolchain, version("1.101"))))]
use rustc_session::config::CrateType;
use rustc_session::config::{ErrorOutputType, OutputFilenames, OutputType};
use rustc_session::output::out_filename;
use rustc_span::Symbol;
#[cfg(all(trust_toolchain, version("1.101")))]
use rustc_structures::CrateType;
use std::any::{Any, type_name, type_name_of_val};
use std::fs::File;
use std::path::Path;
use std::sync::OnceLock;
use tracing::{debug, info};
use trust_mc_metadata::ArtifactType;

use super::chc::get_chc_fallback_count_for_fn;
use super::chc::get_recursive_unwind_count_for_fn;
use super::chc::get_vacuous_checks_for_fn;
use super::codegen_file_io::{
    ArArchiveBuilderBuilder, JsonOutputStyle, codegen_results, write_file, write_smt2_file,
    write_vc_artifact,
};
use super::codegen_function::codegen_function;
use super::codegen_results::AYCodegenResults;
use super::target_config::{check_target, select_target_features};
use super::unsoundness_per_harness as uph;
use super::{take_kani_mem_overapprox_by_fn, take_offset_provenance_unresolved_by_fn};
use crate::kani_middle::{attributes, check_reachable_items};

#[cfg(all(trust_toolchain, version("1.101")))]
type BackendInitSession = rustc_session::EarlySession;
#[cfg(not(all(trust_toolchain, version("1.101"))))]
type BackendInitSession = Session;

/// Preserve the selector's exact feature set across the modern API's set-valued
/// field. The new bfloat reliability flag does not claim unsupported modeling.
#[cfg(all(trust_toolchain, version("1.101")))]
fn modern_target_config(
    arch: &rustc_target::spec::Arch,
    os: &rustc_target::spec::Os,
) -> TargetConfig {
    TargetConfig {
        internal_target_features: select_target_features(arch, os).into_iter().collect(),
        has_reliable_f16: true,
        has_reliable_f16_math: true,
        has_reliable_f16b: false,
        has_reliable_f128: true,
        has_reliable_f128_math: true,
    }
}

/// AY verification backend for the trust_mc compiler.
///
/// Implements the rustc [`CodegenBackend`] trait with AY as the verification
/// engine. This backend translates MIR into SMT-LIB2 verification conditions
/// that AY solves directly.
///
/// # Verification Modes
///
/// Two verification paths are supported, selected per-harness via [`AYConfig`]:
///
/// - **BMC** (bounded model checking): Loops are unrolled to a fixed depth and
///   the resulting acyclic CFG is encoded as quantifier-free bitvector/array
///   constraints (`QF_AUFBV`).
///
/// - **CHC** (Constrained Horn Clauses): Loops are encoded as recursive
///   predicates and solved via AY's PDR-based CHC engine, enabling unbounded
///   verification without manual unwind bounds. Activated with `--ay-chc`.
///
/// # Pipeline
///
/// ```text
/// rustc MIR -> codegen_crate -> AYCtx + StatementCodegen -> AYProgram -> .smt2
///                                       |                          |
///                                       +- BMC path: emit_bmc()    |
///                                       +- CHC path: mir_to_chc()  |
///                                                                   v
///                                                        trust_mc-driver solves
/// ```
///
/// # Usage
///
/// Created by the compiler driver; not instantiated directly by users:
///
/// ```text
/// let backend = AYCodegenBackend::new();
/// // Passed to rustc as the codegen backend via --codegen-backend
/// ```
///
/// # Configuration
///
/// Per-harness behavior is controlled through [`AYConfig`], which is populated
/// from CLI flags (`--ay-chc`, `--ay-logic`, etc.) and harness
/// attributes (`#[kani::unwind(N)]`).
///
/// See also: [`AYConfig`] for solver configuration, [`AYCtx`] for codegen state.
pub(crate) struct AYCodegenBackend {
    /// The engine arguments, parsed once from `-C llvm-args` in
    /// [`CodegenBackend::init`].
    args: OnceLock<Arguments>,
    /// The compiler identity a backend dylib was built against; `None` for the
    /// embedded binary, which links its compiler statically at build time.
    identity: Option<crate::BackendIdentity>,
}

fn write_harness_smt2_file(
    path: &Path,
    program: &AYProgram,
    demoted_fallback_count: usize,
    recursive_unwind_count: usize,
    vacuous_all_checks_unreachable: bool,
) -> std::io::Result<()> {
    write_smt2_file(
        path,
        program,
        demoted_fallback_count,
        recursive_unwind_count,
        vacuous_all_checks_unreachable,
    )
}

impl AYCodegenBackend {
    /// Create a new AY backend.
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: Returned backend is ready for codegen_crate calls.
    pub(crate) fn new() -> Self {
        AYCodegenBackend { args: OnceLock::new(), identity: None }
    }

    /// A backend that checks `identity` against the loading compiler in
    /// [`CodegenBackend::init`].
    pub(crate) fn with_identity(identity: crate::BackendIdentity) -> Self {
        AYCodegenBackend { args: OnceLock::new(), identity: Some(identity) }
    }

    /// Parse the engine arguments from `-C llvm-args` and initialize the
    /// trust-mc session.
    ///
    /// The one place arguments are parsed, for the embedded binary and for
    /// trustc loading `librustc_codegen_trust_mc.dylib` alike. A malformed
    /// argument is a fatal rustc diagnostic (exit 1), never clap's
    /// `process::exit` inside the host compiler.
    fn initialize_session(&self, sess: &BackendInitSession) {
        // A dylib inside a different compiler build than the one it links is
        // undefined behaviour waiting to happen; refuse before anything runs.
        if let Some(identity) = &self.identity
            && let Err(mismatch) = (identity.verify)(sess)
        {
            sess.dcx().fatal(mismatch);
        }
        // Hosted in trustc, nothing but `codegen_crate` runs the crate-items
        // check and VC generation. A session that skips codegen would succeed
        // with nothing checked, so refuse it here.
        if self.identity.is_some()
            && let Some(refusal) = hosted_codegen_refusal(
                sess.opts.unstable_opts.no_codegen,
                sess.opts.output_types.should_codegen(),
            )
        {
            sess.dcx().fatal(refusal);
        }
        let args = match crate::args::parse_llvm_args(&sess.opts.cg.llvm_args) {
            Ok(args) => args,
            Err(err) => sess.dcx().fatal(format!(
                "invalid trust-mc engine arguments (-C llvm-args): {}",
                crate::args::render_llvm_args_error(&err)
            )),
        };
        if self.identity.is_some()
            && let Some(refusal) = hosted_args_refusal(&args)
        {
            sess.dcx().fatal(refusal);
        }
        // The driver keeps its own environment clean, but not the one cargo's
        // `[env]` table or a wrapper gives this process: refuse a knob here.
        if self.identity.is_some()
            && let Some(refusal) = hosted_env_knobs_refusal(std::env::vars_os().map(|(key, _)| key))
        {
            sess.dcx().fatal(refusal);
        }
        crate::session::init_session(
            &args,
            matches!(sess.opts.error_format, ErrorOutputType::Json { .. }),
        );
        QUERY_DB.with(|db| db.borrow_mut().set_args(args.clone()));
        if self.args.set(args).is_err() {
            sess.dcx().fatal("the trust-mc codegen backend was initialized twice");
        }
    }

    /// The arguments [`CodegenBackend::init`] parsed, installed in this
    /// thread's `QUERY_DB` when it has none.
    ///
    /// `QUERY_DB` is thread-local, and nothing guarantees that `init` and
    /// `codegen_crate` run on one thread (`-Zthreads>1`, or a host compiler
    /// that calls them from different threads).
    fn seed_query_db(&self) -> &Arguments {
        let args = self
            .args
            .get()
            .expect("CodegenBackend::init parses the trust-mc arguments before codegen_crate");
        QUERY_DB.with(|db| {
            let mut db = db.borrow_mut();
            if !db.has_args() {
                db.set_args(args.clone());
            }
        });
        args
    }
}

/// Why a trustc-hosted backend must refuse a session that would skip codegen.
///
/// rustc skips `codegen_crate` under exactly `no_codegen || !should_codegen()`
/// (`rustc_interface::passes::start_codegen`). The embedded binary covers that
/// case from `after_analysis`; trustc runs no such callback for a loaded
/// backend, so there the crate-items check and VC generation would never run.
pub(crate) fn hosted_codegen_refusal(
    no_codegen: bool,
    should_codegen: bool,
) -> Option<&'static str> {
    (no_codegen || !should_codegen).then_some(
        "the trust-mc codegen backend requires a codegen build: -Zno-codegen or a \
         metadata/dep-info-only --emit would skip check_crate_items and VC generation",
    )
}

/// Why a trustc-hosted backend must refuse the engine arguments it was given.
///
/// `trust-mc-driver` always sends `--check-version`
/// (`call_single_file::check_version`). Without it the `-C llvm-args` never
/// came from the driver (a front door that strips inherited `-Cllvm-args`, say)
/// and the defaults would check nothing while the build succeeds.
pub(crate) fn hosted_args_refusal(args: &Arguments) -> Option<&'static str> {
    args.check_version().is_none().then_some(
        "trust-mc codegen backend loaded without trust-mc-driver engine arguments \
         (-C llvm-args); refusing to run with defaults",
    )
}

/// Why a trustc-hosted backend must refuse its own environment.
///
/// The engine reads [`ENGINE_ENV_KNOBS`] as generation knobs. On the Trustc
/// route trust-mc-driver refuses while one is set in its environment and removes
/// every `TRUST_MC_*` variable from the cargo and trustc children it starts, but
/// a cargo `[env]` table, a rustc wrapper or anything else between cargo and
/// rustc can set one on the rustc process itself, where the driver cannot see it
/// (review finding, T1 S7: `[env] TRUST_MC_REACH_DEBUG = ""` in a package's
/// `.cargo/config.toml` reached the engine and a verdict was printed). A hosted
/// backend therefore refuses to initialize while any knob is set, naming them;
/// the embedded binary (DevCli, where `loop_two_lane` sets knobs on purpose) is
/// unaffected.
pub(crate) fn hosted_env_knobs_refusal<I, K>(env_keys: I) -> Option<String>
where
    I: IntoIterator<Item = K>,
    K: AsRef<std::ffi::OsStr>,
{
    let vars = trust_mc_metadata::engine_args::set_engine_env_knobs(env_keys);
    (!vars.is_empty()).then(|| {
        format!(
            "trust-mc codegen backend loaded with engine environment knob(s) {} set; on the \
             Trustc route no knob may reach the engine (trust-mc-driver refuses them in its \
             own environment and removes them from its children), so something between cargo \
             and rustc set them (a cargo [env] table, a wrapper); refusing to run",
            vars.join(", ")
        )
    })
}

impl Default for AYCodegenBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl CodegenBackend for AYCodegenBackend {
    fn provide(&self, _providers: &mut Providers) {
        // No pre-monomorphization query overrides needed.
        // Intrinsic handling is done in RustcIntrinsicsPass after monomorphization.
    }

    fn print_version(&self) {
        println!("trust_mc-AY version: {}", env!("CARGO_PKG_VERSION"));
        println!(
            "trust_mc engine: sha={} dirty={}",
            env!("TRUST_MC_GIT_SHA"),
            env!("TRUST_MC_GIT_DIRTY")
        );
        if let Some(identity) = &self.identity {
            println!(
                "trust_mc backend built for: rustc commit {}, {}, artifact_driver_sha256={}",
                identity.rustc_commit,
                identity.driver,
                if identity.driver_sha256.is_empty() { "<none>" } else { identity.driver_sha256 }
            );
        }
    }

    /// The name a named `-Zcodegen-backend=trust_mc` selection matches
    /// (T1-D4). A path selection does not compare it.
    fn name(&self) -> &'static str {
        "trust_mc"
    }

    #[cfg(not(all(trust_toolchain, version("1.101"))))]
    fn init(&self, sess: &Session) {
        self.initialize_session(sess);
    }

    /// Modern rustc initializes its backend before constructing `Session`.
    /// Identity, arguments and hosted-session refusals must still run here,
    /// before either backend initialization or codegen can succeed.
    #[cfg(all(trust_toolchain, version("1.101")))]
    fn init(&mut self, sess: &rustc_session::EarlySession) -> rustc_session::CodegenBackendInit {
        self.initialize_session(sess);
        rustc_session::CodegenBackendInit::default()
    }

    #[cfg(not(trust_toolchain))]
    fn locale_resource(&self) -> &'static str {
        DEFAULT_LOCALE_RESOURCE
    }

    /// Trust: rustc builds the `CrateInfo` itself from this CPU name (the
    /// backend's `locale_resource` hook is gone). The nightly lane passes
    /// `"ay"` to `CrateInfo::new` in `codegen_results`; returning the same name
    /// keeps the two lanes' `CrateInfo` identical.
    #[cfg(trust_toolchain)]
    fn target_cpu(&self, _sess: &Session) -> String {
        "ay".to_owned()
    }

    #[cfg(not(all(trust_toolchain, version("1.101"))))]
    fn target_config(&self, sess: &Session) -> TargetConfig {
        let target_features = select_target_features(&sess.target.arch, &sess.target.os);

        TargetConfig {
            unstable_target_features: target_features.clone(),
            target_features,
            has_reliable_f16: true,
            has_reliable_f16_math: true,
            has_reliable_f128: true,
            has_reliable_f128_math: true,
        }
    }

    #[cfg(all(trust_toolchain, version("1.101")))]
    fn target_config(&self, sess: &rustc_session::EarlySession) -> TargetConfig {
        modern_target_config(&sess.target.arch, &sess.target.os)
    }

    fn codegen_crate(&self, tcx: TyCtxt) -> Box<dyn Any> {
        let ret_val = rustc_internal::run(tcx, || {
            let args = self.seed_query_db();
            // Formerly the embedded binary's `after_analysis`; here, so trustc
            // loading the dylib runs it too. Claimed once per process.
            // A lost claim means some earlier session in this process took the
            // check; generating VCs without it would drop the crate-items
            // refusals silently.
            if !crate::kani_queries::claim_crate_items_check() {
                tcx.dcx().fatal(
                    "check_crate_items already claimed in this process; refusing to generate \
                     VCs without it",
                );
            }
            crate::kani_middle::check_crate_items(tcx, args.ignore_global_asm);
            let queries = QUERY_DB.with(|db| db.borrow().clone());
            // Reset session counters for process-reuse correctness (Part of #2360).
            super::chc::reset_chc_session_counters();
            super::statement::reset_statement_session_counters();
            super::diagnostics::reset_stub_diagnostics();
            uph::reset_per_harness_accumulator(); // Part of #3080.
            // Index the `--c-lib` sources once per run: which `extern "C"`
            // symbols does the user actually supply a definition for? Symbols
            // nobody supplies keep Kani's fail-closed undefined-function
            // `error()`; supplied ones become a sound effect frame.
            super::foreign_defs::init_c_lib_symbols(&queries.args().c_lib);
            // …and READ them. The restricted C front-end turns each accepted
            // definition into the same Expr/Rule IR a Rust callee gets, so a
            // property about the C's VALUES (`takes_int(1) == 3`) becomes
            // provable instead of merely reachable. Anything outside the
            // accepted fragment falls back to the effect frame above, per
            // function. The integer-width model comes from the compilation
            // TARGET, never an assumption: `long` is 32 bits on LLP64.
            {
                let pointer_bits = u32::from(tcx.sess.target.pointer_width);
                let long_bits = if tcx.sess.target.is_like_windows { 32 } else { pointer_bits };
                crate::c_ffi::init(
                    &queries.args().c_lib,
                    crate::c_ffi::CTarget::new(pointer_bits, long_bits),
                );
            }
            check_target(tcx.sess);
            if queries.args().reachability_analysis != ReachabilityType::None
                && queries.kani_functions().is_empty()
            {
                tcx.sess
                    .dcx()
                    .struct_err(
                        "Failed to detect trust_mc functions. Please check your installation is correct.",
                        )
                    .emit();
            }
            let base_filepath = tcx.output_filenames(()).path(OutputType::Object);
            let base_filename = base_filepath.as_path();
            let reachability = queries.args().reachability_analysis;
            let mut results = AYCodegenResults::new(tcx, reachability);
            if reachability == ReachabilityType::None {
                return codegen_results(tcx);
            }
            match reachability {
                ReachabilityType::AllFns | ReachabilityType::Harnesses => {
                    let units = CodegenUnits::new(&queries, tcx);
                    if queries.args().list_metadata_only {
                        units.write_metadata(&queries, tcx);
                        return codegen_results(tcx);
                    }
                    let template_passes = GlobalPasses::new(&queries, tcx);
                    let harness_count: usize = units.iter().map(|unit| unit.harnesses.len()).sum();
                    let codegen_stage_start = std::time::Instant::now();
                    for unit in units.iter() {
                        let mut transformer = BodyTransformation::new(&queries, tcx, unit);
                        for harness in &unit.harnesses {
                            // Reclaim memory from previous harness's cached MIR bodies.
                            // Each harness gets independent codegen. Part of #3075.
                            transformer.clear_cache();
                            let model_path = units.harness_model_path(*harness);
                            let Some(harness_md) = units.harness_metadata(*harness) else {
                                tcx.sess.dcx().err(
                                    "Missing harness metadata for AY codegen; skipping harness",
                                );
                                continue;
                            };
                            // The loop-removing MIR passes follow THIS harness's
                            // unwind bound, not the unit's smallest.
                            transformer.set_harness_declared_unwind(
                                crate::kani_middle::transform::harness_declared_unwind(
                                    &queries,
                                    harness_md.attributes.unwind_value,
                                ),
                            );
                            let has_explicit_unwind = queries.args().unwind.is_some()
                                || harness_md.attributes.unwind_value.is_some()
                                || queries.args().default_unwind.is_some();
                            let unwind_depth = queries
                                .args()
                                .unwind
                                .or(harness_md.attributes.unwind_value)
                                .or(queries.args().default_unwind)
                                .unwrap_or(1);

                            let unwinding_assertions = !queries.args().no_default_checks
                                && !queries.args().no_unwinding_checks;
                            let mut config = AYConfig {
                                unwind_depth,
                                has_explicit_unwind,
                                unwinding_assertions,
                                use_emit_bmc: queries.args().ay_emit_bmc,
                                use_chc: queries.args().ay_chc,
                                chc_track_level: queries.args().ay_chc_track,
                                chc_step_mode: queries.args().ay_chc_step,
                                chc_int_lift: queries.args().ay_chc_int_lift,
                                ay_wide_mem: queries.args().ay_wide_mem,
                                extra_pointer_checks: queries.args().extra_pointer_checks,
                                prove_safety_only: queries.args().prove_safety_only,
                                memory_safety_checks: !queries.args().no_default_checks
                                    && !queries.args().no_memory_safety_checks,
                                overflow_checks: !queries.args().no_default_checks
                                    && !queries.args().no_overflow_checks,
                                // Opt-in only: NaN is defined behaviour, so
                                // `no_default_checks` is irrelevant here.
                                nan_checks: queries.args().nan_checks,
                                undefined_function_checks: !queries.args().no_default_checks
                                    && !queries.args().no_undefined_function_checks,
                                // Auto-enable bounded unrolling when CHC mode has
                                // an explicit unwind hint — eliminates per-file flag
                                // opt-in. Keyed on `has_explicit_unwind` (not
                                // `unwind_depth > 1`) so an explicit `#[kani::unwind(1)]`
                                // also unrolls: a non-terminating loop under a depth-1
                                // bound must emit its unwinding-assertion error edge
                                // (SOUNDNESS — otherwise the loop is vacuously proved
                                // safe, e.g. `loop {}` under unwind(1)).
                                chc_bounded_unroll: queries.args().ay_chc_bounded_unroll
                                    || (queries.args().ay_chc && has_explicit_unwind),
                                // MEMUB-24/25/27: thread shadow-memory state only
                                // when the uninit instrumentation actually ran.
                                uninit_checks: queries
                                    .args()
                                    .ub_check
                                    .contains(&crate::args::ExtraChecks::Uninit),
                                is_contract_proof: matches!(
                                    harness_md.attributes.kind,
                                    trust_mc_metadata::HarnessKind::ProofForContract { .. }
                                ),
                                // Kani parity: the driver forwards
                                // `--assertion-reach-checks` unless the user
                                // asked for `--no-assertion-reach-checks`. With
                                // the checks off, no per-assertion reachability
                                // companion is generated, so an assertion in
                                // dead code reports SUCCESS rather than
                                // UNREACHABLE (see AYConfig for the soundness
                                // argument).
                                assertion_reach_checks: queries.args().check_assertion_reachability,
                                chc_straightline_discharge:
                                    !crate::codegen_ay::chc::straightline_discharge_env_disabled(),
                                ..Default::default()
                            };
                            // Apply user's logic override if specified (#621)
                            if let Some(ref logic) = queries.args().ay_logic {
                                config.logic = logic.clone();
                                config.logic_override = true;
                            }
                            let counters_before = uph::snapshot_counters();
                            // Per-harness translation deadline: a harness whose
                            // codegen outlives its budget is written out as a
                            // fail-closed TRANSLATION_TIMEOUT artifact and the loop
                            // moves on, instead of the driver's watchdog killing
                            // every harness in the file.
                            let budget = queries.args().translation_timeout_ms.map(|ms| {
                                super::translation_deadline::per_harness_budget(
                                    std::time::Duration::from_millis(ms),
                                    harness_count,
                                    codegen_stage_start.elapsed(),
                                )
                            });
                            let guard = budget.map(super::translation_deadline::arm);
                            let outcome =
                                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                    self.codegen_items(
                                        tcx,
                                        &[MonoItem::Fn(*harness)],
                                        &model_path,
                                        config,
                                        template_passes.clone(),
                                        &mut transformer,
                                    )
                                }));
                            drop(guard);
                            let (min_ctx, items, program, vc_artifact) = match outcome {
                                Ok(generated) => generated,
                                Err(payload) => {
                                    let Some(timeout) = payload
                                        .downcast_ref::<super::translation_deadline::TranslationTimeout>()
                                        .cloned()
                                    else {
                                        std::panic::resume_unwind(payload);
                                    };
                                    uph::record_harness_deltas(
                                        &harness_md.pretty_name,
                                        &counters_before,
                                        &uph::snapshot_counters(),
                                    );
                                    uph::absorb_fn_keyed_for_harness(
                                        &harness_md.pretty_name,
                                        &take_offset_provenance_unresolved_by_fn(),
                                        &take_kani_mem_overapprox_by_fn(),
                                    );
                                    write_translation_timeout_artifacts(
                                        tcx,
                                        &model_path,
                                        &harness_md.pretty_name,
                                        &timeout,
                                    );
                                    continue;
                                }
                            };
                            let counters_after = uph::snapshot_counters();
                            uph::record_harness_deltas(
                                &harness_md.pretty_name,
                                &counters_before,
                                &counters_after,
                            );
                            // Re-key the per-FUNCTION attribution maps onto THIS harness while
                            // we are still inside its codegen boundary. Their recorders document
                            // the intent ("attributes the demotion to the harness whose codegen
                            // accumulated it so it cannot leak onto siblings") but key by function
                            // name, and the driver's fail-closed `attributable_to_harness` charges
                            // any non-harness key against EVERY harness — so a fn-keyed entry
                            // demoted every sibling's genuine proof. Draining here is precise:
                            // codegen_items ran for this harness alone, so everything these maps
                            // accumulated is this harness's.
                            uph::absorb_fn_keyed_for_harness(
                                &harness_md.pretty_name,
                                &take_offset_provenance_unresolved_by_fn(),
                                &take_kani_mem_overapprox_by_fn(),
                            );
                            results.extend(min_ctx, items, None);
                            let smt_path = model_path.with_extension("smt2");
                            // The per-function counters are keyed by the name codegen gave the
                            // function, `Instance::name`. On Trust that name carries the crate
                            // (`fail::check`) while the reported `pretty_name` does not
                            // (`rustc_compat::instance_name`), so look the harness up under
                            // every name it can be recorded as: a count found under none of
                            // them would silently drop a demotion.
                            let codegen_fn_name = harness.name();
                            let demoted_fallback_count =
                                get_chc_fallback_count_for_fn(&harness_md.pretty_name)
                                    .max(get_chc_fallback_count_for_fn(&codegen_fn_name))
                                    .max(get_chc_fallback_count_for_fn(&harness_md.mangled_name));
                            // Part of #4058 D2: read per-harness recursive unwind count.
                            let recursive_unwind_count =
                                get_recursive_unwind_count_for_fn(&harness_md.pretty_name)
                                    .max(get_recursive_unwind_count_for_fn(&codegen_fn_name))
                                    .max(get_recursive_unwind_count_for_fn(
                                        &harness_md.mangled_name,
                                    ));
                            // CHC lane V4: the straight-line discharge proved
                            // this harness's checks UNREACHABLE rather than
                            // safe. The emitted system cannot show that, so
                            // carry it as a marker for the driver.
                            let vacuous_all_checks_unreachable =
                                get_vacuous_checks_for_fn(&harness_md.pretty_name)
                                    || get_vacuous_checks_for_fn(&codegen_fn_name)
                                    || get_vacuous_checks_for_fn(&harness_md.mangled_name);
                            if let Err(err) = write_harness_smt2_file(
                                &smt_path,
                                &program,
                                demoted_fallback_count,
                                recursive_unwind_count,
                                vacuous_all_checks_unreachable,
                            ) {
                                tcx.sess.dcx().err(format!(
                                    "compilation failed: could not write verification artifact {}: {err}",
                                    smt_path.display()
                                ));
                            }
                            // Write VC artifact sidecar with property metadata (#1237)
                            let vc_path = model_path.with_extension("vc.json");
                            if let Err(err) = write_vc_artifact(&vc_path, &vc_artifact) {
                                tcx.sess.dcx().err(format!(
                                    "compilation failed: could not write VC artifact {}: {err}",
                                    vc_path.display()
                                ));
                            }
                        }
                    }
                    units.write_metadata(&queries, tcx);
                }
                ReachabilityType::None => {}
                ReachabilityType::PubFns => info!("AY backend: PubFns reachability mode"),
            }
            // ReachabilityType::None returns early at line 187, so this is always reached.
            results.print_report(tcx);
            // Print stub coverage summary after main report (Part of #1685)
            print_stub_coverage_summary();
            if reachability != ReachabilityType::Harnesses
                && reachability != ReachabilityType::AllFns
            {
                let metadata = results.into_metadata();
                let output_style = if queries.args().output_pretty_json {
                    JsonOutputStyle::Pretty
                } else {
                    JsonOutputStyle::Compact
                };
                if let Err(err) =
                    write_file(base_filename, ArtifactType::Metadata, &metadata, output_style)
                {
                    tcx.sess.dcx().err(format!(
                        "compilation failed: could not write metadata artifact: {err}"
                    ));
                }
            }
            codegen_results(tcx)
        });
        ret_val.unwrap_or_else(|_| {
            tcx.sess.dcx().fatal("AY codegen internal error: codegen execution returned an error")
        })
    }

    #[cfg(not(trust_toolchain))]
    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        sess: &Session,
        _filenames: &OutputFilenames,
    ) -> (CodegenResults, FxIndexMap<WorkProductId, WorkProduct>) {
        match ongoing_codegen.downcast::<(CodegenResults, FxIndexMap<WorkProductId, WorkProduct>)>()
        {
            Ok(val) => *val,
            Err(val) => {
                // This is an internal compiler error - codegen returned an unexpected type.
                // Emit a fatal diagnostic to stop compilation with a structured error.
                let actual_type = type_name_of_val(&*val);
                let expected_type =
                    type_name::<(CodegenResults, FxIndexMap<WorkProductId, WorkProduct>)>();
                sess.dcx().fatal(format!(
                    "AY codegen internal error: join_codegen received unexpected type. \
                     Expected: {expected_type}. Actual: {actual_type}. \
                     This is a bug in the AY backend. Please report this issue.",
                ));
            }
        }
    }

    /// Trust: rustc owns the `CrateInfo` and passes it in, so the joined result
    /// is only the (empty) compiled-module list and the work products.
    #[cfg(trust_toolchain)]
    fn join_codegen(
        &self,
        ongoing_codegen: Box<dyn Any>,
        sess: &Session,
        #[cfg(all(trust_toolchain, version("1.101")))] _incr_comp_session: Option<
            &rustc_session::IncrCompSession,
        >,
        _filenames: &OutputFilenames,
        _crate_info: &CrateInfo,
    ) -> (CompiledModules, WorkProductMap) {
        match ongoing_codegen.downcast::<(CompiledModules, WorkProductMap)>() {
            Ok(val) => *val,
            Err(val) => {
                // Same structured fatal error as the nightly lane.
                let actual_type = type_name_of_val(&*val);
                let expected_type = type_name::<(CompiledModules, WorkProductMap)>();
                sess.dcx().fatal(format!(
                    "AY codegen internal error: join_codegen received unexpected type. \
                     Expected: {expected_type}. Actual: {actual_type}. \
                     This is a bug in the AY backend. Please report this issue.",
                ));
            }
        }
    }

    #[cfg(not(trust_toolchain))]
    fn link(
        &self,
        sess: &Session,
        codegen_results: CodegenResults,
        rustc_metadata: EncodedMetadata,
        outputs: &OutputFilenames,
    ) {
        let requested_crate_types = codegen_results.crate_info.crate_types.clone();
        let local_crate_name = codegen_results.crate_info.local_crate_name;

        if requested_crate_types.contains(&CrateType::Rlib) {
            link_binary(
                sess,
                &ArArchiveBuilderBuilder,
                codegen_results,
                rustc_metadata,
                outputs,
                self.name(),
            );
        }

        write_artifact_stubs(sess, &requested_crate_types, local_crate_name, outputs);
    }

    /// Trust: `link` and `link_binary` take the compiled modules and the
    /// rustc-built `CrateInfo` separately. The steps are the nightly lane's.
    #[cfg(trust_toolchain)]
    fn link(
        &self,
        sess: &Session,
        compiled_modules: CompiledModules,
        crate_info: CrateInfo,
        rustc_metadata: EncodedMetadata,
        outputs: &OutputFilenames,
    ) {
        let requested_crate_types = crate_info.crate_types.clone();
        let local_crate_name = crate_info.local_crate_name;

        if requested_crate_types.contains(&CrateType::Rlib) {
            link_binary(
                sess,
                &ArArchiveBuilderBuilder,
                compiled_modules,
                crate_info,
                rustc_metadata,
                outputs,
                self.name(),
            );
        }

        write_artifact_stubs(sess, &requested_crate_types, local_crate_name, outputs);
    }
}

/// Overwrite every requested non-rlib output with a stub naming the metadata
/// artifact. Runs after `link_binary`, which may write to those paths.
/// The artifacts for a harness whose translation ran out of budget.
///
/// The `.smt2` is an unconditionally derivable error relation plus the
/// `; TRANSLATION_TIMEOUT:` marker: the driver reports the harness UNKNOWN from
/// the marker, and a consumer that ignored it would still get FAILURE, never a
/// proof. The `.vc.json` names the harness and no properties.
fn write_translation_timeout_artifacts(
    tcx: TyCtxt,
    model_path: &Path,
    harness_name: &str,
    timeout: &super::translation_deadline::TranslationTimeout,
) {
    tracing::warn!(
        harness = harness_name,
        phase = timeout.phase,
        budget_ms = u64::try_from(timeout.budget.as_millis()).unwrap_or(u64::MAX),
        "translation deadline exceeded; harness reported UNKNOWN (TranslationTimeout)"
    );
    let smt_path = model_path.with_extension("smt2");
    if let Err(err) = std::fs::write(&smt_path, translation_timeout_smt(timeout)) {
        tcx.sess.dcx().err(format!(
            "compilation failed: could not write verification artifact {}: {err}",
            smt_path.display()
        ));
    }
    let harness = trust_mc_core::ident::HarnessId::new(harness_name, harness_name);
    let artifact = trust_mc_core::artifact::VcArtifact::new(harness)
        .with_mode(trust_mc_core::artifact::VerificationMode::Chc);
    let vc_path = model_path.with_extension("vc.json");
    if let Err(err) = write_vc_artifact(&vc_path, &artifact) {
        tcx.sess.dcx().err(format!(
            "compilation failed: could not write VC artifact {}: {err}",
            vc_path.display()
        ));
    }
}

/// The fail-closed HORN program written for a timed-out harness.
pub(super) fn translation_timeout_smt(
    timeout: &super::translation_deadline::TranslationTimeout,
) -> String {
    format!(
        "(set-logic HORN)\n\
         (declare-rel chc_translation_timeout ())\n\
         (rule chc_translation_timeout)\n\
         (query chc_translation_timeout)\n\
         {}",
        timeout.marker_line()
    )
}

fn write_artifact_stubs(
    sess: &Session,
    requested_crate_types: &[CrateType],
    local_crate_name: Symbol,
    outputs: &OutputFilenames,
) {
    for crate_type in requested_crate_types {
        let out_fname = out_filename(sess, *crate_type, outputs, local_crate_name);
        let out_path = out_fname.as_path();
        debug!(?crate_type, ?out_path, "link");
        if *crate_type != CrateType::Rlib {
            let base_filepath = outputs.path(OutputType::Object);
            let base_filename = base_filepath.as_path();
            let content_stub = trust_mc_metadata::CompilerArtifactStub {
                metadata_path: base_filename.with_extension(ArtifactType::Metadata),
            };
            let out_file = File::create(out_path).unwrap_or_else(|err| {
                sess.dcx()
                    .fatal(format!("failed to create output file {}: {err}", out_path.display()))
            });
            serde_json::to_writer(out_file, &content_stub).unwrap_or_else(|err| {
                sess.dcx()
                    .fatal(format!("failed to write artifact stub {}: {err}", out_path.display()))
            });
        }
    }
}

impl AYCodegenBackend {
    /// Generate AY code for the given items.
    fn codegen_items<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        starting_items: &[MonoItem],
        _model_path: &Path,
        config: AYConfig,
        mut global_passes: GlobalPasses,
        transformer: &mut BodyTransformation,
    ) -> (
        crate::codegen_ay::context::MinimalAYCtx,
        Vec<MonoItem>,
        ay_bindings::AYProgram,
        trust_mc_core::artifact::VcArtifact,
    ) {
        let accounting = super::unstubbed_accounting::AccountingScope::begin(if config.use_chc {
            match starting_items {
                [MonoItem::Fn(root)] => Some(*root),
                _ => None,
            }
        } else {
            None
        });
        let abstraction_boundary = AYAbstractionBoundary::new();
        let (mut items, call_graph) =
            super::translation_deadline::timed_phase("reachability", || {
                collect_reachable_items(tcx, transformer, starting_items, &abstraction_boundary)
            });
        // Design 3, D2 (kani_middle/dyn_universe.rs): every dyn coercion this
        // harness can reach, for the CHC dispatch's completeness decisions.
        let mut dyn_universe = call_graph.dyn_universe.clone();

        let instances = items
            .iter()
            .filter_map(|item| match item {
                MonoItem::Fn(instance) => Some(*instance),
                MonoItem::Static(static_def) => {
                    let instance: rustc_public::mir::mono::Instance = (*static_def).into();
                    instance.has_body().then_some(instance)
                }
                MonoItem::GlobalAsm(_) => None,
            })
            .collect();

        let any_pass_modified = super::translation_deadline::timed_phase("global_passes", || {
            global_passes.run_global_passes(transformer, tcx, starting_items, instances, call_graph)
        });

        if any_pass_modified {
            let recollected_graph;
            (items, recollected_graph) =
                collect_reachable_items(tcx, transformer, starting_items, &abstraction_boundary);
            dyn_universe = recollected_graph.dyn_universe;
        }
        let _dyn_universe_guard = crate::kani_middle::dyn_universe::HarnessUniverseGuard::install(
            std::sync::Arc::new(dyn_universe),
        );

        // Save config values before moving into AYCtx
        let function_inlining = config.function_inlining;

        let mut ay_ctx =
            QUERY_DB.with(|db| AYCtx::new(tcx, db.borrow().clone(), config, transformer));

        check_reachable_items(ay_ctx.tcx, &ay_ctx.queries, &items);

        // When function inlining is enabled, only codegen the starting items (harnesses).
        // Called functions are inlined at call sites, so we don't need to codegen them separately.
        // This prevents generating disconnected constraints for inlined functions.
        let items_to_codegen: &[MonoItem] = if function_inlining { starting_items } else { &items };

        for item in items_to_codegen {
            match item {
                MonoItem::Fn(instance) => {
                    // Skip codegen for functions with hook or model markers - their behavior is
                    // defined by the hook/model handler at the call site, not by their body.
                    if let Some(marker) = attributes::fn_marker(instance.def) {
                        use crate::kani_middle::kani_functions::{
                            KaniFunction, try_get_kani_function,
                        };
                        if let Some(kani_fn) = try_get_kani_function(&marker) {
                            match kani_fn {
                                KaniFunction::Hook(_) | KaniFunction::Model(_) => {
                                    debug!(
                                        "AY codegen: skipping {:?} function {}",
                                        kani_fn,
                                        instance.name()
                                    );
                                    continue;
                                }
                                KaniFunction::Intrinsic(_) => {}
                            }
                        }
                    }
                    // Skip kani_intrinsic - it's a placeholder with `loop {}` that's never
                    // executed (calls are intercepted at the call site). Codegen would fail
                    // due to CFG cycle.
                    let fn_name = instance.name();
                    if fn_name.contains("kani_intrinsic") {
                        debug!("AY codegen: skipping kani_intrinsic placeholder {}", fn_name);
                        continue;
                    }

                    debug!("AY codegen: function {}", fn_name);
                    super::translation_deadline::timed_phase("codegen_function", || {
                        codegen_function(&mut ay_ctx, *instance)
                    });
                }
                MonoItem::Static(def) => {
                    debug!("AY codegen: static {}", def.name());
                    ay_ctx.unsupported("static codegen", def.name());
                }
                MonoItem::GlobalAsm(_) => {
                    ay_ctx.unsupported("global_asm", "unknown");
                }
            }
        }

        // Finalize and emit the verification query.
        //
        // Three paths are available:
        // 1. CHC IR: Horn clause emission (emit_chc) - for unbounded verification
        // 2. BMC IR: abstract IR emission (finalize_emit_bmc + split_emit_bmc)
        // 3. Legacy: direct program construction (finalize_counterexample_query + split)
        //
        // The CHC path (#574) uses mir_to_chc to translate MIR to Horn clauses,
        // enabling unbounded verification via AY's PDR-based CHC engine.
        //
        // The BMC IR path (#206) builds the AYProgram from bmc_vc using emit_bmc(),
        // enabling future backend flexibility and cleaner separation of concerns.

        // Build VC artifact before split (split consumes ay_ctx).
        // Extract harness name from starting_items.
        // Kani's crate-relative name on both routes (`rustc_compat::instance_name`): Trust's
        // `Instance::name` prefixes the local crate, which made the artifact's harness differ
        // from the frozen nightly's for the same harness.
        let harness_name = starting_items.iter().find_map(|item| match item {
            MonoItem::Fn(instance) => Some(crate::rustc_compat::instance_name(tcx, *instance)),
            _ => None, // external enum: MonoItem
        });
        let vc_artifact =
            ay_ctx.build_vc_artifact(harness_name.as_deref().unwrap_or("unknown"), None);

        let (min_ctx, program) = if ay_ctx.config.use_chc {
            // CHC path: use emit_chc to generate Horn clause program
            // Note: chc_vc was populated in codegen_function when use_chc was true
            super::translation_deadline::timed_phase("emit_chc", || ay_ctx.split_emit_chc())
        } else if ay_ctx.config.use_emit_bmc {
            // BMC IR path: use emit_bmc to generate program from abstract IR
            ay_ctx.finalize_emit_bmc();
            ay_ctx.split_emit_bmc()
        } else {
            // Legacy path: use directly-constructed program
            ay_ctx.finalize_counterexample_query();
            ay_ctx.finalize_playback_inputs();
            ay_ctx.program.check_sat();
            // Add get-value for violation flags (allows driver to identify which property failed).
            // Note: Z3 will error "model is not available" if unsat, driver must handle this.
            ay_ctx.add_get_value_for_violations();
            // Add get-value for kani::any_raw symbols to enable concrete playback.
            ay_ctx.add_get_value_for_kani_any();
            // Add get-value for cover properties (kani::cover reachability checks) #922.
            ay_ctx.add_get_value_for_covers();
            // Add get-value for source coverage predicates.
            ay_ctx.add_get_value_for_coverage();
            ay_ctx.split()
        };
        accounting.finish();
        (min_ctx, items, program, vc_artifact)
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::panic)]
    use super::*;
    // --- AYCodegenBackend ---
    // format_smt2_with_demoted_fallback_markers tests live in codegen_file_io.rs

    #[test]
    fn translation_timeout_artifact_is_fail_closed_and_marked() {
        let timeout = super::super::translation_deadline::TranslationTimeout {
            phase: "chc_inline_walker",
            budget: std::time::Duration::from_millis(30_000),
        };
        let smt = translation_timeout_smt(&timeout);
        // The marker the driver keys on.
        assert!(
            smt.lines()
                .any(|l| l == "; TRANSLATION_TIMEOUT: phase=chc_inline_walker budget_ms=30000"),
            "{smt}"
        );
        // An unconditional fact for the queried relation: a consumer that ignores
        // the marker derives the query (FAILURE), it never proves anything.
        assert!(smt.contains("(declare-rel chc_translation_timeout ())"), "{smt}");
        assert!(smt.contains("(rule chc_translation_timeout)"), "{smt}");
        assert!(smt.contains("(query chc_translation_timeout)"), "{smt}");
        assert!(smt.starts_with("(set-logic HORN)"), "{smt}");
    }

    #[test]
    fn test_backend_name() {
        let backend = AYCodegenBackend::new();
        assert_eq!(CodegenBackend::name(&backend), "trust_mc");
    }

    #[cfg(all(trust_toolchain, version("1.101")))]
    #[test]
    fn modern_target_config_preserves_selected_features_and_float_capabilities() {
        use rustc_target::spec::{Arch, Os};

        rustc_span::create_session_if_not_set_then(
            rustc_span::edition::Edition::Edition2024,
            |_| {
                let cases: &[(Arch, Os, &[&str])] = &[
                    (Arch::X86_64, Os::Linux, &["sse", "sse2", "x87"]),
                    (Arch::X86_64, Os::MacOs, &["sse", "sse2", "x87"]),
                    (Arch::X86_64, Os::None, &[]),
                    (Arch::AArch64, Os::MacOs, &["neon", "aes", "sha2", "sha3"]),
                    (Arch::AArch64, Os::Linux, &["neon"]),
                    (Arch::AArch64, Os::IOs, &["neon"]),
                    (Arch::AArch64, Os::None, &[]),
                    (Arch::RiscV64, Os::Linux, &[]),
                ];
                for (arch, os, expected) in cases {
                    let config = modern_target_config(arch, os);
                    assert_eq!(
                        config.internal_target_features.len(),
                        expected.len(),
                        "{arch}/{os}"
                    );
                    for feature in *expected {
                        assert!(config.internal_target_features.contains(&Symbol::intern(feature)));
                    }
                    assert!(config.has_reliable_f16);
                    assert!(config.has_reliable_f16_math);
                    assert!(config.has_reliable_f128);
                    assert!(config.has_reliable_f128_math);
                    assert!(!config.has_reliable_f16b, "no bfloat model is installed");
                }
            },
        );
    }

    #[test]
    fn hosted_backend_refuses_sessions_that_skip_codegen() {
        assert!(hosted_codegen_refusal(true, true).is_some(), "-Zno-codegen");
        assert!(hosted_codegen_refusal(false, false).is_some(), "--emit=metadata");
        assert!(hosted_codegen_refusal(true, false).is_some());
        assert_eq!(hosted_codegen_refusal(false, true), None);
    }

    #[test]
    fn hosted_backend_refuses_empty_llvm_args() {
        let empty = crate::args::parse_llvm_args(&[]).expect("an empty list parses to defaults");
        let refusal = hosted_args_refusal(&empty).expect("defaults without the driver are fatal");
        assert!(refusal.contains("-C llvm-args"), "{refusal}");
        let driver: Vec<String> =
            "--check-version=0.7.0 --log-level=warn --assertion-reach-checks --reachability=harnesses"
                .split_whitespace()
                .map(str::to_owned)
                .collect();
        let args = crate::args::parse_llvm_args(&driver).expect("the driver's flag list parses");
        assert_eq!(hosted_args_refusal(&args), None);
    }

    /// A knob in the hosted backend's own environment is refused, naming every
    /// set knob and nothing else; a clean environment, or one with only the
    /// driver's non-knob variables, is accepted.
    #[test]
    fn hosted_backend_refuses_engine_env_knobs_in_its_own_environment() {
        // The driver's own non-knob variable, spelled so the driver's scan of this
        // source for `"TRUST_MC_*"` knob literals does not read it as one.
        let sysroot_var = concat!("TRUST_", "MC_SYSROOT");
        let refusal = hosted_env_knobs_refusal([
            "PATH",
            "TRUST_MC_SMT_NODE_BUDGET",
            sysroot_var,
            "TRUST_MC_REACH_DEBUG",
        ])
        .expect("a set knob is fatal");
        assert!(
            refusal.contains("TRUST_MC_REACH_DEBUG, TRUST_MC_SMT_NODE_BUDGET")
                && !refusal.contains(sysroot_var)
                && refusal.contains("[env]"),
            "{refusal}"
        );
        assert_eq!(hosted_env_knobs_refusal(["PATH", sysroot_var, "AY_TIMEOUT"]), None);
        assert_eq!(hosted_env_knobs_refusal(std::iter::empty::<&str>()), None);
        for knob in trust_mc_metadata::engine_args::ENGINE_ENV_KNOBS {
            assert!(hosted_env_knobs_refusal([*knob]).is_some(), "{knob}");
        }
    }

    /// Every compile trust-mc-driver's Trustc route sends (a standalone file, and
    /// a cargo target with its dependency and local groups concatenated) carries
    /// `--check-version`, so the hosted backend accepts it.
    #[test]
    fn hosted_backend_accepts_the_trustc_route_llvm_args() {
        let fixture = crate::args::trustc_route_llvm_args_fixture;
        let standalone = fixture("standalone");
        let cargo: Vec<String> =
            fixture("cargo-dependency").into_iter().chain(fixture("cargo-local")).collect();
        for llvm_args in [standalone, cargo] {
            let args = crate::args::parse_llvm_args(&llvm_args).expect("the Trustc argv parses");
            assert_eq!(hosted_args_refusal(&args), None, "{llvm_args:?}");
        }
    }
}
