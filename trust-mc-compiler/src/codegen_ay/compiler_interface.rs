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

use crate::args::ReachabilityType;
use crate::codegen_ay::abstraction_boundary::AYAbstractionBoundary;
use crate::codegen_ay::context::{AYConfig, AYCtx};
use crate::codegen_ay::diagnostics::print_stub_coverage_summary;
use crate::kani_middle::codegen_units::CodegenUnits;
use crate::kani_middle::reachability::collect_reachable_items;
use crate::kani_middle::transform::{BodyTransformation, GlobalPasses};
use crate::kani_queries::QUERY_DB;
use ay_bindings::AYProgram;
use rustc_codegen_ssa::back::link::link_binary;
use rustc_codegen_ssa::traits::CodegenBackend;
use rustc_codegen_ssa::{CodegenResults, TargetConfig};
use rustc_data_structures::fx::FxIndexMap;
use rustc_errors::DEFAULT_LOCALE_RESOURCE;
use rustc_metadata::EncodedMetadata;
use rustc_middle::dep_graph::{WorkProduct, WorkProductId};
use rustc_middle::ty::TyCtxt;
use rustc_middle::util::Providers;
use rustc_public::CrateDef;
use rustc_public::mir::mono::MonoItem;
use rustc_public::rustc_internal;
use rustc_session::Session;
use rustc_session::config::{CrateType, OutputFilenames, OutputType};
use rustc_session::output::out_filename;
use std::any::{Any, type_name, type_name_of_val};
use std::fs::File;
use std::path::Path;
use tracing::{debug, info};
use trust_mc_metadata::ArtifactType;

use super::chc::get_chc_fallback_count_for_fn;
use super::chc::get_recursive_unwind_count_for_fn;
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
pub(crate) struct AYCodegenBackend {}

fn write_harness_smt2_file(
    path: &Path,
    program: &AYProgram,
    demoted_fallback_count: usize,
    recursive_unwind_count: usize,
) -> std::io::Result<()> {
    write_smt2_file(path, program, demoted_fallback_count, recursive_unwind_count)
}

impl AYCodegenBackend {
    /// Create a new AY backend.
    ///
    /// REQUIRES: (no preconditions)
    /// ENSURES: Returned backend is ready for codegen_crate calls.
    pub(crate) fn new() -> Self {
        AYCodegenBackend {}
    }
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
    }

    fn name(&self) -> &'static str {
        "trust_mc-ay"
    }

    fn locale_resource(&self) -> &'static str {
        DEFAULT_LOCALE_RESOURCE
    }

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

    fn codegen_crate(&self, tcx: TyCtxt) -> Box<dyn Any> {
        let ret_val = rustc_internal::run(tcx, || {
            let queries = QUERY_DB.with(|db| db.borrow().clone());
            // Reset session counters for process-reuse correctness (Part of #2360).
            super::chc::reset_chc_session_counters();
            super::statement::reset_statement_session_counters();
            super::diagnostics::reset_stub_diagnostics();
            uph::reset_per_harness_accumulator(); // Part of #3080.
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
                                ..Default::default()
                            };
                            // Apply user's logic override if specified (#621)
                            if let Some(ref logic) = queries.args().ay_logic {
                                config.logic = logic.clone();
                                config.logic_override = true;
                            }
                            let counters_before = uph::snapshot_counters();
                            let (min_ctx, items, program, vc_artifact) = self.codegen_items(
                                tcx,
                                &[MonoItem::Fn(*harness)],
                                &model_path,
                                config,
                                template_passes.clone(),
                                &mut transformer,
                            );
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
                            let demoted_fallback_count =
                                get_chc_fallback_count_for_fn(&harness_md.pretty_name)
                                    .max(get_chc_fallback_count_for_fn(&harness_md.mangled_name));
                            // Part of #4058 D2: read per-harness recursive unwind count.
                            let recursive_unwind_count = get_recursive_unwind_count_for_fn(
                                &harness_md.pretty_name,
                            )
                            .max(get_recursive_unwind_count_for_fn(&harness_md.mangled_name));
                            if let Err(err) = write_harness_smt2_file(
                                &smt_path,
                                &program,
                                demoted_fallback_count,
                                recursive_unwind_count,
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

        for crate_type in &requested_crate_types {
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
                    sess.dcx().fatal(format!(
                        "failed to create output file {}: {err}",
                        out_path.display()
                    ))
                });
                serde_json::to_writer(out_file, &content_stub).unwrap_or_else(|err| {
                    sess.dcx().fatal(format!(
                        "failed to write artifact stub {}: {err}",
                        out_path.display()
                    ))
                });
            }
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
        let abstraction_boundary = AYAbstractionBoundary::new();
        let (mut items, call_graph) =
            collect_reachable_items(tcx, transformer, starting_items, &abstraction_boundary);

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

        let any_pass_modified = global_passes.run_global_passes(
            transformer,
            tcx,
            starting_items,
            instances,
            call_graph,
        );

        if any_pass_modified {
            (items, _) =
                collect_reachable_items(tcx, transformer, starting_items, &abstraction_boundary);
        }

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
                    codegen_function(&mut ay_ctx, *instance);
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
        let harness_name = starting_items.iter().find_map(|item| match item {
            MonoItem::Fn(instance) => Some(instance.name()),
            _ => None, // external enum: MonoItem
        });
        let vc_artifact =
            ay_ctx.build_vc_artifact(harness_name.as_deref().unwrap_or("unknown"), None);

        let (min_ctx, program) = if ay_ctx.config.use_chc {
            // CHC path: use emit_chc to generate Horn clause program
            // Note: chc_vc was populated in codegen_function when use_chc was true
            ay_ctx.split_emit_chc()
        } else if ay_ctx.config.use_emit_bmc {
            // BMC IR path: use emit_bmc to generate program from abstract IR
            ay_ctx.finalize_emit_bmc();
            ay_ctx.split_emit_bmc()
        } else {
            // Legacy path: use directly-constructed program
            ay_ctx.finalize_counterexample_query();
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
    fn test_backend_name() {
        let backend = AYCodegenBackend::new();
        assert_eq!(CodegenBackend::name(&backend), "trust_mc-ay");
    }
}
