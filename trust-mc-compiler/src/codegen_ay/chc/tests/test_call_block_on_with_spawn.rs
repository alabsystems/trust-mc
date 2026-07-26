// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Current-head localizer for async spawn dispatch.
//!
//! Part of #4075.

#![allow(clippy::panic, clippy::unwrap_used)]

use super::common::*;
use std::collections::BTreeMap;

const ASYNC_SPAWN_REAL_FILE: &str =
    include_str!("../../../../../tests/trust_mc/AsyncAwait/spawn.rs");
const LOCAL_KANI_ASYNC_RUNTIME: &str = include_str!("test_call_block_on_with_spawn_runtime.txt");

fn build_async_spawn_unit_source(source: &str) -> String {
    let mut result = String::from(LOCAL_KANI_ASYNC_RUNTIME);
    result.push('\n');
    for line in source.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("#[kani::proof")
            || trimmed.starts_with("#[kani::unwind")
            || trimmed.starts_with("// kani-expect:")
            || trimmed.starts_with("// compile-flags:")
            || trimmed.starts_with("// kani-flags:")
            || trimmed.starts_with("//!")
        {
            continue;
        }
        result.push_str(line);
        result.push('\n');
    }
    result
}

#[derive(Debug)]
struct SpawnLocalizerSnapshot {
    fn_name: &'static str,
    rule_count: usize,
    translation_drops: BTreeMap<String, usize>,
    translation_sites: BTreeMap<String, BTreeMap<String, usize>>,
    top_level_drop_sites: Vec<MirDropSite>,
    block_on_with_spawn_call_site: Option<BlockOnWithSpawnCallSite>,
    cfg_window: Vec<String>,
}

#[derive(Debug)]
struct SpawnDispatchAnalysis {
    top_level_sites: BTreeMap<String, usize>,
    call_dispatch_owners: Vec<String>,
    drop_inline_walk_failed_site: Option<String>,
    total_call_dispatch_fallbacks: usize,
    resume_abort_count: usize,
    drop_fallback_count: usize,
    drop_inline_walk_failed_count: usize,
    scheduler_run_fallbacks: usize,
    join_handle_poll_fallbacks: usize,
    scheduler_spawn_fallbacks: usize,
    block_on_with_spawn_fallbacks: usize,
    yield_now_fallbacks: usize,
    active_owner_buckets: Vec<&'static str>,
}

impl SpawnLocalizerSnapshot {
    fn total_sound_fallback_count(&self) -> usize {
        self.translation_drops.values().copied().sum()
    }

    fn total_reason_count(&self, reason: &str) -> usize {
        self.translation_sites
            .values()
            .map(|reasons| reasons.get(reason).copied().unwrap_or(0))
            .sum()
    }

    fn total_reason_count_with_prefix(&self, prefix: &str) -> usize {
        self.translation_sites
            .values()
            .map(|reasons| {
                reasons
                    .iter()
                    .filter(|(reason, _)| reason.starts_with(prefix))
                    .map(|(_, count)| *count)
                    .sum::<usize>()
            })
            .sum()
    }

    fn reason_count(&self, fn_fragment: &str, reason: &str) -> usize {
        self.translation_sites
            .iter()
            .filter(|(fn_name, _)| fn_name.contains(fn_fragment))
            .map(|(_, reasons)| reasons.get(reason).copied().unwrap_or(0))
            .sum()
    }

    fn owners_for_reason(&self, reason: &str) -> Vec<String> {
        self.translation_sites
            .iter()
            .filter_map(|(fn_name, reasons)| {
                reasons.get(reason).copied().filter(|count| *count > 0).map(|_| fn_name.clone())
            })
            .collect()
    }
}

#[derive(Debug)]
struct MirDropSite {
    bb_idx: usize,
    local: usize,
    local_ty: String,
    is_coroutine: bool,
    debug_names: Vec<String>,
}

#[derive(Debug)]
struct BlockOnWithSpawnCallSite {
    call_bb: usize,
    target_bb: usize,
    target_drop_local: Option<usize>,
    target_drop_is_coroutine: bool,
    post_drop_target: Option<usize>,
}

fn collect_mir_drop_sites(
    body: &rustc_public::mir::Body,
    chc_ctx: &ChcCtx<'_, '_>,
) -> Vec<MirDropSite> {
    let mut debug_names_by_local: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for info in &body.var_debug_info {
        let rustc_public::mir::VarDebugInfoContents::Place(place) = &info.value else {
            continue;
        };
        if !place.projection.is_empty() {
            continue;
        }
        debug_names_by_local.entry(place.local).or_default().push(info.name.clone());
    }

    body.blocks
        .iter()
        .enumerate()
        .filter_map(|(bb_idx, block)| {
            let rustc_public::mir::TerminatorKind::Drop { place, .. } = &block.terminator.kind
            else {
                return None;
            };
            if !place.projection.is_empty() {
                return None;
            }
            let local_ty = chc_ctx.resolve_body_ty(body.locals()[place.local].ty);
            Some(MirDropSite {
                bb_idx,
                local: place.local,
                local_ty: format!("{local_ty:?}"),
                is_coroutine: matches!(
                    local_ty.kind(),
                    rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::Coroutine(..))
                ),
                debug_names: debug_names_by_local.remove(&place.local).unwrap_or_default(),
            })
        })
        .collect()
}

fn collect_block_on_with_spawn_call_site(
    body: &rustc_public::mir::Body,
    chc_ctx: &ChcCtx<'_, '_>,
) -> Option<BlockOnWithSpawnCallSite> {
    body.blocks.iter().enumerate().find_map(|(bb_idx, block)| {
        let rustc_public::mir::TerminatorKind::Call { func, target: Some(target_bb), .. } =
            &block.terminator.kind
        else {
            return None;
        };
        let callee_path = chc_ctx.resolve_callee_path(func)?;
        if callee_path != "block_on_with_spawn" && !callee_path.ends_with("::block_on_with_spawn") {
            return None;
        }

        let (target_drop_local, target_drop_is_coroutine, post_drop_target) =
            match &body.blocks[*target_bb].terminator.kind {
                rustc_public::mir::TerminatorKind::Drop { place, target, .. }
                    if place.projection.is_empty() =>
                {
                    let local_ty = chc_ctx.resolve_body_ty(body.locals()[place.local].ty);
                    (
                        Some(place.local),
                        matches!(
                            local_ty.kind(),
                            rustc_public::ty::TyKind::RigidTy(
                                rustc_public::ty::RigidTy::Coroutine(..)
                            )
                        ),
                        Some(*target),
                    )
                }
                _ => (None, false, None),
            };
        Some(BlockOnWithSpawnCallSite {
            call_bb: bb_idx,
            target_bb: *target_bb,
            target_drop_local,
            target_drop_is_coroutine,
            post_drop_target,
        })
    })
}

fn reset_spawn_localizer_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
}

fn collect_cfg_window(body: &rustc_public::mir::Body, chc_ctx: &ChcCtx<'_, '_>) -> Vec<String> {
    body.blocks
        .iter()
        .enumerate()
        .map(|(bb_idx, block)| {
            let term = match &block.terminator.kind {
                rustc_public::mir::TerminatorKind::Call { func, target, .. } => {
                    let callee = chc_ctx
                        .resolve_callee_path(func)
                        .or_else(|| chc_ctx.resolve_fn_def_name(func))
                        .unwrap_or_else(|| "<unresolved>".to_owned());
                    format!("Call(target={target:?}, callee={callee})")
                }
                rustc_public::mir::TerminatorKind::Drop { place, target, unwind, .. } => {
                    format!("Drop(local={}, target=bb{target}, unwind={unwind:?})", place.local)
                }
                rustc_public::mir::TerminatorKind::Assert { target, unwind, .. } => {
                    format!("Assert(target=bb{target}, unwind={unwind:?})")
                }
                rustc_public::mir::TerminatorKind::Goto { target } => format!("Goto(bb{target})"),
                rustc_public::mir::TerminatorKind::SwitchInt { targets, .. } => {
                    format!("SwitchInt(otherwise=bb{})", targets.otherwise())
                }
                rustc_public::mir::TerminatorKind::Return => "Return".to_owned(),
                rustc_public::mir::TerminatorKind::Resume => "Resume".to_owned(),
                rustc_public::mir::TerminatorKind::Abort => "Abort".to_owned(),
                other => format!("{other:?}"),
            };
            format!("bb{bb_idx}: stmts={}, term={term}", block.statements.len())
        })
        .collect()
}

fn run_spawn_localizer() -> SpawnLocalizerSnapshot {
    use std::sync::{Arc, Mutex};
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_spawn_localizer_metadata();

    type LocResult = (usize, Vec<MirDropSite>, Option<BlockOnWithSpawnCallSite>, Vec<String>);
    let result: Arc<Mutex<Option<LocResult>>> = Arc::new(Mutex::new(None));
    let result_clone = Arc::clone(&result);
    let fn_name = "round_robin_schedule_manual";
    let source = build_async_spawn_unit_source(ASYNC_SPAWN_REAL_FILE);

    let handle = std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(
                &source,
                "2018",
                |ctx| {
                    let instance = find_instance_by_suffix(ctx.tcx, fn_name);
                    let body = instance.body().expect("function body");
                    let chc_ctx = ChcCtx::new_with_instance(
                        ctx.tcx,
                        &body,
                        instance,
                        fn_name,
                        ChcConfig {
                            track_level: crate::args::ChcTrackLevel::Mem,
                            ..ChcConfig::default()
                        },
                    );
                    let ds = collect_mir_drop_sites(&body, &chc_ctx);
                    let bs = collect_block_on_with_spawn_call_site(&body, &chc_ctx);
                    let cw = collect_cfg_window(&body, &chc_ctx);
                    let (vc, _, _) = chc_ctx.translate_with_diagnostics();
                    assert_vc_structure(&vc, fn_name, body.blocks.len());
                    *result_clone.lock().unwrap() = Some((vc.rules.len(), ds, bs, cw));
                },
            );
        })
        .expect("spawn large-stack thread");
    join_with_timeout(handle, "run_spawn_localizer");

    let (rule_count, top_level_drop_sites, block_on_with_spawn_call_site, cfg_window) =
        result.lock().unwrap().take().expect("translation produced no result");
    let translation_drops = take_translation_drop_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    SpawnLocalizerSnapshot {
        fn_name,
        rule_count,
        translation_drops,
        translation_sites,
        top_level_drop_sites,
        block_on_with_spawn_call_site,
        cfg_window,
    }
}

fn analyze_spawn_snapshot(snapshot: &SpawnLocalizerSnapshot) -> SpawnDispatchAnalysis {
    let top_level_sites =
        snapshot.translation_sites.get(snapshot.fn_name).cloned().unwrap_or_default();
    let call_dispatch_owners = snapshot.owners_for_reason("call_dispatch_fallback");
    let drop_inline_walk_failed_site = top_level_sites
        .keys()
        .find(|reason| reason.starts_with("drop_inline_walk_failed@"))
        .cloned();
    let total_call_dispatch_fallbacks = snapshot.total_reason_count("call_dispatch_fallback");
    let resume_abort_count = snapshot.total_reason_count("resume_abort");
    let drop_fallback_count = snapshot.total_reason_count("drop_fallback");
    let drop_inline_walk_failed_count =
        snapshot.total_reason_count_with_prefix("drop_inline_walk_failed");
    let scheduler_run_fallbacks = snapshot.reason_count("Scheduler::run", "call_dispatch_fallback");
    let join_handle_poll_fallbacks =
        snapshot.reason_count("JoinHandle::poll", "call_dispatch_fallback");
    let scheduler_spawn_fallbacks =
        snapshot.reason_count("Scheduler::spawn", "call_dispatch_fallback");
    let block_on_with_spawn_fallbacks =
        snapshot.reason_count("block_on_with_spawn", "call_dispatch_fallback");
    let yield_now_fallbacks = snapshot.reason_count("YieldNow::poll", "call_dispatch_fallback")
        + snapshot.reason_count("yield_now", "call_dispatch_fallback");
    let owner_buckets = [
        ("Scheduler::run", scheduler_run_fallbacks),
        ("JoinHandle::poll", join_handle_poll_fallbacks),
        ("Scheduler::spawn", scheduler_spawn_fallbacks),
        ("block_on_with_spawn", block_on_with_spawn_fallbacks),
        ("yield_now", yield_now_fallbacks),
    ];
    let active_owner_buckets: Vec<_> =
        owner_buckets.iter().filter_map(|(label, count)| (*count > 0).then_some(*label)).collect();

    SpawnDispatchAnalysis {
        top_level_sites,
        call_dispatch_owners,
        drop_inline_walk_failed_site,
        total_call_dispatch_fallbacks,
        resume_abort_count,
        drop_fallback_count,
        drop_inline_walk_failed_count,
        scheduler_run_fallbacks,
        join_handle_poll_fallbacks,
        scheduler_spawn_fallbacks,
        block_on_with_spawn_fallbacks,
        yield_now_fallbacks,
        active_owner_buckets,
    }
}

fn emit_spawn_localizer_report(
    snapshot: &SpawnLocalizerSnapshot,
    analysis: &SpawnDispatchAnalysis,
) {
    let block_on_with_spawn_call_site = snapshot.block_on_with_spawn_call_site.as_ref();
    eprintln!(
        "[block_on_with_spawn localizer] fn={}, rules={}, total_sound_fallback_count={}, \
         total_call_dispatch_fallbacks={}, resume_abort={resume_abort_count}, \
         drop_fallback={drop_fallback_count}, drop_inline_walk_failed={drop_inline_walk_failed_count}, \
         owners={call_dispatch_owners:?}, active_owner_buckets={active_owner_buckets:?}, \
         scheduler_run={scheduler_run_fallbacks}, join_handle_poll={join_handle_poll_fallbacks}, \
         scheduler_spawn={scheduler_spawn_fallbacks}, block_on_with_spawn={block_on_with_spawn_fallbacks}, \
         yield_now={yield_now_fallbacks}, block_on_with_spawn_call_site={block_on_with_spawn_call_site:?}, \
         top_level_drop_sites={top_level_drop_sites:?}, translation_drops={translation_drops:?}, \
         translation_sites={translation_sites:?}, cfg_window={cfg_window:?}",
        snapshot.fn_name,
        snapshot.rule_count,
        snapshot.total_sound_fallback_count(),
        analysis.total_call_dispatch_fallbacks,
        resume_abort_count = analysis.resume_abort_count,
        drop_fallback_count = analysis.drop_fallback_count,
        drop_inline_walk_failed_count = analysis.drop_inline_walk_failed_count,
        call_dispatch_owners = analysis.call_dispatch_owners,
        active_owner_buckets = analysis.active_owner_buckets,
        scheduler_run_fallbacks = analysis.scheduler_run_fallbacks,
        join_handle_poll_fallbacks = analysis.join_handle_poll_fallbacks,
        scheduler_spawn_fallbacks = analysis.scheduler_spawn_fallbacks,
        block_on_with_spawn_fallbacks = analysis.block_on_with_spawn_fallbacks,
        yield_now_fallbacks = analysis.yield_now_fallbacks,
        top_level_drop_sites = snapshot.top_level_drop_sites,
        translation_drops = snapshot.translation_drops,
        translation_sites = snapshot.translation_sites,
        cfg_window = snapshot.cfg_window,
    );
}

fn assert_spawn_dispatch_localized(
    snapshot: &SpawnLocalizerSnapshot,
    analysis: &SpawnDispatchAnalysis,
) {
    assert!(
        snapshot.rule_count > 0,
        "{} should produce CHC rules through the normal translation path",
        snapshot.fn_name
    );
    // Part of #4075 D3: trait-scoped vtable discriminant + scheduler loop fuel
    // override eliminated the call_dispatch_fallback. The spawn vtable model
    // now provides exact Future::poll IDs, and the loop replay fuel bounds
    // Scheduler::run to the expected round-robin schedule length.
    assert_eq!(
        analysis.total_call_dispatch_fallbacks,
        0,
        "spawn localizer should emit zero call_dispatch_fallbacks after D3 (trait-scoped \
         vtable discriminant + loop fuel override); active_owner_buckets={active_owner_buckets:?}, \
         owners={call_dispatch_owners:?}, translation_sites={translation_sites:?}",
        active_owner_buckets = analysis.active_owner_buckets,
        call_dispatch_owners = analysis.call_dispatch_owners,
        translation_sites = snapshot.translation_sites,
    );
}

fn assert_spawn_cleanup_residual(
    snapshot: &SpawnLocalizerSnapshot,
    analysis: &SpawnDispatchAnalysis,
) {
    let failed_drop_site =
        snapshot.top_level_drop_sites.iter().find(|site| site.bb_idx == 13 && site.local == 6);
    let block_on_with_spawn_call_site = snapshot.block_on_with_spawn_call_site.as_ref();

    // Part of #4075 D3: trait-scoped vtable discriminant + scheduler loop fuel
    // eliminated the call_dispatch_fallback and rule_budget truncation fallbacks.
    // Only the 2 cleanup-path fallbacks remain (drop_fallback + drop_inline_walk_failed).
    assert_eq!(
        snapshot.total_sound_fallback_count(),
        2,
        "spawn localizer should record 2 fallbacks: cleanup-path only (drop_fallback + \
         drop_inline_walk_failed); translation_drops={:?}, translation_sites={:?}",
        snapshot.translation_drops,
        snapshot.translation_sites,
    );
    assert_eq!(
        analysis.resume_abort_count, 1,
        "spawn localizer should currently keep a single resume_abort marker on the panic cleanup path; \
         translation_sites={:?}",
        snapshot.translation_sites,
    );
    assert_eq!(
        analysis.drop_fallback_count, 1,
        "spawn localizer should currently keep a single drop_fallback marker on the panic cleanup path; \
         translation_sites={:?}",
        snapshot.translation_sites,
    );
    assert_eq!(
        analysis.drop_inline_walk_failed_count, 1,
        "spawn localizer should currently keep one drop_inline_walk_failed site on the panic cleanup path; \
         translation_sites={:?}",
        snapshot.translation_sites,
    );
    assert_eq!(
        analysis.drop_inline_walk_failed_site.as_deref(),
        Some("drop_inline_walk_failed@bb13:local6"),
        "spawn localizer should pin the residual to the panic-only coroutine cleanup drop \
         (drop(_6)) after `core::panicking::assert_failed`; top_level_sites={top_level_sites:?}, \
         top_level_drop_sites={top_level_drop_sites:?}, translation_sites={translation_sites:?}",
        top_level_sites = analysis.top_level_sites,
        top_level_drop_sites = snapshot.top_level_drop_sites,
        translation_sites = snapshot.translation_sites,
    );
    assert!(
        failed_drop_site.is_some_and(|site| {
            site.is_coroutine && site.local_ty.contains("Coroutine(") && site.debug_names.is_empty()
        }),
        "the localized cleanup drop should be the harness coroutine temporary, not a scheduler \
         dispatch site; failed_drop_site={failed_drop_site:?}, top_level_drop_sites={:?}",
        snapshot.top_level_drop_sites,
    );
    assert!(
        block_on_with_spawn_call_site.is_some_and(|site| {
            site.call_bb < site.target_bb
                && site.target_drop_local.is_none()
                && !site.target_drop_is_coroutine
                && site.post_drop_target.is_none()
                && failed_drop_site.is_some_and(|drop_site| site.target_bb < drop_site.bb_idx)
        }),
        "the block_on_with_spawn normal target should flow into a later harness cleanup block \
         rather than dropping the coroutine directly; block_on_with_spawn_call_site={block_on_with_spawn_call_site:?}, \
         failed_drop_site={failed_drop_site:?}, cfg_window={:?}",
        snapshot.cfg_window,
    );
}

#[test]
fn test_block_on_with_spawn_localizer_reports_current_head_drop_map() {
    let snapshot = run_spawn_localizer();
    let analysis = analyze_spawn_snapshot(&snapshot);
    emit_spawn_localizer_report(&snapshot, &analysis);
    assert_spawn_dispatch_localized(&snapshot, &analysis);
    assert_spawn_cleanup_residual(&snapshot, &analysis);
}

/// Documents the vtable gap between the simplified unit-test runtime and the
/// real Kani library (compiletest).
///
/// **Root cause (Part of #4075):** The simplified runtime compiles in a single
/// compilation unit, so `collect_dyn_trait_candidates` Phase 2 (MIR coercion
/// scan) sees all `Unsize` coercions. The inline walker can then resolve
/// vtable discriminants for `dyn Future` dispatch through the `Scheduler::run`
/// loop.
///
/// In the real Kani library (`library/trust_mc/src/futures.rs`), the `Unsize`
/// coercion from concrete coroutine to `BoxFuture = Pin<Box<dyn Future>>`
/// happens inside `Scheduler::spawn → Box::pin(fut)`, which is library code.
/// The vtable identity is lost through `Vec<Option<BoxFuture>>` storage:
///
/// 1. `Scheduler::spawn` → `Box::pin(fut)` creates vtable for concrete type
/// 2. `self.tasks.push(Some(boxed_future))` stores it in Vec
/// 3. `Scheduler::run` → `self.tasks[index]` reads back — vtable gone
/// 4. `fut.as_mut().poll(cx)` → `try_extract_vtable_discriminant` → fallback
///
/// This causes 21 `virtual_missing_vtable` in the compiletest report
/// (`reports/compiletest-per-harness-latest-spawn.json`), but 0 in this unit
/// test. The fix requires either:
/// - D2: propagate vtable identity through Vec/Option storage (deep)
/// - D3: add a specialized `block_on_with_spawn` dispatcher that models the
///   scheduler loop with vtable-preserving task dispatch (bounded)
#[test]
fn test_spawn_localizer_vtable_gap_is_zero_in_simplified_runtime() {
    let snapshot = run_spawn_localizer();
    let virtual_missing_vtable_count = snapshot.total_reason_count("virtual_missing_vtable");
    eprintln!(
        "[spawn vtable gap] virtual_missing_vtable in simplified runtime = {}, \
         expected = 0 (real Kani library has 21 per compiletest report); \
         translation_sites={:?}",
        virtual_missing_vtable_count, snapshot.translation_sites,
    );
    assert_eq!(
        virtual_missing_vtable_count, 0,
        "simplified runtime should have zero virtual_missing_vtable because all \
         types compile in one unit; the gap vs real harness (21) is the production \
         fix target. translation_sites={:?}",
        snapshot.translation_sites,
    );
}

#[test]
fn test_spawn_scheduler_run_vtable_model_stays_scoped_to_scheduler_run() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let source = build_async_spawn_unit_source(ASYNC_SPAWN_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2018", |ctx| {
        let harness_instance = find_instance_by_suffix(ctx.tcx, "round_robin_schedule_manual");
        let harness_body = harness_instance.body().expect("harness body");
        let mut chc_ctx = ChcCtx::new_with_instance(
            ctx.tcx,
            &harness_body,
            harness_instance,
            "round_robin_schedule_manual",
            ChcConfig::default(),
        );
        chc_ctx.spawn_scheduler_vtable_model =
            Some(crate::codegen_ay::chc::codegen_ctx::SpawnSchedulerVtableModel {
                poll_vtable_ids: vec![11, 22],
                next_poll_idx: 0,
                poll_task_indices: vec![0, 1],
                next_task_idx: 0,
                current_task_vtable_id: None,
                scheduler_loop_replay_fuel: None,
            });

        // After removing the instance check (e707017e06), vtable model provides
        // IDs whenever the model is active, regardless of current_instance.
        let vtable_expr = chc_ctx
            .try_consume_spawn_scheduler_run_vtable_expr()
            .expect("spawn model should provide vtable IDs when active");
        assert!(
            matches!(
                vtable_expr.value(),
                ExprValue::BitVecConst { value, width }
                    if *value == num_bigint::BigInt::from(11u64)
                        && *width == crate::codegen_ay::types::POINTER_WIDTH
            ),
            "should receive the first modeled poll vtable (id=11), got {vtable_expr}"
        );
        assert_eq!(
            chc_ctx.spawn_scheduler_vtable_model.as_ref().expect("spawn model").next_poll_idx,
            1,
            "should advance the poll schedule exactly once"
        );
        assert_eq!(
            chc_ctx
                .spawn_scheduler_vtable_model
                .as_ref()
                .expect("spawn model")
                .current_task_vtable_id,
            Some(11),
            "consuming a scheduler-run vtable should remember the active task slot"
        );
    });
}

#[test]
fn test_spawn_stubbed_type_arrays_stay_scoped_to_noop_waker_state() {
    let source = build_async_spawn_unit_source(ASYNC_SPAWN_REAL_FILE);
    crate::codegen_ay::context::with_test_ay_ctx_for_source_with_edition(&source, "2018", |ctx| {
        let harness_instance = find_instance_by_suffix(ctx.tcx, "round_robin_schedule_manual");
        let harness_body = harness_instance.body().expect("harness body");
        let mut chc_ctx = ChcCtx::new_with_instance(
            ctx.tcx,
            &harness_body,
            harness_instance,
            "round_robin_schedule_manual",
            ChcConfig::default(),
        );

        for type_key in [
            "ref_std_task_Waker",
            "ref_std_task_LocalWaker",
            "std_task_RawWaker",
            "std_task_Context",
            "std_panic_AssertUnwindSafe_core_task_wake_ExtData",
            "std_marker_PhantomData_ptr_unit",
            "kani_RoundRobin",
            "kani_futures_SchedulingAssumption",
            "kani_futures_JoinHandle",
            "kani_yield_now_YieldNow",
            "core_num_niche_types_UsizeNoHighBit",
        ] {
            assert!(
                !chc_ctx.should_stub_spawn_type_array(type_key),
                "spawn dead-state stubs must stay inactive outside the specialized spawn path"
            );
        }

        chc_ctx.spawn_scheduler_vtable_model =
            Some(crate::codegen_ay::chc::codegen_ctx::SpawnSchedulerVtableModel {
                poll_vtable_ids: vec![11, 22],
                next_poll_idx: 0,
                poll_task_indices: vec![0, 1],
                next_task_idx: 0,
                current_task_vtable_id: None,
                scheduler_loop_replay_fuel: None,
            });

        for type_key in [
            "ref_std_task_Waker",
            "ref_std_task_LocalWaker",
            "std_task_RawWaker",
            "std_task_Context",
            "std_panic_AssertUnwindSafe_core_task_wake_ExtData",
            "std_marker_PhantomData_ptr_unit",
            // Part of #4075 D2: scheduler-internal stubs
            "kani_RoundRobin",
            "ref_kani_RoundRobin",
            "kani_futures_SchedulingAssumption",
            "tuple_usize_kani_futures_SchedulingAssumption",
            "kani_futures_JoinHandle",
            "kani_yield_now_YieldNow",
            "ref_kani_yield_now_YieldNow",
            "core_num_niche_types_UsizeNoHighBit",
        ] {
            assert!(
                chc_ctx.should_stub_spawn_type_array(type_key),
                "spawn dead-state stubs should cover {type_key} while the spawn inline model is active"
            );
        }

        for type_key in [
            "std_boxed_Box_u8_std_alloc_Global",
            "trust_mc_futures_Scheduler",
            "std_sync_atomic_AtomicI64",
            "std_sync_Arc_std_sync_atomic_AtomicI64_std_alloc_Global",
        ] {
            assert!(
                !chc_ctx.should_stub_spawn_type_array(type_key),
                "proof-relevant spawn state must not be stubbed: {type_key}"
            );
        }
    });
}
