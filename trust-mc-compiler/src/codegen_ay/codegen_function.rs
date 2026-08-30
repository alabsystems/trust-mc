// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Single-function AY codegen: MIR body to AY constraints.
//!
//! Extracted from `compiler_interface.rs` to keep that module focused on the
//! `CodegenBackend` trait implementation and harness orchestration.

use crate::codegen_ay::chc::{ChcConfig, ChcDebugMode, WideMemMode, mir_to_chc_with_instance};
use crate::codegen_ay::context::AYCtx;
use crate::codegen_ay::statement::StatementCodegen;
use crate::kani_middle::attributes;
use crate::kani_middle::reachability::is_prefix_abstracted;
use crate::kani_middle::tuple_usage::TupleUsageAnalysis;
use rustc_public::mir::{Operand, TerminatorKind};
use std::collections::{HashMap, VecDeque};
use std::panic::{AssertUnwindSafe, catch_unwind};
use tracing::{debug, debug_span};
use trust_mc_core::chc::{RelationApp, RelationDecl, Rule, RuleBody};

use super::loop_unroll;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};

/// Generate AY constraints for a single function.
///
/// Processes the MIR body and generates AY SMT constraints for verification
/// using the `StatementCodegen`.
///
/// Uses a single-pass worklist traversal that propagates (path_condition,
/// environment) forward through the CFG. This fixes the stale-SSA issue (#155)
/// where pass-1 path conditions could reference stale SSA names, and implements
/// phi/merge for branch-assigned locals (#129).
pub(super) fn codegen_function(
    ay_ctx: &mut AYCtx<'_, '_>,
    instance: rustc_public::mir::mono::Instance,
) {
    let name = instance.name();
    let _trace_span = debug_span!("AYCodegenFunction", name = %name).entered();

    // Set up function context
    ay_ctx.set_current_fn(instance);

    // Get the MIR body for this function.
    let body = ay_ctx.body(instance);
    codegen_function_with_body(ay_ctx, instance, body, &name);
}

pub(crate) fn codegen_function_with_body(
    ay_ctx: &mut AYCtx<'_, '_>,
    instance: rustc_public::mir::mono::Instance,
    body: rustc_public::mir::Body,
    name: &str,
) {
    // Positive evidence that zero checks means "nothing to prove", not "we
    // dropped it": no obligation SITE is reachable from this body.
    //
    // This used to require no `Call` terminator AT ALL, which refused every
    // harness that called anything — `bar();`, `Path::new(..)`, `println!(..)`
    // are all calls, and all of them were left VACUOUS. The walk asks the same
    // question of every body it can reach instead, and is fail-closed on
    // anything it cannot see (indirect/virtual callee, absent body, inline
    // asm, budget). `Option::unwrap` still fails it: its body asserts.
    // Callees are resolved THROUGH the unit's stub map, so the walk inspects
    // the same program the encoder encodes. A stub can ADD an obligation the
    // original lacks — `#[kani::stub(clean, panicking)]` once made the walk see
    // `clean`, find nothing to prove, and CERTIFY a harness whose emitted check
    // FAILS — and walking the original is exactly how that happened.
    //
    // This replaces a blunt "refuse any stubbed unit" gate, which was sound but
    // cost `tests/kani/Stubbing/glob_{cycle,path}.rs`. No transformer (a test
    // context) still fails closed: an empty map cannot resolve a stub, so the
    // certificate is refused wherever a stub would have mattered.
    let stubs = ay_ctx.transformer_stub_map();
    let obligation_free =
        crate::codegen_ay::obligation_free_walk::body_is_transitively_obligation_free(
            ay_ctx.tcx, instance, &body, &stubs,
        );
    ay_ctx.obligation_free_body_by_fn.insert(name.to_string(), obligation_free);
    tracing::debug!(name, certified = obligation_free, "obligation-free walk");
    // Contract-heavy functions can require more than the default inline depth
    // to fully inline `kani_register_contract`/closure-call shims.
    // If we stop early, BMC falls back to symbolic closure results and can
    // miss contract assumptions in stub-verified harnesses (#1836).
    //
    // The direct-body scan (`needs_contract_inline_boost`) only fires when the
    // contract shims appear in THIS function. But a `#[kani::stub_verified]`
    // harness reaches the replace stub (and its `apply_closure`/`run_contract_fn`
    // chain) only TRANSITIVELY (e.g. aterm's parser_never_panics ->
    // advance -> process_byte -> process_byte_inner-stub -> apply_closure), so
    // the direct scan misses it and the ensures-closure application leaks as a
    // `Call terminator`. Whenever stubbing is enabled the run may inline such a
    // chain, so boost as well — deeper inlining is always sound (it only
    // eliminates more Call terminators).
    let mut inline_depth = ay_ctx.config.inline_depth;
    let stubbing_active = ay_ctx.queries.args().stubbing_enabled;
    // An `async` harness (the proof macro wraps it in `kani::block_on`) spends
    // the default budget on the executor's own shims (`Context::from_waker`,
    // `Pin::new_unchecked`, `Pin::as_mut`, the outer coroutine `poll`) before
    // the first `.await`'s inner `poll` is reached; whatever is left un-inlined
    // falls to the statement mini-inliner, which cannot take a body with a
    // loop. BMC only — CHC keeps `block_on` as a call boundary.
    let async_harness = !ay_ctx.config.use_chc && body_calls_block_on(&body);
    if ay_ctx.config.function_inlining
        && inline_depth < 32
        && (stubbing_active || needs_contract_inline_boost(&body) || async_harness)
    {
        debug!(
            "AY codegen: boosting inline depth for contract-instrumented fn {} ({} -> 32)",
            name, inline_depth
        );
        inline_depth = 32;
    }

    // Apply function inlining to eliminate Call terminators.
    // This is needed because AY backend doesn't support function calls natively.
    debug!(
        "AY codegen: about to apply function inlining to {} (enabled={}, depth={})",
        name, ay_ctx.config.function_inlining, inline_depth
    );
    let mut inline_pass = FunctionInlinePass::new(InlineConfig {
        max_depth: inline_depth,
        enabled: ay_ctx.config.function_inlining,
        // CHC keeps `block_on` as a boundary for its single-poll specializer;
        // BMC inlines it so the busy-poll loop is unrolled with the harness.
        preserve_block_on: ay_ctx.config.use_chc,
    });
    let (inlined, mut body) =
        inline_pass.transform_with_body_provider(ay_ctx.tcx, body, instance, |callee_instance| {
            if !callee_instance.has_body() {
                return None;
            }
            // Part of #2967, #3012: Don't inline stdlib functions that are in
            // the abstraction boundary. The stub dispatch chain handles these
            // via stubs in both CHC and BMC modes. Inlining them replaces
            // Call terminators with concrete MIR that operates on abstract
            // datatypes (Slice, Vec, VecIntoIter), causing type mismatches
            // (BV→DT casts) and dual-model conflicts with stubs.
            let callee_name = callee_instance.name();
            if is_prefix_abstracted(&callee_name) {
                debug!("skip inlining abstracted function: {}", callee_name);
                return None;
            }
            // Part of #3924: In CHC mode, don't inline kani::any_where — the
            // CHC translator has a dedicated handler (try_dispatch_call_any_where)
            // that correctly resolves closure captures and bridges the nondet
            // result with the predicate. MIR-inlining any_where breaks this:
            // the closure call becomes an opaque inferable predicate,
            // disconnecting the assume from the returned value.
            // BMC mode is unaffected — it handles the inlined any/assume/closure
            // primitives individually via StatementCodegen.
            if ay_ctx.config.use_chc
                && (callee_name.ends_with("::any_where") || callee_name.contains("::any_where::"))
            {
                debug!("skip inlining any_where in CHC mode (dedicated handler): {}", callee_name);
                return None;
            }
            // CHC has a metadata-preserving handler for `str::as_bytes`. If
            // the MIR pre-inline pass erases the call, static string byte
            // backing is lost and later `bytes[i]` assertions fall back to
            // unconstrained memory selects.
            if ay_ctx.config.use_chc
                && callee_name.contains("<impl str>")
                && callee_name.ends_with("::as_bytes")
            {
                debug!(
                    "skip inlining str::as_bytes in CHC mode (dedicated handler): {}",
                    callee_name
                );
                return None;
            }
            ay_ctx.body_or_instance_body(callee_instance)
        });
    if inlined {
        debug!("AY codegen: inlined function calls in {}", name);
    }

    // Construct-derived unwind bound from a specialized C-variadic call.
    // `va_arg` past the end of the actual list is UB and its bounds obligation
    // fails there, so no non-failing execution runs a fetching loop body more
    // than `n` times; `n + 2` covers those iterations plus the exit test.
    // Unrolling itself stays fail-closed regardless of the bound: the exhausted
    // back-edge becomes an unwinding-assertion error edge, so a bound that is
    // too small FAILS loudly instead of proving anything vacuously.
    const VARIADIC_UNROLL_DEPTH_CAP: usize = 16;
    let variadic_unroll_depth: Option<u32> = inline_pass
        .variadic_actual_bound()
        .map(|n| n + 2)
        .filter(|d| *d <= VARIADIC_UNROLL_DEPTH_CAP)
        .map(|d| d as u32);

    // Construct-derived unwind bound from a CONSTANT-TRIP-COUNT loop.
    //
    // With no user bound the depth is 1, so `unroll_cfg_loops` cuts a loop's
    // last back-edge into the unwinding-assertion sentinel and everything after
    // the loop becomes reachable only through paths that truncation removed —
    // post-loop checks come back UNREACHABLE instead of getting a verdict.
    // Kani's default is CBMC *complete* unwinding, so a loop with a statically
    // computable trip count is fully unrolled there. This derives that trip
    // count per body (see `loop_unroll::const_trip`) rather than raising the
    // default for everyone: memory is already bounded, but a deeper unroll is a
    // strictly bigger solver query, so the bound has to be earned per loop.
    //
    // Two gates, both fail-open to today's behaviour:
    //   * `has_explicit_unwind` — a user bound (`--unwind`, `--default-unwind`,
    //     `#[kani::unwind(N)]`) must keep today's behaviour EXACTLY, including
    //     the tests that pin `unwinding assertion loop N: FAILURE`.
    //   * `unwinding_assertions` — the derived bound is only safe BECAUSE an
    //     exhausted back-edge is still an error edge. With unwinding assertions
    //     off a mis-derived bound would truncate silently, so we derive nothing.
    // CHC is deliberately left alone: it expresses loops as recursive predicates
    // and needs no bound, so unrolling there would only enlarge the query.
    let const_trip_unroll_depth: Option<u32> = if ay_ctx.config.use_chc
        || ay_ctx.config.has_explicit_unwind
        || !ay_ctx.config.unwinding_assertions
    {
        None
    } else {
        loop_unroll::derive_const_trip_unroll_depth(&body)
    };
    if let Some(depth) = const_trip_unroll_depth {
        debug!(name, depth, "derived a constant-trip-count unwind bound");
    }

    // Unsupported captures deliberately leave the original role-0 register
    // call in place. Scan after inlining so a contracted loop in a helper
    // cannot evade the harness-level fail-closed gate; the register function
    // is `#[inline(never)]`, so its breadcrumb survives the inline pass.
    let loop_contracts_enabled =
        ay_ctx.queries.args().unstable_features.iter().any(|f| f == "loop-contracts");
    if loop_contracts_enabled && body_has_untransformed_loop_contract_call(&body) {
        debug!(name, "unsupported loop invariant capture retained its register-call breadcrumb");
        ay_ctx.unsupported("loop invariant captures unsupported dereference", name.to_owned());
        if ay_ctx.config.use_chc {
            let mut failing_vc = trust_mc_core::chc::ChcVc::new();
            failing_vc.add_relation(RelationDecl::nullary("chc_loop_contract_unsupported"));
            failing_vc.add_rule(Rule::new(
                RuleBody::new(None, vec![]),
                RelationApp::nullary("chc_loop_contract_unsupported"),
            ));
            failing_vc.query.target = Some("chc_loop_contract_unsupported".to_string());
            ay_ctx.chc_vc = Some(failing_vc);
        } else {
            ay_ctx.record_property_violation(
                ay_bindings::Expr::bool_const(true),
                "unsupported_loop_contract",
            );
        }
        ay_ctx.reset_current_fn();
        return;
    }

    // CHC mode: use mir_to_chc to translate MIR to Horn clauses.
    // CHC can express loops as recursive predicates, so no unrolling is needed
    // for unbounded loops. However, when the user provides a bounded unwind hint
    // (#[kani::unwind(N)]), we can unroll constant-bound loops BEFORE CHC encoding,
    // converting them into acyclic straight-line programs. This eliminates the
    // need for PDR to synthesize loop invariants, which is critical for wider
    // bitvector types (BV32+) where invariant synthesis times out.
    tracing::debug!("AY codegen: use_chc={} for fn={}", ay_ctx.config.use_chc, name);
    if ay_ctx.config.use_chc {
        // When --ay-chc-bounded-unroll is set and the body has loops with a
        // known unwind bound, apply bounded unrolling to make the CFG acyclic.
        let cfg = loop_unroll::Cfg::from_body(&body);
        // Gate on `has_explicit_unwind` (not `unwind_depth > 1`) so an explicit
        // `#[kani::unwind(1)]` on a cyclic body still unrolls to depth 1 and emits
        // the unwinding-assertion error edge for a loop that cannot terminate
        // within the bound (SOUNDNESS: a non-terminating `loop {}` under unwind(1)
        // must FAIL, not be vacuously proved safe).
        // A user unwind hint wins when present; otherwise a specialized variadic
        // call supplies its own bound (with unwinding assertions forced ON —
        // this bound is derived by the encoder, not requested by the user, so it
        // must never be allowed to silently truncate an execution).
        let unroll_request: Option<(u32, bool)> =
            if ay_ctx.config.chc_bounded_unroll && ay_ctx.config.has_explicit_unwind {
                Some((ay_ctx.config.unwind_depth, ay_ctx.config.unwinding_assertions))
            } else {
                variadic_unroll_depth.map(|depth| (depth, true))
            };
        if let Some((unroll_depth, unroll_assertions)) = unroll_request
            && !cfg.is_acyclic()
        {
            debug!(
                "AY codegen CHC: body has loops, applying bounded unrolling (depth={}) before CHC encoding for {}",
                unroll_depth, name
            );
            match loop_unroll::unroll_cfg_loops(body.clone(), unroll_depth, unroll_assertions) {
                Ok(unrolled) => {
                    body = unrolled;
                    debug!(
                        "AY codegen CHC: loop unrolling succeeded for {}, {} blocks (acyclic)",
                        name,
                        body.blocks.len()
                    );
                }
                Err(err) => {
                    // Unrolling failed — fall through to standard CHC encoding
                    // which will handle loops as recursive predicates.
                    debug!(
                        "AY codegen CHC: loop unrolling failed for {} ({:?}), falling back to CHC loop encoding",
                        name, err
                    );
                }
            }
        }
        codegen_chc_path(ay_ctx, &body, &name);
        return;
    }

    // BMC path: continue with topological traversal and StatementCodegen.
    debug!("AY codegen: using BMC path for {}", name);

    let (mut topo_order, mut reachable_count) = compute_topo(&body);

    if topo_order.len() != reachable_count {
        // A specialized variadic call bounds its own fetching loop; take the
        // deeper of the two so the BMC twin does not truncate a fetch sequence
        // the model can already discharge.
        let bmc_unwind_depth = ay_ctx
            .config
            .unwind_depth
            .max(variadic_unroll_depth.unwrap_or(0))
            .max(const_trip_unroll_depth.unwrap_or(0));
        debug!(
            "AY codegen: CFG cycle detected in {}, attempting bounded unrolling (depth={})",
            name, bmc_unwind_depth
        );
        match loop_unroll::unroll_cfg_loops(
            body,
            bmc_unwind_depth,
            ay_ctx.config.unwinding_assertions,
        ) {
            Ok(unrolled) => {
                body = unrolled;
                (topo_order, reachable_count) = compute_topo(&body);
            }
            Err(err) => {
                let location = format!("function {} has CFG cycle ({err:?})", name);
                ay_ctx.unsupported("CFG cycle/loop", location);
                ay_ctx.record_property_violation(
                    ay_bindings::Expr::bool_const(true),
                    "unsupported_cfg_cycle",
                );
                ay_ctx.reset_current_fn();
                return;
            }
        }
    }

    if topo_order.len() != reachable_count {
        let location = format!("function {} has CFG cycle (unrolling failed)", name);
        ay_ctx.unsupported("CFG cycle/loop", location);
        ay_ctx.record_property_violation(
            ay_bindings::Expr::bool_const(true),
            "unsupported_cfg_cycle",
        );
        ay_ctx.reset_current_fn();
        return;
    }

    debug!(
        "AY codegen function {} with {} blocks, topo_order len={}",
        name,
        body.blocks.len(),
        topo_order.len()
    );

    // Error recovery boundary (#3739): catch panics from unsupported MIR
    // patterns in the BMC path (e.g., multi-level Box pointer chain gaps)
    // and convert them to a CTREX verdict instead of crashing the compiler.
    // Mirrors the CHC protection at line 254.
    let tuple_usage = TupleUsageAnalysis::run(&body);
    let result = catch_unwind(AssertUnwindSafe(|| {
        let mut codegen = StatementCodegen::new(ay_ctx, &body, tuple_usage);

        for bb_idx in topo_order {
            let block = &body.blocks[bb_idx];
            debug!("AY codegen block {} with {} statements", bb_idx, block.statements.len());

            codegen.initialize_block_entry_env(bb_idx);

            for stmt in &block.statements {
                codegen.codegen_statement(stmt);
            }

            tracing::debug!(
                "AY codegen: calling codegen_terminator_with_successors for bb_idx={}",
                bb_idx
            );
            let successors = codegen.codegen_terminator_with_successors(&block.terminator);
            for (target_bb, branch_cond) in successors {
                codegen.record_outgoing_edge(target_bb, branch_cond);
            }
        }
    }));

    match result {
        Ok(()) => {}
        Err(panic_payload) => {
            let panic_msg = panic_payload
                .downcast_ref::<String>()
                .map(|s| s.as_str())
                .or_else(|| panic_payload.downcast_ref::<&str>().copied())
                .unwrap_or("unknown panic");
            let location = format!("BMC codegen panic in {}: {}", name, panic_msg);
            tracing::error!("{}", location);
            ay_ctx.unsupported("BMC codegen panic", location);
            ay_ctx.record_property_violation(
                ay_bindings::Expr::bool_const(true),
                "bmc_codegen_panic",
            );
        }
    }

    // Clean up function context
    ay_ctx.reset_current_fn();
}

/// Whether `body` still contains a call to a `kani_register_loop_decreases<id>`
/// register function — the lowering of a `#[kani::loop_decreases(...)]` clause.
/// The register fn is `#[inline(never)]`, so the call survives function inlining
/// (unlike the invariant register, which `LoopContractPass` rewrites away),
/// letting CHC codegen detect a decreases clause even when the guarded loop lives
/// in an inlined helper rather than the harness body directly.
/// Whether any local (or its immediate ADT fields) is union-typed — the
/// scalar shadow-memory model does not track initialization re-shaping
/// through union field accesses (`-Z uninit-checks` fail-closed gate).
pub(in crate::codegen_ay) fn body_has_union_local(body: &rustc_public::mir::Body) -> bool {
    use rustc_public::ty::{AdtKind, RigidTy, TyKind};
    body.locals().iter().any(|decl| {
        matches!(
            decl.ty.kind(),
            TyKind::RigidTy(RigidTy::Adt(def, _)) if def.kind() == AdtKind::Union
        )
    })
}

/// Whether the body directly calls `Vec::set_len` (or `String::set_len`) —
/// `set_len` extends the logical length over UNINITIALIZED reserved capacity
/// (e.g. after `Vec::with_capacity`). The scalar shadow-memory model does not
/// track the initialization status of those bytes, so a subsequent read of the
/// grown region falsely proves Safe (`expected/uninit/vec-read-bad-len.rs`
/// reads uninit bytes and is UB). `-Z uninit-checks` fail-closed gate — the raw
/// alloc gate above only fires when the *harness* calls the allocator directly,
/// but `Vec::with_capacity` hides the alloc inside the callee, so the uninit
/// exposure surfaces only at the `set_len` call site.
pub(in crate::codegen_ay) fn body_has_vec_set_len_call(body: &rustc_public::mir::Body) -> bool {
    // `Vec::<T>::set_len` / `String::set_len` render as `...::set_len`. Match the
    // method segment specifically so unrelated `*set_len*` helpers (none in std)
    // do not over-trigger.
    body_any_call_name(body, |name| name.contains("::set_len"))
}

/// Iterate the fully-qualified callee name of every `Call` terminator in the
/// body, applying `pred`. Shared by the set_len/contract/quantifier body scans.
fn body_any_call_name(body: &rustc_public::mir::Body, pred: impl Fn(&str) -> bool) -> bool {
    body.blocks.iter().any(|bb| {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            return false;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            return false;
        };
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(fn_def, _)) =
            func_ty.kind()
        else {
            return false;
        };
        pred(&fn_def.0.name())
    })
}

/// Whether the body calls a Kani quantifier intrinsic (`kani::forall!` /
/// `kani::exists!`, lowered to `kani::internal::kani_forall` / `kani_exists`).
pub(in crate::codegen_ay) fn body_has_kani_quantifier_call(body: &rustc_public::mir::Body) -> bool {
    body_any_call_name(body, |name| name.contains("kani_forall") || name.contains("kani_exists"))
}

/// Whether the body is a `#[kani::proof_for_contract]` CHECK harness — the
/// flattened body dispatches the contract via `kani::internal::init_contracts`
/// (emitted once per contract-proof harness) and/or `run_contract_fn` /
/// `kani_register_contract`. Used only to scope the quantified-postcondition
/// fail-closed gate to contract proofs, so plain `kani::assert(forall!(...))`
/// proofs are untouched.
pub(in crate::codegen_ay) fn body_has_contract_dispatch(body: &rustc_public::mir::Body) -> bool {
    body_any_call_name(body, |name| {
        name.contains("init_contracts")
            || name.contains("run_contract_fn")
            || name.contains("kani_register_contract")
    })
}

/// Whether a `#[kani::loop_decreases]` register call survives on a REACHABLE
/// path of the body (unsupported measure shapes leave it in place).
///
/// Only live blocks count — see [`reachable_blocks`]: the contract-mode fold
/// strands a verbatim copy of the loop, decreases breadcrumb included, in the
/// arms this harness did not select.
fn body_has_loop_decreases_call(body: &rustc_public::mir::Body) -> bool {
    let reachable = reachable_blocks(body);
    body.blocks.iter().enumerate().any(|(bb_idx, bb)| {
        if !reachable[bb_idx] {
            return false;
        }
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            return false;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            return false;
        };
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(fn_def, _)) =
            func_ty.kind()
        else {
            return false;
        };
        fn_def.0.name().contains("kani_register_loop_decreases")
    })
}

/// Blocks reachable from the entry block by following terminator successors.
///
/// `FunctionWithContractPass` selects one contract mode per harness and folds
/// `kani_contract_mode()` to a constant, which strands the arms this harness did
/// not select. For a `#[kani::requires]`/`#[kani::ensures]` function those
/// stranded arms contain a VERBATIM COPY of the original body — loop included,
/// with its own role-0 `kani_register_loop_contract` breadcrumb and its own
/// nested register `fn` (`f::kani_register_loop_contract_<id>` alongside the
/// live `f::{closure#N}::…::kani_register_loop_contract_<id>`). The stranded
/// blocks have no predecessor, so `LoopContractPass`' control-flow-ordered walk
/// never rewrites them, and the CHC inliner copies whole block lists, carrying
/// them into the harness body.
///
/// Breadcrumb scans therefore have to look at the LIVE CFG only: a call that no
/// execution can reach imposes no obligation to discharge, so treating it as an
/// unsupported construct fabricates a verdict instead of deriving one.
fn reachable_blocks(body: &rustc_public::mir::Body) -> Vec<bool> {
    let mut reachable = vec![false; body.blocks.len()];
    if body.blocks.is_empty() {
        return reachable;
    }
    reachable[0] = true;
    let mut worklist = vec![0usize];
    while let Some(bb) = worklist.pop() {
        for succ in body.blocks[bb].terminator.successors() {
            if let Some(seen) = reachable.get_mut(succ)
                && !*seen
            {
                *seen = true;
                worklist.push(succ);
            }
        }
    }
    reachable
}

/// Whether loop-contract lowering left an original (`_transformed == 0`)
/// register call on a REACHABLE path of the body. The lowering pass
/// deliberately retains this breadcrumb when an invariant capture cannot be
/// represented soundly.
///
/// Only live blocks count — see [`reachable_blocks`]. The live latch call the
/// successful lowering emits carries `_transformed == 1`, so a role-0 call that
/// is still reachable really does mean an un-lowered invariant.
fn body_has_untransformed_loop_contract_call(body: &rustc_public::mir::Body) -> bool {
    let reachable = reachable_blocks(body);
    body.blocks.iter().enumerate().any(|(bb_idx, bb)| {
        if !reachable[bb_idx] {
            return false;
        }
        let TerminatorKind::Call { func, args, .. } = &bb.terminator.kind else {
            return false;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            return false;
        };
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(fn_def, _)) =
            func_ty.kind()
        else {
            return false;
        };
        if !fn_def.0.name().contains("kani_register_loop_contract") {
            return false;
        }
        matches!(
            args.get(1),
            Some(Operand::Constant(value))
                if value.const_.eval_target_usize().ok() == Some(0)
        )
    })
}

/// CHC path: translate MIR to Horn clauses.
///
/// Wraps `mir_to_chc` in a `catch_unwind` boundary so that panics from
/// unsupported MIR patterns (`.expect()`, `panic!` in the 132-file CHC
/// pipeline) produce a CTREX verdict for that one harness instead of
/// crashing the entire verification run. Part of #3124.
fn codegen_chc_path(ay_ctx: &mut AYCtx<'_, '_>, body: &rustc_public::mir::Body, name: &str) {
    tracing::debug!("AY codegen: taking CHC path for {}", name);
    let instance =
        ay_ctx.current_fn().expect("CHC path requires active current_fn context").instance;
    let mut local_to_state_idx = HashMap::new();
    for (local_idx, _local_decl) in body.local_decls() {
        let vec_idx = local_to_state_idx.len();
        local_to_state_idx.insert(local_idx, vec_idx);
    }
    ay_ctx.record_chc_local_to_state_idx(name, local_to_state_idx);

    // Loop `decreases` clauses (loop variants) are unsupported: trust-mc proves
    // partial correctness of loops via `#[kani::loop_invariant]`, but does not
    // discharge the ranking/measure obligation a decreases clause imposes. When
    // `-Z loop-contracts` is active and this body (post-inline) still carries a
    // `kani_register_loop_decreases` call, degrade CONSERVATIVELY to a failing VC
    // (never a false PROOF from silently ignoring a stale or increasing measure)
    // and record it as an unsupported construct, so the harness reports FAILED
    // with a clean "unsupported" verdict. The feature gate is required because the
    // Kani macro emits the register call regardless of the flag; without
    // `-Z loop-contracts` the clause is a no-op (Kani ignores it too), so gating
    // keeps flag-less proofs (`decreases_no_flag`) intact.
    let loop_contracts_enabled =
        ay_ctx.queries.args().unstable_features.iter().any(|f| f == "loop-contracts");
    if loop_contracts_enabled && body_has_loop_decreases_call(body) {
        debug!(name, "CHC: loop `decreases` ranking not proven — attributed failing VC");
        // Say so out loud, once per body. Reaching here means
        // `instrument_loop_decreases` did NOT encode this measure (the register
        // call survived the pass), so the clause really is unhandled and the
        // failing VC below is a conservative stand-in rather than a discharged
        // ranking obligation. The failing VC stays exactly as it was — this
        // line only states the limitation the verdict already encodes, which is
        // what `tests/expected/loop-contract/loop_decreases_unsupported` reads.
        ay_ctx.tcx.dcx().warn(
            "`#[kani::loop_decreases]` is parsed but termination checking for loop \
             variants is not supported by trust-mc yet",
        );
        // Attributed failing VC: a registered `loop_decreases` PROPERTY whose
        // error_p1 relation is a reachable fact, bridged into the aggregate
        // `error` query. The harness reports a named failing check
        // (`<harness>.loop_decreases.1`, Status: FAILURE) exactly like Kani,
        // whose CBMC lowering fails the ranking check it cannot discharge —
        // instead of the former UNSUPPORTED-construct report, which kept
        // correct FAILED verdicts (oracle=fail decreases tests) out of parity.
        // Fail-closed as before: never a false PROOF from ignoring a stale or
        // increasing measure. Id 1 matches Kani's 1-based check numbering so
        // expected files matching `loop_decreases.1` line up.
        let mut failing_vc = trust_mc_core::chc::ChcVc::new();
        failing_vc.add_relation(RelationDecl::nullary("error_p1"));
        failing_vc.add_relation(RelationDecl::nullary("error"));
        failing_vc
            .add_rule(Rule::new(RuleBody::new(None, vec![]), RelationApp::nullary("error_p1")));
        failing_vc.add_rule(Rule::new(
            RuleBody::new(Some(RelationApp::nullary("error_p1")), vec![]),
            RelationApp::nullary("error"),
        ));
        failing_vc.query.target = Some("error".to_string());
        failing_vc.add_property(trust_mc_core::chc::ChcProperty {
            id: 1,
            kind: trust_mc_core::violation::PropertyKind::LoopDecreases,
            bb: 0,
            relation: "error_p1".to_string(),
            message: Some("loop `decreases` ranking not proven (termination measure)".to_string()),
            location: None,
            approximation_dependent: Some(false),
        });
        ay_ctx.chc_vc = Some(failing_vc);
        ay_ctx.reset_current_fn();
        return;
    }

    // Extract config values before the catch_unwind boundary.
    // mir_to_chc takes only these values (not ay_ctx itself), so the
    // mutable borrow on ay_ctx is not held across the unwind boundary.
    let tcx = ay_ctx.tcx;
    let chc_cfg = ChcConfig {
        frame_narrowing: crate::codegen_ay::chc::frame_narrowing_enabled(),
        frame_narrowing_flattened: crate::codegen_ay::chc::frame_narrowing_flattened_enabled(),
        track_level: ay_ctx.config.chc_track_level,
        step_mode: ay_ctx.config.chc_step_mode,
        int_lift: ay_ctx.config.chc_int_lift,
        chc_debug: ChcDebugMode::from(ay_ctx.queries.args().ay_chc_debug),
        wide_mem: WideMemMode::from(ay_ctx.config.ay_wide_mem),
        extra_pointer_checks: ay_ctx.config.extra_pointer_checks,
        prove_safety_only: ay_ctx.config.prove_safety_only,
        memory_safety_checks: ay_ctx.config.memory_safety_checks,
        overflow_checks: ay_ctx.config.overflow_checks,
        nan_checks: ay_ctx.config.nan_checks,
        undefined_function_checks: ay_ctx.config.undefined_function_checks,
        recursive_unwind_depth: if ay_ctx.config.has_explicit_unwind {
            ay_ctx.config.unwind_depth
        } else {
            0 // 0 means "use MAX_INLINE_DEPTH" per walker.rs gate
        },
        unwinding_assertions: ay_ctx.config.unwinding_assertions,
        uninit_checks: ay_ctx.config.uninit_checks,
        // P2-S1: contract CHECK harnesses must havoc mutable/interior-mut
        // statics (Kani `--enforce-contract` semantics) instead of pinning
        // them to initializers. `stub_verified`-only harnesses are NOT
        // included: replacement havocs its `modifies` targets at the call
        // site (existing mechanism), matching Kani.
        contract_static_havoc: ay_ctx.config.is_contract_proof,
    };

    // Route the CHC inline walker's callee-body fetches through the SAME
    // transform pipeline the non-inline lane uses. Without this, walked
    // contract chains see raw bodies where `kani_contract_mode()` is the macro
    // dummy ORIGINAL=0, making every walked ensures/requires check vacuous.
    // The guard uninstalls the snapshot on drop (also on unwind).
    let _walker_transformer = ay_ctx.install_walker_transformer();

    // Error recovery boundary (#3124): catch panics from unsupported MIR
    // patterns and convert them to a trivially-failing CHC VC instead of
    // crashing the entire verification process.
    let result = catch_unwind(AssertUnwindSafe(|| {
        mir_to_chc_with_instance(tcx, body, instance, name, chc_cfg)
    }));

    match result {
        Ok(chc_vc) => {
            ay_ctx.chc_vc = Some(chc_vc);
        }
        Err(panic_payload) => {
            let panic_msg = panic_payload
                .downcast_ref::<String>()
                .map(|s| s.as_str())
                .or_else(|| panic_payload.downcast_ref::<&str>().copied())
                .unwrap_or("unknown panic");
            let location = format!("CHC codegen panic in {}: {}", name, panic_msg);
            tracing::error!("{}", location);

            // Record the unsupported construct for diagnostic reporting.
            ay_ctx.unsupported("CHC codegen panic", location);

            // Create a trivially-failing CHC VC: a single fact rule makes
            // the error relation reachable, so the solver returns CTREX
            // rather than giving a false PROOF from an empty program.
            let mut failing_vc = trust_mc_core::chc::ChcVc::new();
            failing_vc.add_relation(RelationDecl::nullary("chc_codegen_error"));
            failing_vc.add_rule(Rule::new(
                RuleBody::new(None, vec![]),
                RelationApp::nullary("chc_codegen_error"),
            ));
            failing_vc.query.target = Some("chc_codegen_error".to_string());
            ay_ctx.chc_vc = Some(failing_vc);
        }
    }
    ay_ctx.reset_current_fn();
}

/// Check if a function body contains contract-related calls that need deeper inlining.
fn is_closure_shim_name(fn_name: &str) -> bool {
    fn_name.contains("FnOnce::call_once")
        || fn_name.contains("FnMut::call_mut")
        || fn_name.contains("::Fn::call")
}

fn is_contract_marker_name(marker: &str) -> bool {
    matches!(
        marker,
        "kani_contract_mode"
            | "kani_force_fn_once"
            | "kani_force_fn_once_with_args"
            | "kani_register_contract"
    )
}

/// Check if a function body contains contract-related calls that need deeper inlining.
fn needs_contract_inline_boost(body: &rustc_public::mir::Body) -> bool {
    for bb in &body.blocks {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            continue;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            continue;
        };
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(fn_def, _)) =
            func_ty.kind()
        else {
            continue;
        };
        let fn_name = fn_def.0.name();
        if is_closure_shim_name(&fn_name) {
            return true;
        }
        let Some(marker) = attributes::fn_marker(fn_def) else {
            continue;
        };
        if is_contract_marker_name(marker.as_str()) {
            return true;
        }
    }
    false
}

/// Does `body` call a `block_on` executor (`kani::block_on` or a user-defined
/// twin)? That is the signature of an `async` harness: `#[kani::proof] async
/// fn h()` expands to `fn h() { async fn h() {..} kani::block_on(h()) }`.
fn body_calls_block_on(body: &rustc_public::mir::Body) -> bool {
    body.blocks.iter().any(|bb| {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else {
            return false;
        };
        let Ok(func_ty) = func.ty(body.locals()) else {
            return false;
        };
        let rustc_public::ty::TyKind::RigidTy(rustc_public::ty::RigidTy::FnDef(fn_def, _)) =
            func_ty.kind()
        else {
            return false;
        };
        let fn_name = fn_def.0.name();
        fn_name == "block_on" || fn_name.ends_with("::block_on")
    })
}

/// Compute a topological order for the reachable CFG (or detect cycles).
///
/// Returns `(topo_order, reachable_count)`. If `topo_order.len() < reachable_count`,
/// the CFG contains cycles (loops) that need unrolling before BMC encoding.
fn compute_topo(body: &rustc_public::mir::Body) -> (Vec<usize>, usize) {
    let block_count = body.blocks.len();
    let mut successors: Vec<Vec<usize>> = vec![Vec::new(); block_count];

    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let mut succs = match &block.terminator.kind {
            TerminatorKind::Goto { target } => vec![*target],
            TerminatorKind::SwitchInt { targets, .. } => {
                let mut succs: Vec<usize> =
                    targets.branches().map(|(_case_val, target)| target).collect();
                succs.push(targets.otherwise());
                succs
            }
            TerminatorKind::Drop { target, .. } => vec![*target],
            TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
            TerminatorKind::Assert { target, .. } => vec![*target],
            TerminatorKind::Return | TerminatorKind::Unreachable => vec![],
            TerminatorKind::Resume | TerminatorKind::Abort => vec![],
            TerminatorKind::InlineAsm { destination, .. } => destination.iter().copied().collect(),
        };
        succs.sort_unstable();
        succs.dedup();
        successors[bb_idx] = succs;
    }

    // Reachable from entry (bb0).
    let mut reachable = vec![false; block_count];
    let mut reach_q: VecDeque<usize> = VecDeque::new();
    reachable[0] = true;
    reach_q.push_back(0);
    while let Some(bb) = reach_q.pop_front() {
        for &succ in &successors[bb] {
            if !reachable[succ] {
                reachable[succ] = true;
                reach_q.push_back(succ);
            }
        }
    }

    // Topological sort on reachable subgraph.
    let mut indegree = vec![0usize; block_count];
    for bb in 0..block_count {
        if !reachable[bb] {
            continue;
        }
        for &succ in &successors[bb] {
            if reachable[succ] {
                indegree[succ] += 1;
            }
        }
    }

    let mut topo_q: VecDeque<usize> = VecDeque::new();
    for bb in 0..block_count {
        if reachable[bb] && indegree[bb] == 0 {
            topo_q.push_back(bb);
        }
    }

    let mut topo_order = Vec::with_capacity(block_count);
    while let Some(bb) = topo_q.pop_front() {
        topo_order.push(bb);
        for &succ in &successors[bb] {
            if !reachable[succ] {
                continue;
            }
            indegree[succ] -= 1;
            if indegree[succ] == 0 {
                topo_q.push_back(succ);
            }
        }
    }

    let reachable_count = reachable.iter().filter(|&&b| b).count();
    (topo_order, reachable_count)
}

#[cfg(test)]
pub(in crate::codegen_ay) mod integration_ay_runner;
#[cfg(test)]
mod integration_bmc_tests;
#[cfg(test)]
mod integration_chc_kani_hook_tests;
#[cfg(test)]
mod integration_chc_dyn_vtable_tests;
#[cfg(test)]
mod integration_chc_tests;
#[cfg(test)]
mod integration_obligation_free_walk_tests;
#[cfg(test)]
mod integration_verdict_baseline_tests;
#[cfg(test)]
mod tests;
