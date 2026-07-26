// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Closure body translation for quantifier encoding.
//!
//! Translates simple closure MIR bodies into AY expressions by walking the
//! CFG linearly and inlining simple function calls. Handles single-block,
//! 2-block (call delegation), and multi-block (Assert/CheckedBinaryOp) patterns.
//!
//! Extracted from quantifier_encoding.rs — Part of #2408.

use ay_bindings::Expr;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Operand, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::inline_known_calls::{
    inline_known_call_expr, inline_known_call_expr_for_callee_path,
};
use super::super::inline_shared::{PlaceResolver, inline_operand_to_expr, inline_rvalue_to_expr};

// resolve_capture_field moved to inline_shared.rs (Part of #3241)

/// Try to recognize `<[T; N] as Index<usize>>::index(&arr, idx)` and emit
/// `arr.select(idx)` directly. Part of #3454: the Index::index callee is
/// multi-block (bounds check + panic) so `inline_simple_fn_call` rejects it,
/// but the select semantics are trivial when the capture is a AY Array.
fn try_inline_array_index_call(
    func_operand: &Operand,
    call_args: &[Expr],
    caller_locals: &[rustc_public::mir::LocalDecl],
) -> Option<Expr> {
    if call_args.len() != 2 {
        return None;
    }
    let func_ty = func_operand.ty(caller_locals).ok()?;
    let (fn_def, _) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
        _ => return None,
    };
    let name = fn_def.trimmed_name();
    if !name.ends_with("::index") {
        return None;
    }
    let arr = &call_args[0];
    let idx = &call_args[1];
    if !arr.sort().is_array() {
        debug!(
            fn_name = %name,
            "try_inline_array_index_call: first arg is not Array sort, skipping"
        );
        return None;
    }
    debug!(fn_name = %name, "quantifier closure: inlining array Index::index as select");
    Some(arr.clone().select(idx.clone()))
}

fn resolve_closure_body_callee_path(
    ctx: &ChcCtx<'_, '_>,
    func_operand: &Operand,
    caller_locals: &[rustc_public::mir::LocalDecl],
) -> Option<String> {
    let func_ty = func_operand.ty(caller_locals).ok()?;
    let func_ty = ctx.resolve_body_ty(func_ty);
    let (fn_def, fn_args) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, args)) => (def, args),
        _ => return None,
    };
    let instance = Instance::resolve(fn_def, &fn_args).ok();
    let def_id = instance.as_ref().map_or_else(|| fn_def.def_id(), |inst| inst.def.def_id());
    let internal_def_id = rustc_public::rustc_internal::internal(ctx.tcx, def_id);
    Some(ctx.tcx.def_path_str(internal_def_id))
}

/// Inline a simple single-block function call into a AY expression.
///
/// Part of #2943: extracted from duplicated logic in `translate_closure_body_as_expr`
/// (Call terminator arm) and `translate_closure_body_with_call`.
///
/// Resolves `func_operand` to an Instance, verifies it has a single basic block
/// with a Return terminator, translates its statements using the provided call
/// arguments, and returns the function's return value (local 0).
fn inline_simple_fn_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func_operand: &Operand,
    call_args: Vec<Expr>,
    caller_locals: &[rustc_public::mir::LocalDecl],
    bb_idx: usize,
) -> Option<Expr> {
    if let Some(callee_path) = resolve_closure_body_callee_path(ctx, func_operand, caller_locals)
        && let Some(expr) = inline_known_call_expr_for_callee_path(
            ctx,
            func_operand,
            &callee_path,
            &call_args,
            None,
            caller_locals,
        )
    {
        // Part of #4053: declare DT sorts for known-call arg/result accessors.
        for arg in &call_args {
            ctx.declare_datatype_sort_if_needed(arg.sort());
        }
        return Some(expr);
    }

    if let Some(expr) = inline_known_call_expr(ctx, func_operand, &call_args, None, caller_locals) {
        // Part of #4053: declare DT sorts for known-call arg/result accessors.
        for arg in &call_args {
            ctx.declare_datatype_sort_if_needed(arg.sort());
        }
        return Some(expr);
    }

    let func_ty = func_operand.ty(caller_locals).ok()?;
    let (fn_def, fn_substs) = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, substs)) => (def, substs),
        _ => return None, // external enum: TyKind
    };
    let instance = Instance::resolve(fn_def, &fn_substs).ok()?;
    // DELIBERATE raw fetch: quantifier predicate helpers carry no contract
    // machinery (mode dispatch + FC-06 live in check/wrapper closures), and
    // the single-block/Return gate below rejects any transformed instrumented
    // body anyway — a gated-transformed fetch here is behaviorally inert while
    // risking the assert(nondet) fallback on shape mismatch.
    let fn_body = instance.body()?;
    if fn_body.blocks.len() != 1
        || !matches!(fn_body.blocks[0].terminator.kind, TerminatorKind::Return)
    {
        debug!(
            ?bb_idx,
            fn_blocks = fn_body.blocks.len(),
            "called function too complex for quantifier inlining"
        );
        return None;
    }
    let mut fn_local_exprs: HashMap<usize, Expr> = HashMap::new();
    for (i, arg_expr) in call_args.into_iter().enumerate() {
        fn_local_exprs.insert(i + 1, arg_expr);
    }
    let empty_resolver = PlaceResolver::Captures(&[]);
    let fn_locals = fn_body.locals();
    for stmt in &fn_body.blocks[0].statements {
        if let StatementKind::Assign(place, rvalue) = &stmt.kind {
            if !place.projection.is_empty() {
                debug!(
                    ?bb_idx,
                    local = place.local,
                    "inline_simple_fn_call: projected assignment cannot be tracked, bailing (#3268)"
                );
                return None;
            }
            if let Some(expr) = inline_rvalue_to_expr(
                ctx,
                rvalue,
                &fn_local_exprs,
                &empty_resolver,
                &fn_locals,
                Some(place.local),
            ) {
                fn_local_exprs.insert(place.local, expr);
            }
        }
    }
    fn_local_exprs.get(&0).cloned()
}

/// Result of translating a quantifier closure body.
///
/// Part of #2440: carries both the predicate expression and the conjunction of
/// all no-panic guards encountered during closure body walking (Assert terminators
/// from CheckedBinaryOp). For soundness, the quantifier encoder must verify
/// that ALL iterations are panic-free before applying the quantifier logic.
pub(in crate::codegen_ay) struct ClosureBodyResult {
    /// The translated predicate expression (the closure's return value).
    pub(in crate::codegen_ay) pred: Expr,
    /// Conjunction of all Assert-derived no-panic guards. `None` if no Assert
    /// terminators were encountered (the closure body is unconditionally safe).
    pub(in crate::codegen_ay) no_panic_guard: Option<Expr>,
}

/// Translate a simple closure MIR body into a AY Expr.
///
/// The closure is expected to have a single basic block with a Return terminator.
/// The closure parameter (local 2 after the closure struct ref at local 1) is
/// substituted with `qvar`. Captured variables are provided as `captures`.
///
/// Part of #2440: returns a `ClosureBodyResult` containing both the predicate
/// and a no-panic guard for soundness in quantifier encoding.
pub(in crate::codegen_ay) fn translate_closure_body_as_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    qvar: &Expr,
    captures: &[Expr],
    bb_idx: usize,
) -> Option<ClosureBodyResult> {
    // For simple 1-block closures, process directly.
    // For 2-block closures with a Call terminator, delegate to the call handler.
    // For multi-block closures with Assert terminators (from CheckedBinaryOp),
    // walk the success path linearly. (Part of #2323 Cluster 3)
    if body.blocks.len() == 2 {
        // Check if bb0 ends with Call -> bb1 (the original 2-block pattern)
        if matches!(body.blocks[0].terminator.kind, TerminatorKind::Call { target: Some(1), .. }) {
            return translate_closure_body_with_call(ctx, body, qvar, captures, bb_idx);
        }
    }

    // Build local-to-expr mapping.
    // local 0 = return value (populated by assignments)
    // local 1 = closure struct ref (&self / &mut self)
    // local 2 = quantified parameter (mapped to qvar)
    // locals 3+ = temporaries
    let mut local_exprs: HashMap<usize, Expr> = HashMap::new();
    local_exprs.insert(2, qvar.clone());

    let locals = body.locals();

    // Walk the CFG linearly from bb0, following Goto/Assert/Return terminators.
    // Part of #2440: Assert terminators now collect no-panic guards instead of
    // being silently skipped, mirroring the closure inline walker (#3234).
    let mut current_bb = 0usize;
    let mut visited = 0usize;
    let max_visits = body.blocks.len().min(8);
    let mut assert_guards: Vec<Expr> = Vec::new();
    loop {
        if current_bb >= body.blocks.len() || visited >= max_visits {
            debug!(?bb_idx, ?current_bb, "quantifier closure walk exceeded bounds");
            return None;
        }
        visited += 1;
        let block = &body.blocks[current_bb];

        // Process all statements in this block
        let resolver = PlaceResolver::Captures(captures);
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                if !place.projection.is_empty() {
                    debug!(
                        ?bb_idx,
                        local = place.local,
                        "quantifier closure: projected assignment cannot be tracked, bailing (#3268)"
                    );
                    return None;
                }
                if let Some(expr) = inline_rvalue_to_expr(
                    ctx,
                    rvalue,
                    &local_exprs,
                    &resolver,
                    &locals,
                    Some(place.local),
                ) {
                    local_exprs.insert(place.local, expr);
                }
            }
        }

        // Follow terminator
        match &block.terminator.kind {
            TerminatorKind::Return => {
                let pred = local_exprs.get(&0).cloned()?;
                let no_panic_guard = if assert_guards.is_empty() {
                    None
                } else {
                    Some(
                        assert_guards
                            .into_iter()
                            .reduce(|a, b| a.and(b))
                            .expect("invariant: assert_guards is non-empty"),
                    )
                };
                return Some(ClosureBodyResult { pred, no_panic_guard });
            }
            TerminatorKind::Goto { target } => {
                current_bb = *target;
            }
            TerminatorKind::Assert { cond, expected, target, .. } => {
                // Part of #2440: Translate Assert condition and collect as a
                // no-panic guard, mirroring inline_translate.rs (#3234).
                let resolver = PlaceResolver::Captures(captures);
                match inline_operand_to_expr(ctx, cond, &local_exprs, &resolver, &locals) {
                    Some(cond_expr) => {
                        let bool_cond = if cond_expr.sort().is_bool() {
                            cond_expr
                        } else if let Some(w) = cond_expr.sort().bitvec_width() {
                            cond_expr.eq(Expr::bitvec_const(0u64, w)).not()
                        } else {
                            debug!(
                                ?bb_idx,
                                ?current_bb,
                                "quantifier closure: Assert condition has unsupported sort, bailing (#2440)"
                            );
                            return None;
                        };
                        let guard = if *expected { bool_cond } else { bool_cond.not() };
                        assert_guards.push(guard);
                        current_bb = *target;
                    }
                    None => {
                        debug!(
                            ?bb_idx,
                            ?current_bb,
                            "quantifier closure: Assert condition untranslatable, bailing (#2440)"
                        );
                        return None;
                    }
                }
            }
            TerminatorKind::Call { func, args, destination, target: Some(target_bb), .. } => {
                // Inline simple function calls within quantifier closures.
                // Part of #2943: uses shared inline_simple_fn_call helper.
                let resolver = PlaceResolver::Captures(captures);
                let call_args: Vec<Expr> = args
                    .iter()
                    .filter_map(|arg| {
                        inline_operand_to_expr(ctx, arg, &local_exprs, &resolver, &locals)
                    })
                    .collect();
                if call_args.len() != args.len() {
                    debug!(?bb_idx, "quantifier closure: failed to translate call args");
                    return None;
                }
                // Part of #3454: fall back to array-indexing pattern if simple inline fails.
                let result = inline_simple_fn_call(ctx, func, call_args.clone(), &locals, bb_idx)
                    .or_else(|| try_inline_array_index_call(func, &call_args, &locals));
                if let Some(result) = result {
                    local_exprs.insert(destination.local, result);
                }
                current_bb = *target_bb;
            }
            _ => {
                // external enum: TerminatorKind
                debug!(?bb_idx, ?current_bb, "unsupported quantifier closure terminator");
                return None;
            }
        }
    }
}

/// Translate a 2-block closure that delegates to a function call.
///
/// Part of #2294: Handles closures like `|i| comp(j, i)` where the MIR is:
///   bb0: statements; _dest = call(args) -> [return: bb1]
///   bb1: _0 = move _dest; return
fn translate_closure_body_with_call<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    body: &rustc_public::mir::Body,
    qvar: &Expr,
    captures: &[Expr],
    bb_idx: usize,
) -> Option<ClosureBodyResult> {
    let bb0 = &body.blocks[0];
    let bb1 = &body.blocks[1];

    // bb1 must be the return block
    if !matches!(bb1.terminator.kind, TerminatorKind::Return) {
        debug!(?bb_idx, "closure bb1 terminator is not Return");
        return None;
    }

    // bb0 must have a Call terminator targeting bb1
    let (call_func, call_args, call_dest) =
        if let TerminatorKind::Call { func, args, destination, target: Some(1), .. } =
            &bb0.terminator.kind
        {
            (func, args, destination)
        } else {
            // external enum: TerminatorKind
            debug!(?bb_idx, "closure bb0 terminator is not Call -> bb1");
            return None;
        };

    // Build local_exprs for bb0's statements (same as single-block case)
    let mut local_exprs: HashMap<usize, Expr> = HashMap::new();
    local_exprs.insert(2, qvar.clone());

    let locals = body.locals();
    let resolver = PlaceResolver::Captures(captures);
    for stmt in &bb0.statements {
        if let StatementKind::Assign(place, rvalue) = &stmt.kind {
            if !place.projection.is_empty() {
                debug!(
                    ?bb_idx,
                    local = place.local,
                    "quantifier 2-block bb0: projected assignment cannot be tracked, bailing (#3268)"
                );
                return None;
            }
            if let Some(expr) = inline_rvalue_to_expr(
                ctx,
                rvalue,
                &local_exprs,
                &resolver,
                &locals,
                Some(place.local),
            ) {
                local_exprs.insert(place.local, expr);
            }
        }
    }

    // Translate call arguments
    let translated_args: Vec<Expr> = call_args
        .iter()
        .filter_map(|arg| inline_operand_to_expr(ctx, arg, &local_exprs, &resolver, &locals))
        .collect();
    if translated_args.len() != call_args.len() {
        debug!(?bb_idx, "failed to translate all call arguments");
        return None;
    }

    // Inline the called function body.
    // Part of #2943: uses shared inline_simple_fn_call helper.
    // Part of #3454: fall back to array-indexing pattern if simple inline fails.
    let call_result =
        inline_simple_fn_call(ctx, call_func, translated_args.clone(), &locals, bb_idx)
            .or_else(|| try_inline_array_index_call(call_func, &translated_args, &locals))?;

    // Assign result to call destination local
    local_exprs.insert(call_dest.local, call_result);

    // Process bb1's statements (typically just `_0 = move _dest`)
    for stmt in &bb1.statements {
        if let StatementKind::Assign(place, rvalue) = &stmt.kind {
            if !place.projection.is_empty() {
                debug!(
                    ?bb_idx,
                    local = place.local,
                    "quantifier 2-block bb1: projected assignment cannot be tracked, bailing (#3268)"
                );
                return None;
            }
            if let Some(expr) = inline_rvalue_to_expr(
                ctx,
                rvalue,
                &local_exprs,
                &resolver,
                &locals,
                Some(place.local),
            ) {
                local_exprs.insert(place.local, expr);
            }
        }
    }

    let pred = local_exprs.get(&0).cloned()?;
    // 2-block call closures have no Assert terminators, so no panic guard.
    Some(ClosureBodyResult { pred, no_panic_guard: None })
}

// rvalue/operand translation delegated to inline_shared.rs (Part of #3241)
