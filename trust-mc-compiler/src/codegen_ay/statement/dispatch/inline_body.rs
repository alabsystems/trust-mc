// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Small-body inline execution for BMC statement dispatch.
//!
//! The BMC mini-inliner executes small acyclic callee CFGs directly in the
//! caller statement context. It admits reachable DAG-shaped bodies composed of
//! the structured MIR terminators already handled by BMC terminator codegen,
//! while rejecting loops and unsupported terminators up front.

use ay_bindings::Expr;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{BasicBlockIdx, Operand, Place, TerminatorKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use std::collections::VecDeque;
use std::sync::Arc;
use tracing::debug;

use crate::codegen_ay::shared::count_effective_blocks;
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::tuple_usage::TupleUsageAnalysis;

/// BMC-specific effective block limit for the DAG inliner.
///
/// User-defined functions with branches (SwitchInt), drops, and nested calls
/// regularly have 20-40 effective blocks. The shared CHC/BMC limit of 16
/// (`MAX_INLINE_EFFECTIVE_BLOCKS`) is too restrictive for these bodies.
/// This constant applies only to the BMC mini-inliner — CHC has its own
/// `chc_inline_effective_block_limit` with separate heuristics.
///
/// Part of #4211: BMC function inlining gap for user-defined functions.
const MAX_BMC_DAG_INLINE_EFFECTIVE_BLOCKS: usize = 64;

/// Maximum BMC mini-inline recursion depth.
///
/// `try_inline_small_instance_call` descends into callee bodies during BMC
/// statement codegen. Without a depth cap, a self-recursive (or mutually
/// recursive) Rust function with a small, DAG-shaped body drives the host
/// dispatcher into unbounded recursion and crashes rustc with a stack overflow
/// before any solver work is attempted (the wall-clock watchdog masks this as
/// UNKNOWN but the encoder never terminates).
///
/// The CHC inliner uses `MAX_INLINE_DEPTH = 4` for the same reason; we mirror
/// that bound here so non-recursive call chains continue to inline normally and
/// recursive ones bail to the unconstrained / over-approximating fallback.
/// Part of #recursive-sum-stack-overflow.
///
/// Layer B (apply_closure inlining) raises this from 4 to 7: modeling a function
/// contract's `ensures` closure adds ~2-3 synthetic frames on top of the user
/// call chain (closure body -> `type_invariant` -> `ArrayVec`/`Vec::len`), so the
/// old depth-4 cap bailed mid-`type_invariant` and re-introduced an unsupported
/// fallback. The cycle guard below still prevents runaway recursion.
///
/// Layer C (nested-collection element-wise replay) raises this from 7 to 12: a
/// `.filter(..).map(..).sum()` over a `Vec<T>` whose element `T` itself owns a
/// collection (e.g. the ay-pb `eval_terms` fold over `Vec<PbTerm>`, each `PbTerm`
/// a `Vec<PbLit>`) replays the outer chain element-wise AND, per element, inlines
/// the inner predicate whose body iterates the inner collection — stacking
/// `eval_terms -> filter-closure -> eval_term -> all-closure -> eval_lit ->
/// and_then-closure -> try_from`, ~5 frames deeper than the single-level `.all()`
/// the depth-7 cap was tuned for. The same-instance cycle guard below still
/// prevents runaway recursion, so a non-recursive nested-iterator chain inlines
/// to completion instead of bailing mid-`eval_lit` into a Call-terminator havoc.
const MAX_BMC_MINI_INLINE_DEPTH: usize = 12;

struct InlineParentState {
    path_condition: Option<Expr>,
    env: std::collections::BTreeMap<std::sync::Arc<str>, Expr>,
    ref_pointees: std::collections::BTreeMap<std::sync::Arc<str>, std::sync::Arc<str>>,
    flattened_tuples: std::collections::HashMap<std::sync::Arc<str>, Vec<Expr>>,
    heap_pointees: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    ptr_source_map: std::collections::HashMap<std::sync::Arc<str>, std::sync::Arc<str>>,
    addr_symbols: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    addr_metadata_symbols: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    hashmap_len_symbols: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    entry_map_bases: std::collections::HashMap<std::sync::Arc<str>, std::sync::Arc<str>>,
    entry_keys: std::collections::HashMap<std::sync::Arc<str>, Expr>,
    ssa_concrete_values: std::collections::HashMap<String, Expr>,
    stub_indexed_refs: std::collections::HashMap<std::sync::Arc<str>, (std::sync::Arc<str>, Expr)>,
    /// Pre-resolved fn_ptr callees from the caller's body scan.
    /// Enables nested fn_ptr resolution when the fn_ptr is received as a parameter.
    parent_fn_ptr_callees: Vec<(Instance, bool)>,
}

pub(in crate::codegen_ay::statement) struct InlineArgValue {
    pub(in crate::codegen_ay::statement) expr: Expr,
    pub(in crate::codegen_ay::statement) pointee_base: Option<Arc<str>>,
    /// Piecewise storage entries of a FLATTENED caller argument (#2076): the
    /// discriminant `.0`, the payload `.1`, and enum-variant / tuple field keys
    /// (`_variant_V_field_F`, `_field_F`). Recorded as `(suffix, value)` pairs so
    /// `seed_inline_params` can re-key them onto the callee parameter base ON
    /// ENTRY — the mirror of the return-side `apply_flattened_value_entries`.
    ///
    /// Without this, an inlined callee that reads `discriminant(param)` /
    /// `(param as variant#V).F` on a flattened `Option`/enum value parameter (e.g.
    /// the `self` of an inlined `Option::and_then` in the ay-pb `eval_lit` chain
    /// `.checked_sub(1).and_then(..).and_then(|i| a.get(i)).copied()`) misses the
    /// discriminant and falls back to a SYMBOLIC "both variants explored"
    /// over-approximation — admitting a spurious counterexample.
    /// Part of #multi-hop-flattened-option.
    pub(in crate::codegen_ay::statement) flattened_entries: Vec<(String, Expr)>,
    /// `ref_pointees` links carried by a FLATTENED reference-carrying argument,
    /// as `(suffix, pointee_base)` pairs relative to the caller arg base ("" is
    /// the base itself). Re-keyed onto the callee parameter base on ENTRY so a
    /// `*param` / `.copied()` deref inside the inlined body resolves the same
    /// pointee the caller tracked (e.g. a flattened `Option<&T>` value parameter).
    /// Part of #multi-hop-flattened-option.
    pub(in crate::codegen_ay::statement) nested_ref_pointees: Vec<(String, Arc<str>)>,
}

struct InlineExecutionResult {
    result: Expr,
    return_base: Arc<str>,
    env: std::collections::BTreeMap<Arc<str>, Expr>,
    ref_pointees: std::collections::BTreeMap<Arc<str>, Arc<str>>,
    /// The callee frame's SSA-var -> folded-constructor cache. Carried back so
    /// the parent can resolve an inline-returned iterator/adaptor value (e.g.
    /// `Copied::new`'s `Ctor(Copied[fld_it=..])`, G2 Wall A) instead of seeing
    /// a bare SSA `Var` that `resolve_iter_concrete_range` must fail-close on.
    /// Entries are equality-asserted SSA definitions — aliases of REAL values,
    /// safe to merge into the parent's cache (same keyspace, callee-frame
    /// names are unique per `set_current_fn`).
    ssa_concrete_values: std::collections::HashMap<String, Expr>,
}

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Inline a small callee body into the current BMC statement context.
    ///
    /// `params` are normalized to the callee signature:
    /// - value params use the exact callee value expression
    /// - `&T` params use the pointee value that should back the callee reference local
    pub(in crate::codegen_ay::statement) fn try_inline_small_instance_call(
        &mut self,
        instance: Instance,
        params: &[InlineArgValue],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<BasicBlockIdx> {
        let target = target?;
        let body = self.ctx.body_or_instance_body(instance)?;
        let effective_blocks = count_effective_blocks(&body);
        let limit = MAX_BMC_DAG_INLINE_EFFECTIVE_BLOCKS;
        if effective_blocks > limit {
            debug!(
                callee = instance.name(),
                effective_blocks, limit, "mini-inline: callee exceeds effective block limit"
            );
            return None;
        }
        if !body_is_dag_inline_candidate(&body) {
            debug!(callee = instance.name(), "mini-inline: callee is not a DAG inline candidate");
            return None;
        }

        let arg_locals = body.arg_locals();
        if arg_locals.len() != params.len() {
            debug!(
                callee = instance.name(),
                expected = arg_locals.len(),
                got = params.len(),
                "mini-inline: parameter arity mismatch"
            );
            return None;
        }

        // BMC mini-inline recursion guard.
        //
        // The dispatcher calls `try_inline_small_instance_call` while translating
        // a callee body whose own `Call` terminators flow back through the same
        // dispatcher. For a self-recursive function such as `recursive_sum`, the
        // callee body contains a `Call recursive_sum(n - 1)` terminator, which
        // re-enters this helper with the same `Instance` and grows the host
        // stack until rustc aborts (`thread 'rustc' has overflowed its stack`).
        //
        // Bail before pushing if the instance is already on the inline stack
        // (cycle) or the stack depth has reached the cap. Returning `None`
        // makes BMC dispatch fall through to the non-inlining call path, which
        // leaves the destination unconstrained and the verdict over-approximated
        // — the same behaviour CHC uses when its `MAX_INLINE_DEPTH = 4` bound is
        // reached. Part of #recursive-sum-stack-overflow.
        let instance_key = instance.name();
        if self.ctx.bmc_mini_inline_stack.iter().any(|n| n == &instance_key)
            || self.ctx.bmc_mini_inline_stack.len() >= MAX_BMC_MINI_INLINE_DEPTH
        {
            debug!(
                callee = %instance_key,
                depth = self.ctx.bmc_mini_inline_stack.len(),
                "mini-inline: recursion or depth cap reached, declining to inline"
            );
            return None;
        }

        let inherited_state = self.capture_inline_parent_state();
        let parent_fn = self.ctx.current_fn().cloned();
        self.ctx.set_current_fn(instance);
        self.ctx.bmc_mini_inline_stack.push(instance_key);
        let result = {
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut inline_codegen = StatementCodegen::new(self.ctx, &body, tuple_usage);
            inline_codegen.apply_inline_parent_state(inherited_state);
            inline_codegen.execute_dag_inline_body(params)
        };
        self.ctx.bmc_mini_inline_stack.pop();
        if let Some(parent_fn) = parent_fn {
            self.ctx.set_current_fn(parent_fn.instance);
        }

        let result = result?;
        self.propagate_inline_return_ref_pointees(
            destination,
            &result.return_base,
            &result.env,
            &result.ref_pointees,
        );
        // Merge ONLY the callee's SSA->folded-constructor cache (equality-
        // asserted aliases of real values); never the raw inline env wholesale.
        // Without this, an inline-returned adapter value (e.g. `.copied()`'s
        // `Ctor(Copied[fld_it=..])`) degrades to a bare SSA Var in the parent
        // and the iterator range reader fail-closes (G2 Wall A).
        self.ssa_concrete_values.extend(result.ssa_concrete_values);
        self.assign_value_to_place(destination, result.result);
        // Part of #4112 follow-up: flattened Option-like returns (#2076) store the
        // discriminant under `{ret}.0` and the payload under `{ret}_variant_V_field_F`.
        // Re-key those piecewise entries onto the call destination so caller-side
        // `discriminant(dest)` and `(dest as variant#V).F` reads stay linked to the
        // value the callee actually returned (previously they degraded to symbolic /
        // unconstrained EncodingGap fallbacks).
        let flattened_entries =
            Self::collect_flattened_value_entries(&result.env, result.return_base.as_ref());
        if !flattened_entries.is_empty() {
            let dest_base = self.ssa_base_name(destination);
            self.apply_flattened_value_entries(&dest_base, flattened_entries);
        }
        Some(target)
    }

    /// Inline a small callee/closure body and RETURN its result value
    /// expression, WITHOUT binding it to a destination `Place`.
    ///
    /// This is the value-returning sibling of `try_inline_small_instance_call`,
    /// used by the sound iterator-adapter unrolling (`IterAll`/`IterAny`) to
    /// invoke a per-element predicate closure and collect its boolean result so
    /// the caller can fold the per-element results into a single `all`/`any`
    /// value.
    ///
    /// SOUNDNESS: returns `None` (the caller MUST fail closed — record an
    /// `unsupported_with_fallback` and leave the result unconstrained, never
    /// silently pass) whenever the body is not a small reachable DAG-inline
    /// candidate, the parameter arity mismatches, or the recursion / depth caps
    /// are reached. Mirrors every admission check of
    /// `try_inline_small_instance_call`; it only drops the destination binding
    /// and the flattened-entry rekeying (the predicate result is a scalar bool).
    pub(in crate::codegen_ay::statement) fn inline_instance_value(
        &mut self,
        instance: Instance,
        params: &[InlineArgValue],
    ) -> Option<Expr> {
        let body = self.ctx.body_or_instance_body(instance)?;
        let effective_blocks = count_effective_blocks(&body);
        if effective_blocks > MAX_BMC_DAG_INLINE_EFFECTIVE_BLOCKS {
            return None;
        }
        if !body_is_dag_inline_candidate(&body) {
            return None;
        }
        let arg_locals = body.arg_locals();
        if arg_locals.len() != params.len() {
            return None;
        }
        let instance_key = instance.name();
        if self.ctx.bmc_mini_inline_stack.iter().any(|n| n == &instance_key)
            || self.ctx.bmc_mini_inline_stack.len() >= MAX_BMC_MINI_INLINE_DEPTH
        {
            return None;
        }

        let inherited_state = self.capture_inline_parent_state();
        let parent_fn = self.ctx.current_fn().cloned();
        self.ctx.set_current_fn(instance);
        self.ctx.bmc_mini_inline_stack.push(instance_key);
        let result = {
            let tuple_usage = TupleUsageAnalysis::run(&body);
            let mut inline_codegen = StatementCodegen::new(self.ctx, &body, tuple_usage);
            inline_codegen.apply_inline_parent_state(inherited_state);
            inline_codegen.execute_dag_inline_body(params)
        };
        self.ctx.bmc_mini_inline_stack.pop();
        // Restore the parent frame VERBATIM (name included) rather than
        // re-deriving it through the active `inline_frame_salt`: an outermost
        // pop returns to a caller frame that must keep its own (un-salted, or
        // differently-salted) namespace.
        self.ctx.restore_current_fn(parent_fn);
        Some(result?.result)
    }

    fn execute_dag_inline_body(
        &mut self,
        params: &[InlineArgValue],
    ) -> Option<InlineExecutionResult> {
        let inherited_path_condition = self.current_path_condition.clone();
        let inherited_env = self.current_env.clone();
        self.initialize_block_entry_env(0);
        self.current_path_condition = inherited_path_condition;
        self.current_env.extend(inherited_env);
        self.seed_inline_params(params)?;

        let topo_order = self.compute_inline_topo_order()?;
        debug!(
            block_count = self.body.blocks.len(),
            topo_len = topo_order.len(),
            "mini-inline: executing DAG body"
        );

        for bb_idx in topo_order {
            if bb_idx != 0 {
                self.initialize_block_entry_env(bb_idx);
            }

            {
                let block = &self.body.blocks[bb_idx];
                debug!(
                    bb = bb_idx,
                    statements = block.statements.len(),
                    "mini-inline: executing block"
                );

                for stmt in &block.statements {
                    self.codegen_statement(stmt);
                }
            }

            let terminator = self.body.blocks[bb_idx].terminator.clone();
            let successors = self.codegen_terminator_with_successors(&terminator);
            for (target_bb, edge_cond) in successors {
                self.record_outgoing_edge(target_bb, edge_cond);
            }
        }

        self.inline_return_expr()
    }

    fn capture_inline_parent_state(&self) -> InlineParentState {
        // Resolve fn_ptr callees from the caller's body so the nested codegen
        // can find them when fn pointers are passed as parameters.
        let mut parent_fn_ptr_callees = self.parent_fn_ptr_callees.clone();
        parent_fn_ptr_callees.extend(self.resolve_all_fn_ptr_callees());

        InlineParentState {
            path_condition: self.current_path_condition.clone(),
            env: self.current_env.clone(),
            ref_pointees: self.ref_pointees.clone(),
            flattened_tuples: self.flattened_tuples.clone(),
            heap_pointees: self.heap_pointees.clone(),
            ptr_source_map: self.ptr_source_map.clone(),
            addr_symbols: self.addr_symbols.clone(),
            addr_metadata_symbols: self.addr_metadata_symbols.clone(),
            hashmap_len_symbols: self.hashmap_len_symbols.clone(),
            entry_map_bases: self.entry_map_bases.clone(),
            entry_keys: self.entry_keys.clone(),
            ssa_concrete_values: self.ssa_concrete_values.clone(),
            stub_indexed_refs: self.stub_indexed_refs.clone(),
            parent_fn_ptr_callees,
        }
    }

    fn apply_inline_parent_state(&mut self, state: InlineParentState) {
        self.current_path_condition = state.path_condition;
        self.current_env.extend(state.env);
        self.ref_pointees.extend(state.ref_pointees);
        self.flattened_tuples.extend(state.flattened_tuples);
        self.heap_pointees.extend(state.heap_pointees);
        self.ptr_source_map.extend(state.ptr_source_map);
        self.addr_symbols.extend(state.addr_symbols);
        self.addr_metadata_symbols.extend(state.addr_metadata_symbols);
        self.hashmap_len_symbols.extend(state.hashmap_len_symbols);
        self.entry_map_bases.extend(state.entry_map_bases);
        self.entry_keys.extend(state.entry_keys);
        self.ssa_concrete_values.extend(state.ssa_concrete_values);
        self.stub_indexed_refs.extend(state.stub_indexed_refs);
        self.parent_fn_ptr_callees = state.parent_fn_ptr_callees;
    }

    fn seed_inline_params(&mut self, params: &[InlineArgValue]) -> Option<()> {
        for (index, local_decl) in self.body.arg_locals().iter().enumerate() {
            let place = Place { local: index + 1, projection: vec![] };
            match local_decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)) => {
                    self.assign_value_to_place(&place, params[index].expr.clone());
                    if let Some(pointee_base) = params[index].pointee_base.clone() {
                        let dest_base: Arc<str> = self.ssa_base_name(&place).into();
                        self.ref_pointees.insert(dest_base, pointee_base);
                    } else if let TyKind::RigidTy(RigidTy::Ref(
                        _,
                        pointee_ty,
                        rustc_public::mir::Mutability::Not,
                    )) = local_decl.ty.kind()
                        && let Some(pointee_sort) = Self::infer_sort_from_ty(pointee_ty)
                        && (pointee_sort.is_datatype() || pointee_sort.is_array())
                        && *params[index].expr.sort() == pointee_sort
                    {
                        // The caller passed the pointee VALUE itself (value
                        // semantics — e.g. the Slice datatype a Vec deref
                        // produces) with NO ref_pointees link. Bind the callee
                        // param to a pointee entry holding that REAL value, so
                        // an inherited stale link / fresh arg_pointee cannot
                        // shadow it and callee derefs (`.iter()` receivers)
                        // resolve the actual data. Mirrors
                        // `try_ref_pointee_from_env_value`: SHARED refs and
                        // exact datatype/array sort match only — rebinding a
                        // `&mut` pointee would drop callee writebacks (a
                        // false-verify surface), and thin-pointer bitvectors
                        // stay untouched.
                        let dest_base: Arc<str> = self.ssa_base_name(&place).into();
                        let pointee_name = self.ctx.fresh_name("inline_arg_pointee");
                        let pointee: Arc<str> = Arc::from(pointee_name.as_str());
                        self.env_update(Arc::clone(&pointee), params[index].expr.clone());
                        self.ref_pointees.insert(dest_base, pointee);
                    }
                }
                _ => self.assign_value_to_place(&place, params[index].expr.clone()),
            }
            self.seed_inline_param_flattened(&place, &params[index]);
        }
        Some(())
    }

    /// Re-key a caller argument's FLATTENED piecewise entries + nested
    /// `ref_pointees` onto the callee parameter base ON ENTRY.
    ///
    /// The entry-side mirror of the return-side `apply_flattened_value_entries` /
    /// `propagate_inline_return_ref_pointees`. The parent env and `ref_pointees`
    /// were already inherited (`apply_inline_parent_state`) under the CALLER's key
    /// names, so this only publishes callee-parameter-keyed ALIASES to the same
    /// values — faithful, never a fresh symbolic. Without it, an inlined body that
    /// reads `discriminant(param)` on a flattened `Option`/enum value parameter
    /// misses the `.0` discriminant and over-approximates it as a symbolic "both
    /// variants explored" discriminant (spurious CEX). Part of
    /// #multi-hop-flattened-option.
    fn seed_inline_param_flattened(&mut self, place: &Place, arg: &InlineArgValue) {
        if arg.flattened_entries.is_empty() && arg.nested_ref_pointees.is_empty() {
            return;
        }
        let dest_base = self.ssa_base_name(place);
        if !arg.flattened_entries.is_empty() {
            self.apply_flattened_value_entries(&dest_base, arg.flattened_entries.clone());
        }
        for (suffix, pointee_base) in &arg.nested_ref_pointees {
            let mut dest_key = String::with_capacity(dest_base.len() + suffix.len());
            dest_key.push_str(&dest_base);
            dest_key.push_str(suffix);
            self.ref_pointees.insert(Arc::from(dest_key), Arc::clone(pointee_base));
        }
    }

    /// Translate a caller operand into a value suitable for seeding a callee parameter.
    ///
    /// For reference/pointer parameters, preserve the original reference value
    /// plus its pointee mapping so inline bodies keep aliasing intact.
    /// For value parameters, translate the operand directly.
    /// Shared by closure_call, fn_inline, and fn_ptr dispatch paths.
    pub(in crate::codegen_ay::statement) fn translate_inline_arg_value(
        &mut self,
        operand: &Operand,
        callee_ty: Ty,
    ) -> Option<InlineArgValue> {
        // Capture the FLATTENED piecewise entries + nested `ref_pointees` of the
        // caller argument so `seed_inline_params` can re-key them onto the callee
        // parameter base ON ENTRY (mirror of the return-side re-key). Needed for a
        // flattened `Option`/enum value parameter whose inlined body reads
        // `discriminant(param)` / a Some-payload deref (#multi-hop-flattened-option).
        let (flattened_entries, nested_ref_pointees) = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let arg_base = self.ssa_base_name(place);
                let entries =
                    Self::collect_flattened_value_entries(&self.current_env, arg_base.as_str());
                let refs = self.collect_nested_arg_ref_pointees(arg_base.as_str());
                (entries, refs)
            }
            Operand::Constant(_) => (Vec::new(), Vec::new()),
        };
        match callee_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(..)) | TyKind::RigidTy(RigidTy::RawPtr(..)) => {
                let expr = self.codegen_operand(operand)?;
                let pointee_base = match operand {
                    Operand::Copy(place) | Operand::Move(place) => {
                        let ref_base = self.ssa_base_name(place);
                        self.ref_pointees.get(ref_base.as_str()).cloned().or_else(|| {
                            self.ensure_ref_pointee_for_place(place);
                            self.ref_pointees.get(ref_base.as_str()).cloned()
                        })
                    }
                    Operand::Constant(_) => None,
                };
                Some(InlineArgValue { expr, pointee_base, flattened_entries, nested_ref_pointees })
            }
            _ => Some(InlineArgValue {
                expr: self.codegen_operand(operand)?,
                pointee_base: None,
                flattened_entries,
                nested_ref_pointees,
            }),
        }
    }

    /// Collect the `ref_pointees` links attached to a caller argument's flattened
    /// storage: the base itself (suffix `""`) plus the Some/tuple field keys
    /// (`_variant_V_field_F`, `_field_F`, `.0`, `.1`). Returned as
    /// `(suffix, pointee_base)` pairs so `seed_inline_params` can re-key them onto
    /// the callee parameter base on ENTRY (faithful aliasing — the pointee bases
    /// and their env values are already inherited via `apply_inline_parent_state`).
    /// Part of #multi-hop-flattened-option.
    pub(in crate::codegen_ay::statement) fn collect_nested_arg_ref_pointees(
        &self,
        arg_base: &str,
    ) -> Vec<(String, Arc<str>)> {
        let mut out = Vec::new();
        if let Some(pointee) = self.ref_pointees.get(arg_base) {
            out.push((String::new(), Arc::clone(pointee)));
        }
        for dotted in [".0", ".1"] {
            let mut key = String::with_capacity(arg_base.len() + dotted.len());
            key.push_str(arg_base);
            key.push_str(dotted);
            if let Some(pointee) = self.ref_pointees.get(key.as_str()) {
                out.push((dotted.to_string(), Arc::clone(pointee)));
            }
        }
        for pfx in ["_variant_", "_field_"] {
            let mut prefix = String::with_capacity(arg_base.len() + pfx.len());
            prefix.push_str(arg_base);
            prefix.push_str(pfx);
            let range_start: Arc<str> = Arc::from(prefix.as_str());
            for (key, pointee) in self
                .ref_pointees
                .range(range_start..)
                .take_while(|(k, _)| k.starts_with(prefix.as_str()))
            {
                out.push((key[arg_base.len()..].to_string(), Arc::clone(pointee)));
            }
        }
        out
    }

    fn inline_return_expr(&mut self) -> Option<InlineExecutionResult> {
        let ret_place = Place { local: 0, projection: vec![] };
        let ret_base = self.ssa_base_name(&ret_place);
        if let Some(expr) = self.env_lookup(&ret_base) {
            return Some(InlineExecutionResult {
                result: expr.clone(),
                return_base: Arc::from(ret_base.as_str()),
                env: self.current_env.clone(),
                ref_pointees: self.ref_pointees.clone(),
                ssa_concrete_values: self.ssa_concrete_values.clone(),
            });
        }

        let ret_ty = self.body.locals().first()?.ty;
        if matches!(ret_ty.kind(), TyKind::RigidTy(RigidTy::Tuple(fields)) if fields.is_empty()) {
            return Some(InlineExecutionResult {
                result: Expr::bitvec_const(0u64, POINTER_WIDTH),
                return_base: Arc::from(ret_base.as_str()),
                env: self.current_env.clone(),
                ref_pointees: self.ref_pointees.clone(),
                ssa_concrete_values: self.ssa_concrete_values.clone(),
            });
        }
        None
    }

    fn propagate_inline_return_ref_pointees(
        &mut self,
        destination: &Place,
        return_base: &Arc<str>,
        inline_env: &std::collections::BTreeMap<Arc<str>, Expr>,
        inline_ref_pointees: &std::collections::BTreeMap<Arc<str>, Arc<str>>,
    ) {
        let dest_base: Arc<str> = self.ssa_base_name(destination).into();

        if let Some(pointee_base) = inline_ref_pointees.get(return_base.as_ref()).cloned() {
            if !self.current_env.contains_key(&pointee_base)
                && let Some(expr) = inline_env.get(&pointee_base).cloned()
            {
                self.current_env.insert(Arc::clone(&pointee_base), expr);
            }
            self.ref_pointees.insert(Arc::clone(&dest_base), pointee_base);
        }

        let mut prefix = String::with_capacity(return_base.len() + 1);
        prefix.push_str(return_base.as_ref());
        prefix.push('_');
        let range_start: Arc<str> = Arc::from(prefix.as_str());
        let nested_refs: Vec<_> = inline_ref_pointees
            .range(range_start..)
            .take_while(|(key, _)| key.starts_with(prefix.as_str()))
            .map(|(key, pointee_base)| (Arc::clone(key), Arc::clone(pointee_base)))
            .collect();

        for (key, pointee_base) in nested_refs {
            let suffix = &key[return_base.len()..];
            let mut dest_key = String::with_capacity(dest_base.len() + suffix.len());
            dest_key.push_str(dest_base.as_ref());
            dest_key.push_str(suffix);

            if !self.current_env.contains_key(&pointee_base)
                && let Some(expr) = inline_env.get(&pointee_base).cloned()
            {
                self.current_env.insert(Arc::clone(&pointee_base), expr);
            }
            self.ref_pointees.insert(Arc::from(dest_key), pointee_base);
        }
    }

    fn compute_inline_topo_order(&self) -> Option<Vec<usize>> {
        let successors = inline_candidate_successors(self.body)?;
        let block_count = successors.len();

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

        let reachable_count = reachable.iter().filter(|&&bb| bb).count();
        if topo_order.len() != reachable_count {
            debug!(
                topo_len = topo_order.len(),
                reachable_count, "mini-inline: reachable CFG is not acyclic"
            );
            return None;
        }

        Some(topo_order)
    }
}

fn body_is_dag_inline_candidate(body: &rustc_public::mir::Body) -> bool {
    let Some(successors) = inline_candidate_successors(body) else {
        return false;
    };

    fn dfs(bb: usize, successors: &[Vec<usize>], state: &mut [u8]) -> bool {
        state[bb] = 1;
        for &succ in &successors[bb] {
            match state[succ] {
                0 => {
                    if !dfs(succ, successors, state) {
                        return false;
                    }
                }
                1 => return false,
                2 => {}
                _ => unreachable!("invalid DFS mark"),
            }
        }
        state[bb] = 2;
        true
    }

    let mut state = vec![0u8; successors.len()];
    let is_acyclic = dfs(0, &successors, &mut state);
    if !is_acyclic {
        debug!("mini-inline: cycle detected in callee CFG");
    }
    is_acyclic
}

fn inline_candidate_successors(body: &rustc_public::mir::Body) -> Option<Vec<Vec<usize>>> {
    if body.blocks.is_empty() {
        debug!("mini-inline: empty callee body");
        return None;
    }

    let block_count = body.blocks.len();
    let mut successors = Vec::with_capacity(block_count);
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        let mut succs = match &block.terminator.kind {
            TerminatorKind::Return | TerminatorKind::Unreachable => vec![],
            TerminatorKind::Goto { target }
            | TerminatorKind::Assert { target, .. }
            | TerminatorKind::Drop { target, .. } => vec![*target],
            TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
            TerminatorKind::SwitchInt { targets, .. } => {
                let mut succs: Vec<usize> =
                    targets.branches().map(|(_case_val, target)| target).collect();
                succs.push(targets.otherwise());
                succs
            }
            _ => {
                debug!(
                    bb = bb_idx,
                    kind = ?block.terminator.kind,
                    "mini-inline: unsupported terminator kind in callee"
                );
                return None;
            }
        };
        succs.sort_unstable();
        succs.dedup();
        if succs.iter().any(|&succ| succ >= block_count) {
            debug!(bb = bb_idx, ?succs, block_count, "mini-inline: invalid successor index");
            return None;
        }
        successors.push(succs);
    }

    Some(successors)
}
