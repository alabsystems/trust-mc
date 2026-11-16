// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec iterator and core operation call handling.
//!
//! Extracted from include!() to proper module via extension trait pattern.
//! Part of #2306: include!() to proper module migration.
//!
//! Operation helpers are in:
//! - `codegen_call_vec_iter.rs`: vec iterator result routing (Part of #4135)
//! - `codegen_call_vec_array_iter.rs`: array-inner iterator handlers (Part of #4135)
//! - `codegen_call_vec_ops.rs`: lifecycle and capacity ops (Part of #2884)
//! - `codegen_call_vec_ops_len.rs`: len/query ops — clear, clone, len (Part of #2304)
//! - `codegen_call_vec_ops_views.rs`: view ops — as_ptr, as_mut_ptr
//! - `codegen_call_vec_element.rs`: push and pop ops (Part of #2884)

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::CtorFieldExt;

use super::ChcCtx;
use super::chc_call_context::{ChcCallContext, DispatchCallContext};
use super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::codegen_call_vec_element::VecPopContext;
use super::codegen_call_vec_ops::VecOpNewContext;
use super::codegen_rules::CodegenRules;
use tracing::{debug, warn};

/// All four Vec Datatype fields extracted in a single pass. Part of #2267.
/// Eliminates repeated `vec_in.field_select()` patterns across
/// VecPush, VecReserve, VecShrinkToFit, VecPop.
pub(in crate::codegen_ay::chc) struct ChcVecFields {
    pub(in crate::codegen_ay::chc) vec_sort: Sort,
    pub(in crate::codegen_ay::chc) ptr: Expr,
    pub(in crate::codegen_ay::chc) len: Expr,
    pub(in crate::codegen_ay::chc) cap: Expr,
    pub(in crate::codegen_ay::chc) data: Expr,
}

impl ChcVecFields {
    /// Extract ptr/len/cap/data without materializing datatype name as `String`.
    ///
    /// Callers that only need field expressions should use this to avoid
    /// the extra allocation from `datatype_name().to_owned()`.
    pub(in crate::codegen_ay::chc) fn extract_without_name(
        vec_in: Expr,
    ) -> Option<(Expr, Expr, Expr, Expr)> {
        let sort_ref = vec_in.sort().clone();
        let dt = sort_ref.datatype_sort()?;
        let ctor = dt.constructors.first()?;
        let ptr_field = ctor.field(vec_layout::FLD_PTR)?;
        let len_field = ctor.field(vec_layout::FLD_LEN)?;
        let cap_field = ctor.field(vec_layout::FLD_CAP)?;
        let data_field = ctor.field(vec_layout::FLD_DATA)?;
        let ptr =
            vec_in.clone().field_select(&dt.name, vec_layout::FLD_PTR, ptr_field.sort.clone());
        let len =
            vec_in.clone().field_select(&dt.name, vec_layout::FLD_LEN, len_field.sort.clone());
        let cap =
            vec_in.clone().field_select(&dt.name, vec_layout::FLD_CAP, cap_field.sort.clone());
        let data = vec_in.field_select(&dt.name, vec_layout::FLD_DATA, data_field.sort.clone());
        Some((ptr, len, cap, data))
    }

    /// Extract all four Vec fields from a CHC Vec expression.
    /// Uses `get_dt_field_sort` for sort resolution and falls back to defaults.
    pub(in crate::codegen_ay::chc) fn extract(vec_in: Expr) -> Option<Self> {
        // Keep the Vec sort so constructor callsites can borrow dt_name as `&str`
        // without allocating an intermediate owned `String`.
        let vec_sort = vec_in.sort().clone();
        let _ = vec_sort.datatype_name()?;
        let (ptr, len, cap, data) = Self::extract_without_name(vec_in)?;
        Some(Self { vec_sort, ptr, len, cap, data })
    }
}

/// Extension trait for Vec iterator and core operation call handling on `ChcCtx`.
pub(in crate::codegen_ay::chc) trait CallVec {
    fn codegen_call_vec_iter(&mut self, stub: StubKind, dcx: &DispatchCallContext<'_>);

    /// Handle array inner iterator next() calls (PolymorphicIter::next, IndexRange::next).
    ///
    /// Part of #3984: These are called on inner fields of ArrayIntoIter locals where
    /// the receiver is a BV64 heap pointer. Routes through the parent IntoIter local
    /// which IS in projection_locals and can be reconstructed from flattened state vars.
    fn codegen_call_array_inner_iter_next(&mut self, dcx: &DispatchCallContext<'_>);

    /// Handle IndexRange::next() calls — returns Option<usize> (index into array).
    ///
    /// Part of #3984: IndexRange::next is simpler than PolymorphicIter::next: it
    /// just returns the current start index wrapped in Option, and increments start.
    /// The MIR then feeds this through Option::map to extract the actual element.
    fn codegen_call_array_index_range_next(&mut self, dcx: &DispatchCallContext<'_>);

    fn codegen_call_vec_core(&mut self, cx: &ChcCallContext<'_>);
    fn codegen_call_vec_core_with_callee(
        &mut self,
        cx: &ChcCallContext<'_>,
        callee: Option<&Operand>,
    );

    /// Try to handle an array-inner OptionMap call precisely.
    ///
    /// Part of #3984: When Option::map is called after IndexRange::next in the
    /// array consume path, the closure lifts Option<usize> to Option<T> by
    /// reading data[idx]. This handler intercepts OptionMap before the generic
    /// combinator over-approximation, producing Some(data[idx]) / None.
    /// Returns true if it handled the call, false to fall through.
    fn try_codegen_array_inner_option_map(&mut self, cx: &ChcCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallVec for ChcCtx<'tcx, 'body> {
    /// Handle Vec iterator stub calls (Part of #1811).
    fn codegen_call_vec_iter(&mut self, stub: StubKind, dcx: &DispatchCallContext<'_>) {
        // Keep the dedicated IndexRange handler referenced on current HEAD until the
        // matching collection-dispatch packet lands from the shared worktree.
        let _ = <Self as CallVec>::codegen_call_array_index_range_next
            as fn(&mut Self, &DispatchCallContext<'_>);
        super::codegen_call_vec_iter::codegen_call_vec_iter_impl(self, stub, dcx);
    }

    fn codegen_call_array_inner_iter_next(&mut self, dcx: &DispatchCallContext<'_>) {
        super::codegen_call_vec_array_iter::codegen_call_array_inner_iter_next_impl(self, dcx);
    }

    fn codegen_call_array_index_range_next(&mut self, dcx: &DispatchCallContext<'_>) {
        super::codegen_call_vec_array_iter::codegen_call_array_index_range_next_impl(self, dcx);
    }

    fn try_codegen_array_inner_option_map(&mut self, cx: &ChcCallContext<'_>) -> bool {
        super::codegen_call_vec_array_iter::try_codegen_array_inner_option_map_impl(self, cx)
    }

    /// Handle Vec core operation stubs (Part of #2196, #2877).
    ///
    /// Dispatches to per-category helpers in codegen_call_vec_ops.rs and
    /// codegen_call_vec_element.rs (Part of #2884).
    fn codegen_call_vec_core(&mut self, cx: &ChcCallContext<'_>) {
        self.codegen_call_vec_core_with_callee(cx, None);
    }

    fn codegen_call_vec_core_with_callee(
        &mut self,
        cx: &ChcCallContext<'_>,
        callee: Option<&Operand>,
    ) {
        let stub = cx.stub;
        let args = cx.args;
        let destination = cx.destination;
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;
        let dest_local: usize = destination.local;
        let Some(dest_vec_idx) = self.try_state_idx_for_local(dest_local) else {
            debug!(dest_local, "CHC: vec_core dest not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_vec_core_dest");
            emit_sound_fallback_goto(
                self,
                from_app,
                target,
                modified_locals,
                &[dest_local],
                stmt_constraints,
            );
            return;
        };
        debug!("vec_core_stub stub={:?} dest={}", stub, dest_local);
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();
        // The "capacity overflow" panic of `Vec::extend` from a range, stated
        // as a check before the length update that assumes it.
        let mut extend_capacity_check: Option<Expr> = None;
        // `Vec::split_off`'s panic when `at > len`, stated the same way.
        let mut split_off_bounds_check: Option<Expr> = None;

        // Resolve collection local for length tracking (args[0] is &self for most methods)
        let collection_local = self.resolve_collection_local(args);

        // Part of #1037 V1: record Vec locals whose capacity is modeled by
        // Vec-level stubs so RawVec stubs skip redundant capacity constraints.
        if stub.is_vec_capacity_modifier()
            && let Some(coll) = collection_local
        {
            self.collections.vec_cap_stubs_fired.insert(coll);
        }

        if vec_stub_invalidates_receiver_adapter_source_data(stub)
            && let Some(coll) = collection_local
        {
            self.invalidate_vec_adapter_source_data(coll);
        }
        if matches!(stub, StubKind::VecAppend | StubKind::VecAppendElements)
            && let Some(other) = resolve_collection_local_from_operand(self, args.get(1))
        {
            self.invalidate_vec_adapter_source_data(other);
        }
        if vec_stub_overwrites_dest_adapter_source_data(stub) {
            self.invalidate_vec_adapter_source_data(dest_local);
        }

        match stub {
            StubKind::VecNew | StubKind::VecWithCapacity => {
                self.vec_op_new(
                    VecOpNewContext {
                        stub,
                        args,
                        modified_locals,
                        dest_local,
                        dest_vec_idx,
                        callee,
                    },
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecFromElem => {
                self.vec_op_from_elem(
                    args,
                    modified_locals,
                    dest_local,
                    dest_vec_idx,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecFromSlice => {
                self.vec_op_from_slice(
                    args,
                    modified_locals,
                    dest_local,
                    dest_vec_idx,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
                debug!(dest_local, "VecFromSlice: cloned slice backing into owned Vec");
            }
            StubKind::VecPush => {
                let field_projections = self.resolve_collection_field_projections(args);
                self.vec_op_push(
                    args,
                    modified_locals,
                    collection_local,
                    &field_projections,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecReserve | StubKind::VecReserveExact => {
                use crate::codegen_ay::shared::vec_capacity::VecGrowth;
                self.vec_op_reserve(
                    if stub == StubKind::VecReserveExact {
                        VecGrowth::Exact
                    } else {
                        VecGrowth::Amortized
                    },
                    args,
                    modified_locals,
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecShrinkToFit => {
                self.vec_op_shrink_to_fit(
                    modified_locals,
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecDrop => {
                // Drop is a no-op in the CHC abstraction.
            }
            StubKind::VecPop => {
                let field_projections = self.resolve_collection_field_projections(args);
                let pop = VecPopContext {
                    modified_locals,
                    collection_local,
                    field_projections: &field_projections,
                    dest_local,
                };
                self.vec_op_pop(
                    pop,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecLen => {
                let field_projections = self.resolve_collection_field_projections(args);
                self.vec_op_len(
                    collection_local,
                    dest_local,
                    &field_projections,
                    modified_locals,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecIsEmpty => {
                // Part of #3348: VecIsEmpty via vec_core dispatch enables
                // struct-embedded fallback (C1/C2) that the collection_predicate
                // path lacks. This fixes proof_non_empty_clause_not_empty in
                // ay_self_verify_tseitin.rs where CnfClause(Vec<CnfLit>).0.is_empty()
                // couldn't resolve the sidecar len_var through the struct wrapper.
                let field_projections = self.resolve_collection_field_projections(args);
                self.vec_op_is_empty(
                    collection_local,
                    dest_local,
                    &field_projections,
                    modified_locals,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecAsSlice => {
                let field_projections = self.resolve_collection_field_projections(args);
                self.vec_op_as_slice(
                    modified_locals,
                    collection_local,
                    dest_local,
                    &field_projections,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
                // Part of #3439: when the Vec is accessed through a struct field
                // (e.g., `_ref = &mut (*_self).marks` → deref_mut → slice),
                // record the field projections so register_index_mut_tracking
                // can reconstruct the struct→Vec path for store propagation.
                if let Some(Operand::Copy(place) | Operand::Move(place)) = args.first() {
                    if let Some(rt) = self.ref_resolution.ref_targets.get(&place.local) {
                        if !rt.projections.is_empty() {
                            self.ref_resolution
                                .slice_to_vec_field_projections
                                .insert(dest_local, rt.projections.clone());
                        }
                    }
                }
            }
            StubKind::VecCapacity => {
                self.vec_op_capacity(
                    modified_locals,
                    collection_local,
                    dest_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecAsPtr | StubKind::VecAsMutPtr => {
                let field_projections = self.resolve_collection_field_projections(args);
                self.vec_op_as_ptr(
                    modified_locals,
                    collection_local,
                    &field_projections,
                    dest_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecResize => {
                let field_projections = self.resolve_collection_field_projections(args);
                self.vec_op_resize(
                    args,
                    modified_locals,
                    collection_local,
                    &field_projections,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecClear => {
                self.vec_op_clear(
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #3895: Vec::set_len(new_len) — len-only mutation.
            StubKind::VecSetLen => {
                self.vec_op_set_len(
                    args,
                    modified_locals,
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecClone => {
                self.vec_op_clone(
                    collection_local,
                    dest_local,
                    modified_locals,
                    dest_vec_idx,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            StubKind::VecExtendFromSlice | StubKind::VecExtendRange
                if args.get(1).and_then(|op| op.ty(self.body.locals()).ok()).is_some_and(
                    |ty| !crate::codegen_ay::reduce_loop_rule::extend_source_is_modelled(ty),
                ) =>
            {
                // An adapter source (`map`, `filter`, `take`, a user iterator):
                // the models read only the sequence underneath, never the
                // adapter's closure or its element count
                // (`reduce_loop_rule::extend_source_is_modelled`).
                debug!(?stub, "Vec extend from an adapter the models do not read — fail closed");
                self.record_sound_fallback_reason("vec_extend_adapter_unmodelled");
            }
            StubKind::VecExtendFromSlice | StubKind::VecExtendRange => {
                // Part of #3607 D3: detect Range argument type at dispatch time.
                // `<Vec as Extend<T>>::extend` resolves to VecExtendFromSlice by
                // default because the callee path lacks "Range". Check args[1]
                // type for RangeInclusive/Range to redirect.
                let is_range = args
                    .get(1)
                    .and_then(|op| {
                        let ty = op.ty(self.body.locals()).ok()?;
                        let name = format!("{:?}", ty.kind());
                        Some(name.contains("Range"))
                    })
                    .unwrap_or(false);
                if is_range || matches!(stub, StubKind::VecExtendRange) {
                    extend_capacity_check = self.vec_op_extend_range(
                        args,
                        modified_locals,
                        collection_local,
                        &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                    );
                } else {
                    self.vec_op_extend_from_slice(
                        args,
                        modified_locals,
                        collection_local,
                        &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                    );
                }
            }
            // Reversal has an EXACT element mapping (`new[i] == old[len-1-i]`),
            // so it does not belong in the unconstrained-permutation family.
            // Falls back to that family only if the receiver's data array or
            // length cannot be resolved.
            StubKind::VecReverse => {
                // A length past the unroll bound is handled INSIDE the exact
                // model (that array is left unconstrained), so `false` here means
                // only one thing: the receiver's Vec representation could not be
                // recovered, and NOTHING was emitted.
                let modeled = self.vec_op_reverse(
                    collection_local,
                    modified_locals,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
                if !modeled {
                    // The receiver's data array is UNTOUCHED, i.e. the reversal
                    // became an identity. That is the shape that proves false
                    // post-conditions, so fail closed.
                    self.record_sound_fallback_reason("vec_permutation_receiver_unresolved");
                }
            }
            // Part of #4135: permutation operations — preserve len, re-bind data
            // to a permutation of the input (see `vec_op_permutation`).
            StubKind::VecSort | StubKind::VecSwap => {
                let modeled = self.vec_op_permutation(
                    collection_local,
                    modified_locals,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                    &format!("{stub:?}"),
                );
                if !modeled {
                    self.record_sound_fallback_reason("vec_permutation_receiver_unresolved");
                }
            }
            // Part of #4135: Vec::append(&mut self, &mut other).
            StubKind::VecAppend | StubKind::VecAppendElements => {
                extend_capacity_check = self.vec_op_append(
                    args,
                    modified_locals,
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::truncate(&mut self, len).
            StubKind::VecTruncate => {
                self.vec_op_truncate(
                    args,
                    modified_locals,
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::insert(&mut self, index, element).
            StubKind::VecInsert => {
                self.vec_op_insert(
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::remove(&mut self, index) -> T.
            StubKind::VecRemove => {
                self.vec_op_remove(
                    collection_local,
                    dest_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: retain/dedup — filtering operations.
            StubKind::VecRetain | StubKind::VecDedup => {
                self.vec_op_filter_inplace(
                    collection_local,
                    &format!("{stub:?}"),
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::drain(range).
            StubKind::VecDrain => {
                self.vec_op_drain(
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::splice(range, replace_with).
            StubKind::VecSplice => {
                self.vec_op_splice(
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::split_off(at) -> Vec<T>.
            StubKind::VecSplitOff => {
                split_off_bounds_check = self.vec_op_split_off(
                    args,
                    modified_locals,
                    collection_local,
                    dest_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::last() -> Option<&T>.
            StubKind::VecLast => {
                self.vec_op_last(
                    collection_local,
                    dest_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: Vec::resize internal extend_with(n).
            StubKind::VecExtendWith => {
                self.vec_op_extend_with(
                    args,
                    modified_locals,
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: trusted-length iterator extend.
            StubKind::VecExtendTrusted => {
                self.vec_op_extend_trusted(
                    collection_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // Part of #4135: FromIterator::from_iter(iter) -> Vec<T>.
            StubKind::VecFromIter => {
                self.vec_op_from_iter(
                    collection_local,
                    dest_local,
                    &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
                );
            }
            // No-op / identity stubs that don't mutate Vec state in the model.
            // VecSpareCapacityMut: returns &mut [MaybeUninit<T>] — no len change.
            // VecIntoBoxedSlice: consumes Vec, returns Box<[T]> — no Vec mutation.
            // VecWithCapacityIn/VecFromRawPartsIn: handled by VecNew/pointer paths.
            StubKind::VecSpareCapacityMut
            | StubKind::VecIntoBoxedSlice
            | StubKind::VecWithCapacityIn
            | StubKind::VecFromRawPartsIn => {
                // Sound over-approximation: state vars unconstrained (identity).
                debug!(?stub, "codegen_call_vec_core: identity pass-through for internal stub");
            }
            // All is_vec_core() variants are matched above. This arm catches
            // StubKind variants that should never reach here.
            other => {
                // SOUND AUDIT (#3369): unexpected stub with &[] extra_dests — target
                // retains identity (under-approx). Reclassified from record_sound_fallback.
                warn!(?other, "codegen_call_vec_core: unexpected stub — update routing");
                self.record_fallback();
                let new_output_args = self.build_output_args(modified_locals, &[]);
                self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
                return;
            }
        }

        let sidecar_receiver = if self.resolve_collection_field_projections(args).is_empty()
            && args.first().is_some_and(|arg| match arg {
                Operand::Copy(place) | Operand::Move(place) => place.projection.is_empty(),
                _ => false,
            }) {
            collection_local
        } else {
            None
        };
        self.finish_sidecar_vec_mutation(
            stub,
            sidecar_receiver,
            destination.projection.is_empty().then_some(dest_local),
            modified_locals,
            &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
        );

        // Drain pending_checks from build_memory_store (VecPop Mem-level mirror).
        // VecPop's memory mirror writes to stack locals, which are always valid.
        // Emitting error rules for stack-local writes adds spurious reachability
        // to error state. Clear instead of emit. Part of #3359.
        self.heap_state.pending_checks.clear();

        // The closure `retain`, `dedup_by(_key)` and `sort_by(_key)` run on
        // the elements is never walked: the models only constrain the
        // result. A closure that can carry an obligation (an `assert!`, an
        // overflowing add) lost it, and `v.retain(|x| { assert!(*x < 200);
        // true })` verified clean where Kani fails (walker fail-closed review 6
        // round 3, `h17_retain_bug`, `h18_sort_by_key_bug`). Such a closure
        // gets an uncertified reach check wherever the call is reached.
        if matches!(stub, StubKind::VecRetain | StubKind::VecDedup | StubKind::VecSort)
            && super::codegen_call_iterator_adapter::closure_arg_may_carry_obligation(self, args)
        {
            let t = super::codegen_call_virtual_inline::uncertified_check::uncertified_reach_check(
                self,
                super::codegen_call_virtual_inline::uncertified_check::VEC_CLOSURE_STEP_UNCERTIFIED,
            );
            let check = super::inline_body::DeferredInlineCheck {
                check: t,
                kind: trust_mc_core::violation::PropertyKind::Assertion,
                message: Some(format!(
                    "a closure `{stub:?}` runs on the elements can fail its checks (not \
                     replayed by the CHC encoder)"
                )),
                write_mark: self.heap_state.write_mark(),
                merge_key: None,
            };
            let mut body: Vec<Expr> = stmt_constraints.to_vec();
            body.extend(extra_constraints.iter().cloned());
            self.emit_deferred_inline_checks_at(from_app, &body, target, vec![check]);
        }

        // The condition reads the call's entry state only, so it is posed on
        // the statement constraints alone: the length update's constraints
        // assume it.
        if let Some(no_panic) = extend_capacity_check {
            let check = super::inline_body::DeferredInlineCheck {
                check: no_panic,
                kind: trust_mc_core::violation::PropertyKind::Assertion,
                message: Some("capacity overflow".to_string()),
                write_mark: self.heap_state.write_mark(),
                merge_key: None,
            };
            self.emit_deferred_inline_checks_at(from_app, stmt_constraints, target, vec![check]);
        }
        if let Some(no_panic) = split_off_bounds_check {
            let check = super::inline_body::DeferredInlineCheck {
                check: no_panic,
                kind: trust_mc_core::violation::PropertyKind::Assertion,
                message: Some("`at` split index should be <= len".to_string()),
                write_mark: self.heap_state.write_mark(),
                merge_key: None,
            };
            self.emit_deferred_inline_checks_at(from_app, stmt_constraints, target, vec![check]);
        }

        let new_output_args = self.build_output_args(modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            extra_constraints,
        );
    }
}

fn resolve_collection_local_from_operand(
    ctx: &ChcCtx<'_, '_>,
    arg: Option<&Operand>,
) -> Option<usize> {
    if let Some(Operand::Copy(place) | Operand::Move(place)) = arg {
        let ref_local = place.local;
        Some(ctx.ref_resolution.ref_targets.get(&ref_local).map_or(ref_local, |rt| rt.local))
    } else {
        None
    }
}

fn vec_stub_invalidates_receiver_adapter_source_data(stub: StubKind) -> bool {
    matches!(
        stub,
        StubKind::VecPush
            | StubKind::VecPop
            | StubKind::VecAsMutPtr
            | StubKind::VecResize
            | StubKind::VecSetLen
            | StubKind::VecClear
            | StubKind::VecExtendFromSlice
            | StubKind::VecExtendRange
            | StubKind::VecAppendElements
            | StubKind::VecExtendWith
            | StubKind::VecExtendTrusted
            | StubKind::VecSwap
            | StubKind::VecRetain
            | StubKind::VecAppend
            | StubKind::VecReverse
            | StubKind::VecDedup
            | StubKind::VecSplitOff
            | StubKind::VecSort
            | StubKind::VecDrain
            | StubKind::VecSplice
            | StubKind::VecTruncate
            | StubKind::VecInsert
            | StubKind::VecRemove
    )
}

fn vec_stub_overwrites_dest_adapter_source_data(stub: StubKind) -> bool {
    matches!(
        stub,
        StubKind::VecNew
            | StubKind::VecWithCapacity
            | StubKind::VecWithCapacityIn
            | StubKind::VecFromElem
            | StubKind::VecFromSlice
            | StubKind::VecClone
            | StubKind::VecFromIter
            | StubKind::VecSplitOff
    )
}
