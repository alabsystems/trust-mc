// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Stub registry dispatch for stdlib call codegen.
//!
//! This module contains `try_codegen_stdlib_stub_call` which maps
//! resolved callee paths to stub handlers via the `StubKind` enum.
//!
//! Simple constant/identity/no-op/diverging stubs are in `stub_dispatch_simple.rs`.
//! Pointer/memory stubs are in `stub_dispatch_memory.rs`.
//! Option/Result stubs are in `stub_dispatch_option_result.rs`.
//!
//! Extracted from dispatch.rs per #2027 for maintainability.

use ay_bindings::Expr;
use rustc_public::mir::{BasicBlockIdx, Operand, Place};
use tracing::{debug, warn};

use super::CallDispatchOutcome;
use super::stub_dispatch_table::{
    BIGINT_STUBS, BTREEMAP_INTERNAL_STUBS, BTREESET_STUBS, HASHMAP_STUBS, HASHSET_STUBS,
    ITER_STUBS, OPTION_RESULT_STUBS, POINTER_MEMORY_STUBS, PREHANDLED_STUBS, STRING_STUBS,
    VEC_STUBS, stub_in,
};
use crate::codegen_ay::statement::StatementCodegen;
use crate::codegen_ay::statement::panic_helpers::bmc_is_no_return_panic_helper;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::POINTER_WIDTH;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Authenticate the registry candidate before a query handler can use it.
    /// Later family-specific checks still run in the dispatcher below.
    fn stdlib_registry_candidate(&self, func: &Operand, callee_path: &str) -> Option<StubKind> {
        let stub_kind = self.stub_registry.lookup(callee_path)?;
        if stub_kind == StubKind::RawVecPtr && !self.native_rawvec_ptr_call(func) {
            return None;
        }
        if crate::codegen_ay::shared::string_identity::is_string_stub(stub_kind)
            && (self.ctx.unit_has_stubs()
                || !crate::codegen_ay::shared::string_identity::string_stub_is_authorized(
                    self.ctx.tcx,
                    func,
                    self.body.locals(),
                    stub_kind,
                ))
        {
            return None;
        }
        if crate::codegen_ay::shared::callee_is_local_item(func, self.body.locals()) {
            debug!(?stub_kind, %callee_path, "a local item named like a std stub: not a stub");
            return None;
        }
        // BMC's replacements live on its attached transformer, independently
        // of the CHC TLS read by the shared predicate. A replacement anywhere
        // in this unit can change a query transitively. Scope this veto to the
        // six query categories; other families keep their existing routing.
        if matches!(
            stub_kind,
            StubKind::VecLen
                | StubKind::VecCapacity
                | StubKind::VecIsEmpty
                | StubKind::VecAsPtr
                | StubKind::VecAsMutPtr
                | StubKind::VecAsSlice
        ) && self.ctx.unit_has_stubs()
        {
            return None;
        }
        crate::codegen_ay::shared::vec_query_identity::vec_query_stub_is_authorized(
            self.ctx.tcx,
            func,
            self.body.locals(),
            stub_kind,
        )
        .then_some(stub_kind)
    }

    /// Classification-only access to the production BMC decision. This does
    /// not encode a call, establish layout custody or run a solver.
    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay) fn test_stdlib_registry_candidate(
        &self,
        func: &Operand,
    ) -> Option<StubKind> {
        self.stdlib_registry_candidate(func, &self.resolve_callee_path(func)?)
    }

    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay) fn test_string_dispatch_misses(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> bool {
        matches!(
            self.try_codegen_stdlib_stub_call(func, args, destination, target),
            CallDispatchOutcome::Miss
        )
    }

    /// Try to codegen a stdlib call via semantic stub registry.
    ///
    // INVARIANT for every arm below: a handler's `None` means "I could not encode
    // this", never "this call diverges". Route it with `.map(Some)` (outer None =>
    // the next dispatcher, and finally the fail-closed unsupported fallback), NOT
    // `Some(..)`. Inside a handler the same rule reads `return target`, not
    // `return None`. See docs/dispatch-diverge-hazard-2026-09-17.md.
    //
    // Every nested result below is converted by
    // `CallDispatchOutcome::from_nested_target_for_call`, the backstop for an arm
    // that still spells `Some(..)`: an inner `None` on a call WITH a MIR return
    // target is `FallthroughToUnsupported` (recorded, successor edge kept), and
    // only a call with no return target diverges. Before it, that inner `None`
    // was `Diverge`, which DELETES the post-call path and makes every later
    // assertion hold vacuously.
    pub(in crate::codegen_ay::statement) fn try_codegen_stdlib_stub_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> CallDispatchOutcome {
        if target.is_some() && self.native_empty_string_nullness_as_ptr(func, args, destination) {
            return CallDispatchOutcome::from_nested_target_for_call(Some(target), target);
        }
        // Typed headers grant neither an unqualified pointer nor child writeback.
        if crate::codegen_ay::native_string_unmodeled_operation(
            self.ctx.tcx,
            func,
            self.body.locals(),
            !self.ctx.unit_has_stubs(),
        ) {
            self.ctx.unsupported_with_fallback(
                "native_string_unmodeled_operation",
                "actual inherent String operation lacks native custody",
            );
            self.codegen_symbolic_result(destination);
            return CallDispatchOutcome::from_nested_target_for_call(Some(target), target);
        }
        let Some(callee_path) = self.resolve_callee_path(func) else {
            return CallDispatchOutcome::Miss;
        };

        if target.is_some()
            && callee_path.ends_with("::from_ref")
            && self.try_codegen_shared_scalar_slice(func, args, destination).is_some()
        {
            return CallDispatchOutcome::from_nested_target_for_call(Some(target), target);
        }

        if target.is_none() && bmc_is_no_return_panic_helper(&callee_path) {
            // These shims take the panic message as a leading `&str` (e.g.
            // `core::panicking::panic(msg)`, `Result::unwrap_failed(msg, _)`).
            // Name it on the Failed Checks line; None keeps "panic reached".
            let message = self.panic_message_from_args(args);
            self.record_violation_guarded_with_message(Expr::bool_const(true), "panic", message);
            return CallDispatchOutcome::Diverge;
        }

        // Pre-check for BTree internal stubs that require examining generic args (Part of #1627)
        if let Some(result) =
            self.try_codegen_btree_internal_precheck(func, &callee_path, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target_for_call(Some(result), target);
        }

        // Pre-check for Cow<str>::to_string() which has path that doesn't contain "Cow" (Part of #1738)
        if let Some(result) =
            self.try_codegen_cow_tostring_precheck(func, &callee_path, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target_for_call(Some(result), target);
        }

        // Pre-check for MaybeUninit::uninit()/assume_init(): model uninitialized
        // memory as a fresh arbitrary inner value, before these tiny generic methods
        // get mini-inlined into an unencodable union construction/transmute.
        if let Some(result) =
            self.try_codegen_maybe_uninit_precheck(&callee_path, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target_for_call(Some(result), target);
        }

        let Some(stub_kind) = self.stdlib_registry_candidate(func, &callee_path) else {
            return CallDispatchOutcome::Miss;
        };
        // `Iterator::sum` is matched by NAME; only core's numeric `Sum` impls
        // are a fold the element-wise unroll encodes (a user `Sum`,
        // `Duration` or `Option<T>` is left to the ordinary call path). The
        // unroll adds what each of core's impls adds, read from the call
        // (`iter_sum_summand::classify_iter_sum`): `+` with its overflow check
        // for a primitive, `wrapping_add` for `Wrapping`, `saturating_add` for
        // `Saturating`.
        if stub_kind == StubKind::IterSum
            && crate::codegen_ay::reduce_loop_rule::iter_sum_call_model(func, self.body.locals())
                .is_none()
        {
            return CallDispatchOutcome::Miss;
        }
        // `SliceRepeat` is a CHC-lane model only (chc/call/codegen_call_slice_repeat.rs).
        // No BMC table routes it, and an unrouted matched stub falls through to
        // Unsupported; before the stub existed `<[T]>::repeat` was a plain Miss
        // here. Keep the BMC lane exactly as it was.
        if stub_kind == StubKind::SliceRepeat {
            return CallDispatchOutcome::Miss;
        }
        debug!(?stub_kind, %callee_path, "AY stdlib stub matched");

        // Try simple stubs first (constants, identity, no-op, diverging, BigRational)
        if let Some(result) =
            self.try_codegen_simple_stub(stub_kind, args, destination, target, &callee_path)
        {
            return CallDispatchOutcome::from_nested_target_for_call(Some(result), target);
        }

        if let Some(result) =
            self.try_codegen_slice_comparison_stub(stub_kind, func, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target_for_call(Some(result), target);
        }

        if let Some(result) =
            self.try_codegen_alloc_layout_stub(stub_kind, func, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target_for_call(Some(result), target);
        }

        if let Some(result) = self.try_codegen_pointer_stub(stub_kind, args, destination, target) {
            return CallDispatchOutcome::from_nested_target_for_call(Some(result), target);
        }

        if stub_in(POINTER_MEMORY_STUBS, stub_kind) {
            let result = self.try_codegen_pointer_memory_stub(stub_kind, args, destination, target);
            if result.is_none() {
                warn!(
                    ?stub_kind,
                    "pointer/memory dispatcher returned None for matched stub variant"
                );
                return CallDispatchOutcome::FallthroughToUnsupported;
            }
            return CallDispatchOutcome::from_nested_target_for_call(result, target);
        }

        // FC-06(bmc): a container model's store through a `&mut` argument is an
        // env-level update the deref-store hook never sees. Classify it against
        // the innermost modifies frame before the handler encodes it
        // (statement::modifies_frame::bmc_modifies_check_stub_mut_args).
        if [BIGINT_STUBS, HASHMAP_STUBS, VEC_STUBS, STRING_STUBS, HASHSET_STUBS, BTREESET_STUBS]
            .iter()
            .any(|family| stub_in(family, stub_kind))
        {
            self.bmc_modifies_check_stub_mut_args(args, &callee_path);
        }
        if stub_in(BIGINT_STUBS, stub_kind) {
            return CallDispatchOutcome::from_fallthrough_result(self.codegen_bigint_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(HASHMAP_STUBS, stub_kind) {
            return CallDispatchOutcome::from_fallthrough_result(self.codegen_hashmap_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(VEC_STUBS, stub_kind) {
            // MEMUB fail-closed: the abstract Vec model has no shadow-init
            // integration — Vec bodies are abstracted at the reachability
            // boundary (kani_middle/std_abstraction.rs), so the UninitPass never
            // sees their reads and the stub blesses whatever bytes the model
            // holds. Under -Z uninit-checks that let
            // `Vec::with_capacity` + `set_len` + `index` (an uninitialized
            // read, corpus uninit/vec-read-bad-len) verify SUCCESSFUL with
            // PROOF_QUALIFIERS:clean — a false proof. Until the Vec stubs
            // track per-element init state, record a demoting fallback so the
            // harness reports INCONCLUSIVE instead of a clean proof. Scoped
            // to uninit-checks runs: no other corpus family passes the flag.
            if self.ctx.config.uninit_checks {
                self.ctx
                    .unsupported_with_fallback("uninit_checks_abstract_vec", callee_path.clone());
            }
            return CallDispatchOutcome::from_fallthrough_result(self.codegen_vec_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(ITER_STUBS, stub_kind) {
            return CallDispatchOutcome::from_fallthrough_result(self.codegen_iter_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
                Some(func),
            ));
        }
        if stub_in(STRING_STUBS, stub_kind) {
            return CallDispatchOutcome::from_fallthrough_result(self.codegen_string_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(BTREESET_STUBS, stub_kind) {
            return CallDispatchOutcome::from_fallthrough_result(self.codegen_btreeset_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(HASHSET_STUBS, stub_kind) {
            return CallDispatchOutcome::from_fallthrough_result(self.codegen_hashset_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(BTREEMAP_INTERNAL_STUBS, stub_kind) {
            return CallDispatchOutcome::from_fallthrough_result(
                self.codegen_btreemap_internal_stub(
                    stub_kind,
                    args,
                    destination,
                    target,
                    &callee_path,
                ),
            );
        }

        if stub_in(OPTION_RESULT_STUBS, stub_kind) {
            return self.try_codegen_option_result_stub(stub_kind, func, args, destination, target);
        }

        if stub_in(PREHANDLED_STUBS, stub_kind) {
            warn!(
                ?stub_kind,
                %callee_path,
                "stub should be handled before stdlib dispatcher — update routing"
            );
            return CallDispatchOutcome::FallthroughToUnsupported;
        }

        CallDispatchOutcome::FallthroughToUnsupported
    }

    fn try_codegen_slice_comparison_stub(
        &mut self,
        stub_kind: StubKind,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        match stub_kind {
            StubKind::SlicePartialEqEqual => {
                // `.map(Some)` for the same reason as PrimitivePartialEqEq below:
                // this stub TAIL-CALLS `codegen_partial_eq` (slice.rs:145), so a
                // plain `Some(..)` would turn that function's fail-closed `None`
                // back into a claim that the call diverges.
                self.codegen_slice_partial_eq_stub(args, destination, target).map(Some)
            }
            StubKind::SliceIndexIndex | StubKind::IndexIndex | StubKind::IndexMut => {
                self.authenticated_core_index_args(func, args)?;
                self.codegen_slice_index_stub(args, destination, target).map(Some)
            }
            StubKind::SliceGetUnchecked => {
                self.codegen_slice_index_stub(args, destination, target).map(Some)
            }
            StubKind::SliceIsEmpty => {
                self.codegen_slice_is_empty_stub(args, destination, target).map(Some)
            }
            StubKind::SliceFirst => {
                // Part of #3768: slice::first — BMC fallback (unconstrained destination).
                // Full semantic encoding is in the CHC path. BMC uses sound over-approx.
                debug!("codegen_stubbed_call: SliceFirst — unconstrained fallback");
                None
            }
            StubKind::SliceGet => {
                // R2: model `<[T]>::get(i)` as `ite(i < len, Some(&a[i]), None)` in
                // the flattened-Option encoding so the ay-pb `eval_lit` chain
                // `.and_then(|i| a.get(i)).copied().unwrap_or(false)` resolves
                // exactly. On success continue with the encoded Option; on ANY
                // unresolved case (range index, non-Option dest, unresolved
                // len/elem) return `None` so dispatch FALLS THROUGH to the
                // fail-closed fallback. `Some(None)` would claim the call
                // diverges (the dispatcher's backstop turns that into the
                // unsupported fallback only because `get` has a return target).
                self.codegen_slice_get(args, destination, target).map(Some)
            }
            StubKind::SlicePartitionPoint => {
                // Part of dterm#6841: partition_point returns 0..=len.
                // Sound over-approximation: constrain result to [0, len].
                self.codegen_slice_partition_point(args, destination, target).map(Some)
            }
            StubKind::MemchrMemchr => {
                // core::slice::memchr::* -> Option<usize>, SOUND over-approximation.
                // `.map(Some)` (like SliceGet): success -> Some(Some(bb)); an unresolved
                // Option encoding -> None here -> falls through to the fail-closed
                // fallback. `Some(None)` would claim the call diverges.
                self.codegen_slice_memchr(args, destination, target).map(Some)
            }
            StubKind::SliceLast
            | StubKind::SliceBinarySearchByKey
            | StubKind::SliceChunks
            | StubKind::SliceWindows => {
                // Part of #4208: sound over-approximation (unconstrained destination).
                debug!("codegen_stubbed_call: {:?} — unconstrained fallback", stub_kind);
                None
            }
            StubKind::OptionUnwrap => {
                self.codegen_option_unwrap(args, destination, target).map(Some)
            }
            StubKind::PrimitivePartialEqEq => {
                // `.map(Some)`, not `Some(..)`, for the reason SliceGet and
                // MemchrMemchr already give: `Some(None)` claims the call
                // diverges, which would PRUNE the post-call path if the
                // dispatcher's backstop did not catch it. `eq` does not
                // diverge, so every `None` here is an unsupported construct —
                // the #703 sort mismatch, or a reference layer that could not
                // be dereferenced. Pruning the path would make every later
                // assertion hold VACUOUSLY; falling through records the
                // fallback and leaves the result unconstrained.
                self.codegen_partial_eq(args, destination, target).map(Some)
            }
            StubKind::PrimitivePartialEqNe => {
                self.codegen_partial_ne(args, destination, target).map(Some)
            }
            StubKind::PrimitiveClone => {
                self.codegen_primitive_clone(args, destination, target).map(Some)
            }
            StubKind::OrdCmp => self.codegen_ord_cmp(args, destination, target).map(Some),
            StubKind::PrimitivePartialOrdLt => {
                debug!("codegen_stubbed_call: PartialOrd::lt");
                self.codegen_partial_ord_cmp(args, destination, target, "lt").map(Some)
            }
            StubKind::PrimitivePartialOrdLe => {
                debug!("codegen_stubbed_call: PartialOrd::le");
                self.codegen_partial_ord_cmp(args, destination, target, "le").map(Some)
            }
            StubKind::PrimitivePartialOrdGt => {
                debug!("codegen_stubbed_call: PartialOrd::gt");
                self.codegen_partial_ord_cmp(args, destination, target, "gt").map(Some)
            }
            StubKind::PrimitivePartialOrdGe => {
                debug!("codegen_stubbed_call: PartialOrd::ge");
                self.codegen_partial_ord_cmp(args, destination, target, "ge").map(Some)
            }
            _other => None, // partial dispatch: StubKind
        }
    }

    fn try_codegen_alloc_layout_stub(
        &mut self,
        stub_kind: StubKind,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        match stub_kind {
            StubKind::RustAlloc => self.codegen_rust_alloc(args, destination, target).map(Some),
            StubKind::RustAllocZeroed => {
                self.codegen_rust_alloc_zeroed(args, destination, target).map(Some)
            }
            StubKind::RustDealloc => self.codegen_rust_dealloc(args, target).map(Some),
            StubKind::RustRealloc => self.codegen_rust_realloc(args, destination, target).map(Some),
            StubKind::LayoutSize => self.codegen_layout_size(args, destination, target).map(Some),
            StubKind::LayoutAlign => self.codegen_layout_align(args, destination, target).map(Some),
            StubKind::LayoutDangling => {
                self.codegen_layout_dangling(args, destination, target).map(Some)
            }
            StubKind::LayoutIsSizeAlignValid => {
                self.codegen_layout_is_size_align_valid(args, destination, target).map(Some)
            }
            StubKind::LayoutArray => {
                let (elem_size, elem_align) = self.extract_element_type_layout(func);
                self.codegen_layout_array_with_type(
                    args,
                    destination,
                    target,
                    elem_size,
                    elem_align,
                )
                .map(Some)
            }
            StubKind::LayoutArrayInner => {
                // Part of #3273: Layout::array::inner(element_size, align, n)
                // Args are runtime values, not generics. Delegate to from_size_align
                // after computing array_size = element_size * n.
                self.codegen_layout_array_inner(args, destination, target).map(Some)
            }
            StubKind::LayoutNew => {
                let (size, align) = self.extract_element_type_layout(func);
                let size_expr = Expr::bitvec_const(size as u128, POINTER_WIDTH);
                let align_expr = Expr::bitvec_const(align as u128, POINTER_WIDTH);
                let layout = self.create_layout_struct(size_expr, align_expr);
                self.assign_value_to_place(destination, layout);
                Some(target)
            }
            StubKind::LayoutFromSizeAlignUnchecked => {
                self.codegen_layout_from_size_align_unchecked(args, destination, target).map(Some)
            }
            StubKind::AllocatorAllocate => {
                self.codegen_allocator_allocate(args, destination, target).map(Some)
            }
            StubKind::GlobalAllocImpl => {
                debug!("codegen_stubbed_call: Global::alloc_impl");
                self.codegen_allocator_allocate(args, destination, target).map(Some)
            }
            StubKind::LayoutFromSizeAlign => {
                self.codegen_layout_from_size_align(args, destination, target).map(Some)
            }
            StubKind::LayoutCalculateLayoutFor => {
                self.codegen_layout_calculate_layout_for(func, args, destination, target).map(Some)
            }
            StubKind::LayoutForValueRaw => {
                self.codegen_layout_for_value_raw(func, destination, target).map(Some)
            }
            // mem::size_of::<T> / mem::align_of::<T>: extract T from func's
            // generic args for correct layout. Moved from simple stubs which
            // incorrectly used the destination type (always usize). Part of #3141.
            StubKind::MemSizeOf => {
                let (size, _align) = self.extract_element_type_layout(func);
                debug!(size, "codegen_stubbed_call: mem::size_of<T>");
                let size_expr = Expr::bitvec_const(size as u128, POINTER_WIDTH);
                self.assign_value_to_place(destination, size_expr);
                Some(target)
            }
            StubKind::MemAlignOf => {
                let (_size, align) = self.extract_element_type_layout(func);
                debug!(align, "codegen_stubbed_call: mem::align_of<T>");
                let align_expr = Expr::bitvec_const(align as u128, POINTER_WIDTH);
                self.assign_value_to_place(destination, align_expr);
                Some(target)
            }
            // Part of #3007: conservative upper bound for Layout::max_size_for_align.
            // Used by Layout::array to check for overflow. Returning isize::MAX
            // lets the overflow check pass for small arrays while remaining sound.
            // Matches CHC-level implementation in alloc_extra.rs.
            StubKind::LayoutMaxSizeForAlign => {
                let max_size = Expr::bitvec_const(i64::MAX as u128, POINTER_WIDTH);
                self.assign_value_to_place(destination, max_size);
                Some(target)
            }
            // Part of #3494: Box::new(value) — allocate heap memory for the boxed value.
            // BoxNew's MIR args contain the value to box (not size/align like RustAlloc).
            // Extract T's layout from func's generic args, allocate, return pointer.
            StubKind::BoxNew => {
                if cfg!(all(trust_toolchain, version("1.101")))
                    && crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(self.ctx.tcx) {
                    self.ctx.unsupported_with_fallback("BoxGlobalAllocator",
                        "Box allocation must execute the user global allocator's body effects");
                }
                let native = self.native_box_new_layout(func, args);
                let (size, align) = native.unwrap_or_else(|| {
                    let (size, align) = self.extract_element_type_layout(func);
                    (size as u64, align as u64)
                });
                let size_expr = Expr::bitvec_const(size as u128, POINTER_WIDTH);
                let align_expr = Expr::bitvec_const(align as u128, POINTER_WIDTH);
                let ptr = if native.is_some() && size == 0 {
                    let pointer = Expr::bitvec_const(align, POINTER_WIDTH);
                    self.ctx.record_box_numeric_address(pointer.clone());
                    pointer
                } else {
                    let pointer = self.ctx.heap_alloc(size_expr, align_expr);
                    if native.is_some() && size <= 0x100000 && align <= 0x100000 {
                        self.ctx.record_native_box_allocation(
                            pointer.clone(),
                            size,
                            align,
                            self.store_path_condition(),
                        );
                    } else if native.is_some() {
                        self.ctx.unsupported_with_fallback(
                            "BoxAllocationExtent",
                            "native allocation exceeds BMC region capacity",
                        );
                    }
                    pointer
                };
                // The boxed value lives at the allocation (box_new_payload.rs).
                self.store_box_new_payload(func, args, &ptr);
                self.assign_value_to_place(destination, ptr);
                Some(target)
            }
            _other => None, // internal enum: StubKind
        }
    }

    fn try_codegen_pointer_stub(
        &mut self,
        stub_kind: StubKind,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> Option<Option<BasicBlockIdx>> {
        match stub_kind {
            StubKind::PtrAdd => self.codegen_ptr_add(args, destination, target).map(Some),
            StubKind::PtrSub => self.codegen_ptr_sub(args, destination, target).map(Some),
            StubKind::PtrWrappingAdd => {
                self.codegen_ptr_wrapping_add(args, destination, target).map(Some)
            }
            StubKind::PtrWrappingSub => {
                self.codegen_ptr_wrapping_sub(args, destination, target).map(Some)
            }
            StubKind::PtrWrappingOffset => {
                self.codegen_ptr_wrapping_offset(args, destination, target).map(Some)
            }
            // Part of #3510: wrapping_byte_offset does NOT scale by sizeof(T).
            StubKind::PtrWrappingByteOffset => {
                self.codegen_ptr_wrapping_byte_offset(args, destination, target).map(Some)
            }
            // Part of #3514: wrapping_byte_add/sub do NOT scale by sizeof(T).
            StubKind::PtrWrappingByteAdd => {
                self.codegen_ptr_wrapping_byte_add(args, destination, target).map(Some)
            }
            StubKind::PtrWrappingByteSub => {
                self.codegen_ptr_wrapping_byte_sub(args, destination, target).map(Some)
            }
            StubKind::PtrWithMetadataOf => {
                self.codegen_ptr_with_metadata_of(args, destination, target).map(Some)
            }
            StubKind::PtrWrite => self.codegen_ptr_write(args, target).map(Some),
            StubKind::PtrRead => self.codegen_ptr_read(args, destination, target).map(Some),
            StubKind::NonNullNew => self.codegen_nonnull_new(args, destination, target).map(Some),
            StubKind::NonNullCast => self.codegen_nonnull_cast(args, destination, target).map(Some),
            StubKind::NonNullSliceFromRawParts => {
                self.codegen_nonnull_slice_from_raw_parts(args, destination, target).map(Some)
            }
            StubKind::OptionOkOr => self.codegen_option_ok_or(args, destination, target).map(Some),
            StubKind::NonNullAsNonNullPtr => {
                self.codegen_nonnull_as_nonnull_ptr(args, destination, target).map(Some)
            }
            StubKind::TryBranch => self.codegen_try_branch(args, destination, target).map(Some),
            // Part of #3532: ptr.with_addr(addr) returns the addr argument as a pointer.
            // Mirrors CHC handler in stubs_util_intrinsics.rs:659.
            StubKind::PtrWithAddr => {
                self.codegen_ptr_with_addr(args, destination, target).map(Some)
            }
            _other => None, // internal enum: StubKind
        }
    }
}
