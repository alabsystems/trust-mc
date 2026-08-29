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
    /// Try to codegen a stdlib call via semantic stub registry.
    ///
    pub(in crate::codegen_ay::statement) fn try_codegen_stdlib_stub_call(
        &mut self,
        func: &Operand,
        args: &[Operand],
        destination: &Place,
        target: Option<BasicBlockIdx>,
    ) -> CallDispatchOutcome {
        let Some(callee_path) = self.resolve_callee_path(func) else {
            return CallDispatchOutcome::Miss;
        };

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
            return CallDispatchOutcome::from_nested_target(Some(result));
        }

        // `<String as BoundedArbitrary>::bounded_any::<N>` — model the bound the
        // API promises instead of the UTF-8 chunking the library goes through.
        if let Some(result) =
            self.try_codegen_bounded_string_precheck(func, &callee_path, destination, target)
        {
            return CallDispatchOutcome::from_handled_target(result);
        }

        // Pre-check for Cow<str>::to_string() which has path that doesn't contain "Cow" (Part of #1738)
        if let Some(result) =
            self.try_codegen_cow_tostring_precheck(func, &callee_path, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target(Some(result));
        }

        // Pre-check for MaybeUninit::uninit()/assume_init(): model uninitialized
        // memory as a fresh arbitrary inner value, before these tiny generic methods
        // get mini-inlined into an unencodable union construction/transmute.
        if let Some(result) =
            self.try_codegen_maybe_uninit_precheck(&callee_path, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target(Some(result));
        }

        let Some(stub_kind) = self.stub_registry.lookup(&callee_path) else {
            return CallDispatchOutcome::Miss;
        };
        debug!(?stub_kind, %callee_path, "AY stdlib stub matched");

        // Try simple stubs first (constants, identity, no-op, diverging, BigRational)
        if let Some(result) =
            self.try_codegen_simple_stub(stub_kind, args, destination, target, &callee_path)
        {
            return CallDispatchOutcome::from_nested_target(Some(result));
        }

        if let Some(result) =
            self.try_codegen_slice_comparison_stub(stub_kind, func, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target(Some(result));
        }

        if let Some(result) =
            self.try_codegen_alloc_layout_stub(stub_kind, func, args, destination, target)
        {
            return CallDispatchOutcome::from_nested_target(Some(result));
        }

        if let Some(result) = self.try_codegen_pointer_stub(stub_kind, args, destination, target) {
            return CallDispatchOutcome::from_nested_target(Some(result));
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
            return CallDispatchOutcome::from_nested_target(result);
        }

        if stub_in(BIGINT_STUBS, stub_kind) {
            return CallDispatchOutcome::from_handled_target(self.codegen_bigint_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(HASHMAP_STUBS, stub_kind) {
            return CallDispatchOutcome::from_handled_target(self.codegen_hashmap_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(VEC_STUBS, stub_kind) {
            // MEMUB fail-closed: the abstract Vec model has no shadow-init
            // integration — Vec bodies are prefix-abstracted
            // (reachability.rs: "std::vec::Vec::"), so the UninitPass never
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
            return CallDispatchOutcome::from_handled_target(self.codegen_vec_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(ITER_STUBS, stub_kind) {
            return CallDispatchOutcome::from_handled_target(self.codegen_iter_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(STRING_STUBS, stub_kind) {
            return CallDispatchOutcome::from_handled_target(self.codegen_string_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(BTREESET_STUBS, stub_kind) {
            return CallDispatchOutcome::from_handled_target(self.codegen_btreeset_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(HASHSET_STUBS, stub_kind) {
            return CallDispatchOutcome::from_handled_target(self.codegen_hashset_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
        }
        if stub_in(BTREEMAP_INTERNAL_STUBS, stub_kind) {
            return CallDispatchOutcome::from_handled_target(self.codegen_btreemap_internal_stub(
                stub_kind,
                args,
                destination,
                target,
                &callee_path,
            ));
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
                Some(self.codegen_slice_partial_eq_stub(args, destination, target))
            }
            StubKind::SliceIndexIndex | StubKind::IndexIndex | StubKind::IndexMut => {
                self.authenticated_core_index_args(func, args)?;
                Some(self.codegen_slice_index_stub(args, destination, target))
            }
            StubKind::SliceGetUnchecked => {
                Some(self.codegen_slice_index_stub(args, destination, target))
            }
            StubKind::SliceIsEmpty => {
                Some(self.codegen_slice_is_empty_stub(args, destination, target))
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
                // fail-closed fallback. Returning `Some(None)` here would map to
                // Diverge (call_outcome.rs:35) and UNSOUNDLY prune the post-call
                // path for a non-diverging `get`.
                self.codegen_slice_get(args, destination, target).map(Some)
            }
            StubKind::SlicePartitionPoint => {
                // Part of dterm#6841: partition_point returns 0..=len.
                // Sound over-approximation: constrain result to [0, len].
                Some(self.codegen_slice_partition_point(args, destination, target))
            }
            StubKind::MemchrMemchr => {
                // core::slice::memchr::* -> Option<usize>, SOUND over-approximation.
                // `.map(Some)` (like SliceGet): success -> Some(Some(bb)); an unresolved
                // Option encoding -> None here -> falls through to the fail-closed
                // fallback. Returning Some(None) would map to Diverge (unsound).
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
            StubKind::OptionUnwrap => Some(self.codegen_option_unwrap(args, destination, target)),
            StubKind::PrimitivePartialEqEq => {
                Some(self.codegen_partial_eq(args, destination, target))
            }
            StubKind::PrimitivePartialEqNe => {
                Some(self.codegen_partial_ne(args, destination, target))
            }
            StubKind::PrimitiveClone => {
                Some(self.codegen_primitive_clone(args, destination, target))
            }
            StubKind::OrdCmp => Some(self.codegen_ord_cmp(args, destination, target)),
            StubKind::PrimitivePartialOrdLt => {
                debug!("codegen_stubbed_call: PartialOrd::lt");
                Some(self.codegen_partial_ord_cmp(args, destination, target, "lt"))
            }
            StubKind::PrimitivePartialOrdLe => {
                debug!("codegen_stubbed_call: PartialOrd::le");
                Some(self.codegen_partial_ord_cmp(args, destination, target, "le"))
            }
            StubKind::PrimitivePartialOrdGt => {
                debug!("codegen_stubbed_call: PartialOrd::gt");
                Some(self.codegen_partial_ord_cmp(args, destination, target, "gt"))
            }
            StubKind::PrimitivePartialOrdGe => {
                debug!("codegen_stubbed_call: PartialOrd::ge");
                Some(self.codegen_partial_ord_cmp(args, destination, target, "ge"))
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
            StubKind::RustAlloc => Some(self.codegen_rust_alloc(args, destination, target)),
            StubKind::RustAllocZeroed => {
                Some(self.codegen_rust_alloc_zeroed(args, destination, target))
            }
            StubKind::RustDealloc => Some(self.codegen_rust_dealloc(args, target)),
            StubKind::RustRealloc => Some(self.codegen_rust_realloc(args, destination, target)),
            StubKind::LayoutSize => Some(self.codegen_layout_size(args, destination, target)),
            StubKind::LayoutAlign => Some(self.codegen_layout_align(args, destination, target)),
            StubKind::LayoutDangling => {
                Some(self.codegen_layout_dangling(args, destination, target))
            }
            StubKind::LayoutIsSizeAlignValid => {
                Some(self.codegen_layout_is_size_align_valid(destination, target))
            }
            StubKind::LayoutArray => {
                let (elem_size, elem_align) = self.extract_element_type_layout(func);
                Some(self.codegen_layout_array_with_type(
                    args,
                    destination,
                    target,
                    elem_size,
                    elem_align,
                ))
            }
            StubKind::LayoutArrayInner => {
                // Part of #3273: Layout::array::inner(element_size, align, n)
                // Args are runtime values, not generics. Delegate to from_size_align
                // after computing array_size = element_size * n.
                Some(self.codegen_layout_array_inner(args, destination, target))
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
                Some(self.codegen_layout_from_size_align_unchecked(args, destination, target))
            }
            StubKind::AllocatorAllocate => {
                Some(self.codegen_allocator_allocate(args, destination, target))
            }
            StubKind::GlobalAllocImpl => {
                debug!("codegen_stubbed_call: Global::alloc_impl");
                Some(self.codegen_allocator_allocate(args, destination, target))
            }
            StubKind::LayoutFromSizeAlign => {
                Some(self.codegen_layout_from_size_align(args, destination, target))
            }
            StubKind::LayoutCalculateLayoutFor => {
                Some(self.codegen_layout_calculate_layout_for(func, args, destination, target))
            }
            StubKind::LayoutForValueRaw => {
                Some(self.codegen_layout_for_value_raw(func, destination, target))
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
                let (size, align) = self.extract_element_type_layout(func);
                let size_expr = Expr::bitvec_const(size as u128, POINTER_WIDTH);
                let align_expr = Expr::bitvec_const(align as u128, POINTER_WIDTH);
                let ptr = self.ctx.heap_alloc(size_expr, align_expr);
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
            StubKind::PtrAdd => Some(self.codegen_ptr_add(args, destination, target)),
            StubKind::PtrSub => Some(self.codegen_ptr_sub(args, destination, target)),
            StubKind::PtrWrappingAdd => {
                Some(self.codegen_ptr_wrapping_add(args, destination, target))
            }
            StubKind::PtrWrappingSub => {
                Some(self.codegen_ptr_wrapping_sub(args, destination, target))
            }
            StubKind::PtrWrappingOffset => {
                Some(self.codegen_ptr_wrapping_offset(args, destination, target))
            }
            // Part of #3510: wrapping_byte_offset does NOT scale by sizeof(T).
            StubKind::PtrWrappingByteOffset => {
                Some(self.codegen_ptr_wrapping_byte_offset(args, destination, target))
            }
            // Part of #3514: wrapping_byte_add/sub do NOT scale by sizeof(T).
            StubKind::PtrWrappingByteAdd => {
                Some(self.codegen_ptr_wrapping_byte_add(args, destination, target))
            }
            StubKind::PtrWrappingByteSub => {
                Some(self.codegen_ptr_wrapping_byte_sub(args, destination, target))
            }
            StubKind::PtrWithMetadataOf => {
                Some(self.codegen_ptr_with_metadata_of(args, destination, target))
            }
            StubKind::PtrWrite => Some(self.codegen_ptr_write(args, target)),
            StubKind::PtrRead => Some(self.codegen_ptr_read(args, destination, target)),
            StubKind::NonNullNew => Some(self.codegen_nonnull_new(args, destination, target)),
            StubKind::NonNullCast => Some(self.codegen_nonnull_cast(args, destination, target)),
            StubKind::NonNullSliceFromRawParts => {
                Some(self.codegen_nonnull_slice_from_raw_parts(args, destination, target))
            }
            StubKind::OptionOkOr => Some(self.codegen_option_ok_or(args, destination, target)),
            StubKind::NonNullAsNonNullPtr => {
                Some(self.codegen_nonnull_as_nonnull_ptr(args, destination, target))
            }
            StubKind::TryBranch => Some(self.codegen_try_branch(args, destination, target)),
            // Part of #3532: ptr.with_addr(addr) returns the addr argument as a pointer.
            // Mirrors CHC handler in stubs_util_intrinsics.rs:659.
            StubKind::PtrWithAddr => Some(self.codegen_ptr_with_addr(args, destination, target)),
            _other => None, // internal enum: StubKind
        }
    }
}
