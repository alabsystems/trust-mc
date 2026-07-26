// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Miscellaneous compiler intrinsic handlers for CHC codegen.
//!
//! Handles intrinsics lacking MIR bodies: volatile ops (in `misc_intrinsics_volatile.rs`),
//! arith_offset, float_to_int_unchecked (#3668), write_bytes, assert_zero_valid,
//! forget, mem::zeroed (#3702), TypeId::of (#4273), and others. Without these
//! handlers the intrinsics increment `unhandled_calls`, converting PROOF -> CTREX.
//!
//! Part of #3444, #3456, #3464, #3702, #4273.

use ay_bindings::Expr;
use rustc_middle::ty::layout::ValidityRequirement;
use rustc_public::mir::{BasicBlockIdx, CopyNonOverlapping, Operand};
use rustc_public::rustc_internal;
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};
use std::collections::HashMap;
use tracing::debug;

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::{CallCoerce, emit_sound_fallback_goto};
use super::super::codegen_rules::CodegenRules;
use super::super::ptr_offset_common;
use super::super::stmt_accumulator::StmtAccumulator;
use super::misc_intrinsics_pointer;
use super::misc_intrinsics_volatile;
use crate::codegen_ay::types::POINTER_WIDTH;

/// Detected miscellaneous intrinsic kind.
#[derive(Debug, Clone, Copy)]
pub(in crate::codegen_ay::chc) enum MiscIntrinsicKind {
    /// `volatile_load(ptr) -> T` — identical to regular load for verification.
    VolatileLoad,
    /// `volatile_store(ptr, val) -> ()` — no-op for verification.
    VolatileStore,
    /// `unaligned_volatile_load(ptr) -> T` — same as volatile_load.
    UnalignedVolatileLoad,
    /// `float_to_int_unchecked(f) -> Int` — UB if out of range, unconstrained result.
    FloatToIntUnchecked,
    /// `arith_offset(base, offset) -> *const T` — pointer arithmetic.
    ArithOffset,
    /// `ptr.offset_from(rhs) -> isize` — signed pointer distance.
    PtrOffsetFrom,
    /// `ptr.offset_from_unsigned(rhs) -> usize` — unsigned pointer distance.
    PtrOffsetFromUnsigned,
    /// `check_language_ub()` / `check_library_ub()` / `intrinsics::ub_checks() -> bool`.
    UbChecksEnabled,
    /// `write_bytes(dst, val, count) -> ()` — memory fill, unconstrained.
    WriteBytes,
    /// `volatile_copy_memory(dst, src, count) -> ()` — memory copy.
    VolatileCopyMemory,
    /// `volatile_copy_nonoverlapping_memory(dst, src, count) -> ()` — memory copy.
    VolatileCopyNonOverlappingMemory,
    /// `assert_inhabited::<T>()` — UB when `T` is uninhabited (e.g. `!`, empty enum).
    AssertInhabited,
    /// `assert_zero_valid::<T>()` — UB when `T` forbids the all-zero bit pattern.
    AssertZeroValid,
    /// `assert_mem_uninitialized_valid::<T>()` — UB when `T` forbids uninitialized memory.
    AssertMemUninitializedValid,
    /// `forget(val) -> ()` — skip destructor, no-op for verification model.
    Forget,
    /// `breakpoint() -> ()` — debugger trap intrinsic; pure no-op for verification.
    Breakpoint,
    /// `typed_swap_nonoverlapping(x, y) -> ()` — memory swap, unconstrained.
    TypedSwapNonoverlapping,
    /// `ptr_guaranteed_cmp(a, b) -> u8` — returns 1 if ptrs equal, 0 otherwise.
    PtrGuaranteedCmp,
    /// `discriminant_value(&T) -> isize` — returns the discriminant of an enum,
    /// or 0 for non-enum types.
    DiscriminantValue,
    /// `std::mem::zeroed::<T>() -> T` — returns all-zero bit pattern (#3702).
    MemZeroed,
    /// `offset_from_unsigned::runtime_ptr_ge(self, origin) -> bool` — Part of #3783.
    /// Internal runtime check within `offset_from_unsigned` that verifies `self >= origin`.
    RuntimePtrGe,
    /// `MaybeUninit::<T>::uninit()` — creates uninitialized storage.
    /// Part of #3792: for Array-sorted destinations (SIMD types), must produce an
    /// unconstrained value of the correct sort. fn_inline translates the body to
    /// Bool (from the unit `()` aggregate), causing sort mismatch with Array dests.
    MaybeUninitUninit,
    /// `std::mem::uninitialized::<T>() -> T` — deprecated, returns uninitialized storage.
    /// Part of #3798: intercept before fn_inline to avoid type/size fallback.
    /// Sound: leaves destination unconstrained (nondeterministic value).
    MemUninitialized,
    /// `std::mem::replace(&mut T, T) -> T` — swap value at reference with new, return old.
    /// Part of #4092: direct handler mirrors `codegen_typed_swap` architecture.
    MemReplace,
    /// `TypeId::of::<T>()` / `core::intrinsics::type_id::<T>()` — returns a
    /// deterministic 128-bit type identity hash. Without this handler, the call
    /// falls through to unconstrained fallback, producing symbolic TypeId values
    /// that break `<dyn Error>::is::<T>()` and similar dynamic type checks.
    /// Part of #4273.
    TypeIdOf,
}

/// Detect miscellaneous intrinsic from callee path.
///
/// Returns the intrinsic kind if the path matches a known intrinsic,
/// None otherwise.
pub(in crate::codegen_ay::chc) fn detect_misc_intrinsic(path: &str) -> Option<MiscIntrinsicKind> {
    let is_compiler_intrinsic =
        path.starts_with("core::intrinsics::") || path.starts_with("std::intrinsics::");
    let method = path
        .rsplit("::")
        .find(|segment| !segment.is_empty() && !segment.starts_with('<'))?
        .split('<')
        .next()?;
    match method {
        "volatile_load" => Some(MiscIntrinsicKind::VolatileLoad),
        // #3728: core::ptr::read_volatile may not inline to volatile_load.
        "read_volatile" if path.contains("core::ptr::") => Some(MiscIntrinsicKind::VolatileLoad),
        "volatile_store" => Some(MiscIntrinsicKind::VolatileStore),
        // #3728: symmetric with read_volatile above.
        "write_volatile" if path.contains("core::ptr::") => Some(MiscIntrinsicKind::VolatileStore),
        "unaligned_volatile_load" => Some(MiscIntrinsicKind::UnalignedVolatileLoad),
        "float_to_int_unchecked" => Some(MiscIntrinsicKind::FloatToIntUnchecked),
        "arith_offset" => Some(MiscIntrinsicKind::ArithOffset),
        "offset_from" if path.contains("::ptr::") => Some(MiscIntrinsicKind::PtrOffsetFrom),
        "offset_from_unsigned" if path.contains("::ptr::") => {
            Some(MiscIntrinsicKind::PtrOffsetFromUnsigned)
        }
        "check_language_ub" if path.contains("::ub_checks::") => {
            Some(MiscIntrinsicKind::UbChecksEnabled)
        }
        "check_library_ub" if path.contains("::ub_checks::") => {
            Some(MiscIntrinsicKind::UbChecksEnabled)
        }
        "ub_checks" if path.contains("intrinsics::") => Some(MiscIntrinsicKind::UbChecksEnabled),
        "write_bytes" => Some(MiscIntrinsicKind::WriteBytes),
        "volatile_copy_memory" => Some(MiscIntrinsicKind::VolatileCopyMemory),
        "volatile_copy_nonoverlapping_memory" => {
            Some(MiscIntrinsicKind::VolatileCopyNonOverlappingMemory)
        }
        // Compile-time type-validity checks. Undefined behaviour when the target
        // type is uninhabited / forbids the zero or uninitialized bit pattern;
        // otherwise a runtime no-op. Resolved statically via rustc queries.
        "assert_inhabited" if is_compiler_intrinsic => Some(MiscIntrinsicKind::AssertInhabited),
        "assert_zero_valid" if is_compiler_intrinsic => Some(MiscIntrinsicKind::AssertZeroValid),
        "assert_mem_uninitialized_valid" if is_compiler_intrinsic => {
            Some(MiscIntrinsicKind::AssertMemUninitializedValid)
        }
        // Part of #3456: forget — no-op for verification. Guard: core only.
        "forget" if path.contains("core::mem::") || path.contains("intrinsics::") => {
            Some(MiscIntrinsicKind::Forget)
        }
        // breakpoint — debugger trap intrinsic, a pure no-op. Intercept it here
        // (pre-fn_inline) so it never falls through to the fn_inline fallback,
        // which would mint a spurious `P_inf_` inferable predicate and demote
        // the (correct) proof to FAILURE. The codegen catch-all emits a plain
        // goto-to-target no-op, matching Kani's SKIP. Guard: intrinsics only.
        "breakpoint" if path.contains("intrinsics::") => Some(MiscIntrinsicKind::Breakpoint),
        // Part of #3456: typed memory swap.
        "typed_swap_nonoverlapping" => Some(MiscIntrinsicKind::TypedSwapNonoverlapping),
        // Part of #3464: std::mem::swap -> typed_swap. Guard: core/std only.
        "swap" if path.contains("std::mem::") || path.contains("core::mem::") => {
            Some(MiscIntrinsicKind::TypedSwapNonoverlapping)
        }
        "ptr_guaranteed_cmp" => Some(MiscIntrinsicKind::PtrGuaranteedCmp),
        // discriminant_value intrinsic: returns discriminant of an enum, 0 for non-enums.
        "discriminant_value" => Some(MiscIntrinsicKind::DiscriminantValue),
        // Part of #3702: std::mem::zeroed() — typed zero value.
        "zeroed" if path.contains("std::mem::") || path.contains("core::mem::") => {
            Some(MiscIntrinsicKind::MemZeroed)
        }
        // Part of #3783: runtime pointer comparison within offset_from_unsigned.
        // Encodes as BV unsigned comparison on pointer values.
        "runtime_ptr_ge" if path.contains("::ptr::") => Some(MiscIntrinsicKind::RuntimePtrGe),
        // Part of #3792: MaybeUninit::uninit() — produces uninitialized storage.
        // Must be intercepted before fn_inline: the body creates `MaybeUninit { uninit: () }`
        // which translates to Bool, but SIMD destinations need Array sort.
        "uninit" if path.contains("MaybeUninit") => Some(MiscIntrinsicKind::MaybeUninitUninit),
        // Part of #3798: std::mem::uninitialized() — deprecated but used in older tests.
        // Intercept before fn_inline to avoid type/size fallback from inlining the body.
        "uninitialized"
            if path.contains("std::mem::")
                || path.contains("core::mem::")
                || path.contains("core::intrinsics::") =>
        {
            Some(MiscIntrinsicKind::MemUninitialized)
        }
        // Part of #4092: std::mem::replace / core::mem::replace — direct CHC handler.
        "replace" if path.contains("std::mem::") || path.contains("core::mem::") => {
            Some(MiscIntrinsicKind::MemReplace)
        }
        // Part of #4273: TypeId::of::<T>() and the underlying type_id intrinsic.
        // TypeId::of appears as `std::any::TypeId::of` or `core::any::TypeId::of`.
        // The raw intrinsic appears as `core::intrinsics::type_id`.
        "of" if path.contains("TypeId") || path.contains("any::") => {
            Some(MiscIntrinsicKind::TypeIdOf)
        }
        "type_id" if path.contains("intrinsics") => Some(MiscIntrinsicKind::TypeIdOf),
        _ => None,
    }
}

/// Handle a miscellaneous intrinsic call in CHC codegen.
///
/// Emits sound over-approximation transition rules without incrementing the
/// `unhandled_call` diagnostic counter.
pub(in crate::codegen_ay::chc) fn codegen_misc_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: MiscIntrinsicKind,
) {
    match kind {
        MiscIntrinsicKind::ArithOffset => {
            misc_intrinsics_pointer::codegen_arith_offset(ctx, dcx, target)
        }
        MiscIntrinsicKind::PtrOffsetFrom => ptr_offset_common::codegen_ptr_offset_from_call(
            ctx,
            dcx,
            target,
            false,
            "codegen_misc_intrinsic::PtrOffsetFrom",
        ),
        MiscIntrinsicKind::PtrOffsetFromUnsigned => {
            ptr_offset_common::codegen_ptr_offset_from_call(
                ctx,
                dcx,
                target,
                true,
                "codegen_misc_intrinsic::PtrOffsetFromUnsigned",
            )
        }
        MiscIntrinsicKind::UbChecksEnabled => {
            misc_intrinsics_pointer::codegen_bool_const_intrinsic(
                ctx,
                dcx,
                target,
                true,
                "codegen_misc_intrinsic::UbChecksEnabled",
            )
        }
        // Part of #3464: volatile_load/store with value propagation.
        MiscIntrinsicKind::VolatileLoad | MiscIntrinsicKind::UnalignedVolatileLoad => {
            misc_intrinsics_volatile::codegen_volatile_load(ctx, dcx, target)
        }
        MiscIntrinsicKind::VolatileStore => {
            misc_intrinsics_volatile::codegen_volatile_store(ctx, dcx, target)
        }
        MiscIntrinsicKind::VolatileCopyMemory => {
            codegen_volatile_copy(ctx, dcx, target, "volatile_copy_memory")
        }
        MiscIntrinsicKind::VolatileCopyNonOverlappingMemory => {
            codegen_volatile_copy(ctx, dcx, target, "volatile_copy_nonoverlapping_memory")
        }
        // Part of #3464: typed_swap with cross-assignment.
        MiscIntrinsicKind::TypedSwapNonoverlapping => {
            misc_intrinsics_volatile::codegen_typed_swap(ctx, dcx, target)
        }
        // Part of #3470: ptr_guaranteed_cmp returns 1u8 if equal, 0u8 otherwise.
        MiscIntrinsicKind::PtrGuaranteedCmp => {
            misc_intrinsics_pointer::codegen_ptr_guaranteed_cmp(ctx, dcx, target)
        }
        // discriminant_value(&T) -> isize: returns enum discriminant or 0 for non-enums.
        MiscIntrinsicKind::DiscriminantValue => codegen_discriminant_value(ctx, dcx, target),
        // Part of #3668: float_to_int_unchecked — BV-level IEEE 754 extraction.
        MiscIntrinsicKind::FloatToIntUnchecked => codegen_float_to_int_unchecked(ctx, dcx, target),
        // Part of #3702: write_bytes — try precise zero-fill for mem::zeroed() shape.
        MiscIntrinsicKind::WriteBytes => {
            if !super::misc_intrinsics_write_bytes::try_codegen_full_write_bytes(ctx, dcx, target) {
                codegen_unconstrained_intrinsic(ctx, dcx, target, kind);
            }
        }
        // Part of #3702: mem::zeroed() — produce typed zero for destination.
        MiscIntrinsicKind::MemZeroed => {
            super::misc_intrinsics_mem_zeroed::codegen_mem_zeroed(ctx, dcx, target)
        }
        // Part of #3783: runtime pointer comparison — encode as BV unsigned >=.
        MiscIntrinsicKind::RuntimePtrGe => {
            misc_intrinsics_pointer::codegen_runtime_ptr_ge(ctx, dcx, target)
        }
        // Part of #4092: mem::replace — structural read-old/write-new/return-old.
        MiscIntrinsicKind::MemReplace => {
            misc_intrinsics_volatile::codegen_mem_replace(ctx, dcx, target)
        }
        // Part of #4273: TypeId::of::<T>() — deterministic bv128 constant.
        MiscIntrinsicKind::TypeIdOf => codegen_type_id_of(ctx, dcx, target),
        // Compile-time type-validity assertions: fire a block-reachability-gated
        // error rule when rustc proves the type is invalid for the requirement,
        // then continue as a no-op transition.
        MiscIntrinsicKind::AssertInhabited
        | MiscIntrinsicKind::AssertZeroValid
        | MiscIntrinsicKind::AssertMemUninitializedValid => {
            codegen_assert_validity(ctx, dcx, target, kind)
        }
        _ => codegen_unconstrained_intrinsic(ctx, dcx, target, kind),
    }
}

/// Handle `discriminant_value(&T) -> isize`.
///
/// Returns the discriminant of an enum variant, or 0 for non-enum types.
/// The argument is a reference `&T`; we resolve it through `ref_targets`
/// to find the underlying local, then delegate to `translate_discriminant`
/// for the enum case.
fn codegen_discriminant_value(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    if let Some(result) = try_resolve_discriminant_value(ctx, dcx) {
        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            let constraint = ctx.make_coerced_eq_constraint(
                &dest_var,
                result,
                out_sort,
                dest_local,
                "codegen_discriminant_value",
            );
            let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
            ctx.emit_goto_rule_extra(
                dcx.from_app,
                target,
                &new_output_args,
                dcx.stmt_constraints,
                constraint,
            );
            debug!("CHC: discriminant_value encoded precisely");
            return;
        }
    }

    // Fallback: unconstrained return (sound over-approximation).
    debug!("CHC: discriminant_value fallback -- unconstrained");
    emit_sound_fallback_goto(
        ctx,
        dcx.from_app,
        target,
        dcx.modified_locals,
        &[dest_local],
        dcx.stmt_constraints,
    );
}

/// Resolve discriminant value from the `&T` argument. Returns `Some(0)` for
/// non-enum types; delegates to `translate_discriminant` or
/// `const_ref_discriminants` for enums. Part of #3798.
fn try_resolve_discriminant_value(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<Expr> {
    let arg = dcx.args.first()?;

    // Extract pointee type T from the &T argument type.
    let pointee_ty = arg.ty(ctx.body.locals()).ok().and_then(|ty| match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => Some(pointee),
        TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) => Some(pointee),
        _ => None,
    })?;

    // Non-enum types always have discriminant 0.
    match pointee_ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => {
            let variants = def.variants();
            if variants.len() <= 1 {
                // Struct or single-variant enum: discriminant is always 0.
                return Some(Expr::bitvec_const(0u128, POINTER_WIDTH));
            }
            // Multi-variant enum: resolve the underlying local to get the
            // symbolic discriminant expression.
            if let Some(target_local) =
                super::super::codegen_call_atomic::resolve_ptr_target_local(ctx, arg)
            {
                let place = rustc_public::mir::Place { local: target_local, projection: vec![] };
                if let Some(expr) = ctx.translate_discriminant(&place, dcx.modified_locals) {
                    return Some(expr);
                }
            }
            // Part of #3798: const_ref_discriminants fallback for promoted refs.
            if let Operand::Copy(place) | Operand::Move(place) = arg
                && place.projection.is_empty()
                && let Some(&discr) = ctx.ref_resolution.const_ref_discriminants.get(&place.local)
            {
                return Some(Expr::bitvec_const(discr as i128, POINTER_WIDTH));
            }
            None
        }
        _ => {
            // Primitive, tuple, closure, etc.: discriminant is always 0.
            Some(Expr::bitvec_const(0u128, POINTER_WIDTH))
        }
    }
}

/// Handle `float_to_int_unchecked(f) -> Int` via BV-level IEEE 754 extraction.
/// UB-free precondition (finite + in-range) means only truncation is needed.
/// Falls back to unconstrained for untranslatable types. Part of #3668.
fn codegen_float_to_int_unchecked(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local: usize = dcx.destination.local;

    // Resolve the source float and target integer once, so the UB safety check
    // and the result extraction share the same translated operand.
    let built = resolve_float_to_int_src_target(ctx, dcx).and_then(
        |(src_value, target_width, is_signed)| {
            // `float_to_int_unchecked` is Undefined Behavior when the source is
            // NaN/infinite or out of the target integer's range. Emit a safety
            // error rule that is reachable exactly when the conversion is not
            // well-defined. The predicate is pure bit-vector (no FP theory), so
            // the CHC/HORN backend accepts it. Part of the UB-soundness fixes.
            if let Some(safe_pred) =
                super::float_to_int_saturating::build_float_to_int_ub_free_predicate(
                    &src_value,
                    target_width,
                    is_signed,
                )
            {
                ctx.emit_error_rule_for_condition(
                    dcx.from_app,
                    safe_pred,
                    dcx.stmt_constraints,
                    dcx.bb_idx,
                );
                debug!("CHC: float_to_int_unchecked UB range/NaN safety check emitted");
            }
            build_float_to_int_extraction(&src_value, target_width, is_signed)
        },
    );

    if let Some(int_expr) = built
        && let Some((_, dest_var)) = ctx.resolve_destination(dest_local)
        && let Some(eq) = ctx.make_coerced_eq_constraint(
            &dest_var,
            int_expr,
            dest_var.sort(),
            dest_local,
            "float_to_int_unchecked",
        )
    {
        let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
        ctx.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &new_output_args,
            dcx.stmt_constraints,
            [eq],
        );
        debug!("CHC: float_to_int_unchecked BV extraction (Part of #3668)");
        return;
    }
    debug!("CHC: float_to_int_unchecked fallback -- unconstrained");
    emit_sound_fallback_goto(
        ctx,
        dcx.from_app,
        target,
        dcx.modified_locals,
        &[dest_local],
        dcx.stmt_constraints,
    );
}

/// Resolve the translated source float operand and the target integer
/// `(width, signed)` for a `float_to_int_unchecked` call. Returns `None` for
/// untranslatable operands or non-integer destinations.
fn resolve_float_to_int_src_target(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<(Expr, u32, bool)> {
    let src_value = ctx.translate_operand_with_modified(dcx.args.first()?, dcx.modified_locals)?;
    let dest_ty = ctx.body.locals().get(dcx.destination.local)?.ty;
    let (target_width, is_signed) = match dest_ty.kind() {
        TyKind::RigidTy(RigidTy::Int(int_ty)) => {
            use rustc_public::ty::IntTy;
            match int_ty {
                IntTy::I8 => (8u32, true),
                IntTy::I16 => (16, true),
                IntTy::I32 => (32, true),
                IntTy::I64 => (64, true),
                IntTy::I128 => (128, true),
                IntTy::Isize => (POINTER_WIDTH, true),
            }
        }
        TyKind::RigidTy(RigidTy::Uint(uint_ty)) => {
            use rustc_public::ty::UintTy;
            match uint_ty {
                UintTy::U8 => (8u32, false),
                UintTy::U16 => (16, false),
                UintTy::U32 => (32, false),
                UintTy::U64 => (64, false),
                UintTy::U128 => (128, false),
                UintTy::Usize => (POINTER_WIDTH, false),
            }
        }
        _ => return None,
    };
    Some((src_value, target_width, is_signed))
}

/// Build the truncating BV extraction for a `float_to_int_unchecked` result.
fn build_float_to_int_extraction(
    src_value: &Expr,
    target_width: u32,
    is_signed: bool,
) -> Option<Expr> {
    // Part of #3465, #3870: HORN rejects `fp.to_{s,u}bv`, so use pure-BV paths only.
    // Try CHC-local extractor first, then module-level pure-BV, then FP theory fallback.
    super::float_predicates::build_float_to_int_expr(src_value, target_width, is_signed)
        .or_else(|| {
            crate::codegen_ay::float_arithmetic::float_to_int_bv_pure(
                src_value.clone(),
                target_width,
                is_signed,
            )
        })
        .or_else(|| {
            crate::codegen_ay::float_arithmetic::float_to_int_bv(
                src_value.clone(),
                target_width,
                is_signed,
            )
        })
}

/// Handle `TypeId::of::<T>()` by computing the rustc type_id_hash as a concrete bv128.
///
/// Extracts the generic type parameter `T` from the FnDef operand, computes the
/// deterministic 128-bit TypeId hash using `tcx.type_id_hash()`, and constrains
/// the destination local to that constant. Falls back to unconstrained if the
/// type parameter is unresolvable or type_id_hash panics for exotic types.
///
/// This mirrors the inline walker handler `try_inline_type_id_of` in
/// `nested_call.rs` but operates at the top-level call dispatch context.
/// Part of #4273.
fn codegen_type_id_of(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
) {
    let dest_local = dcx.destination.local;

    if let Some(type_id_expr) = try_resolve_type_id_of(ctx, dcx) {
        if let Some((_, dest_var)) = ctx.resolve_destination(dest_local) {
            let out_sort = dest_var.sort();
            if let Some(eq) = ctx.make_coerced_eq_constraint(
                &dest_var,
                type_id_expr,
                out_sort,
                dest_local,
                "codegen_type_id_of",
            ) {
                let new_output_args = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
                ctx.emit_goto_rule_extra(
                    dcx.from_app,
                    target,
                    &new_output_args,
                    dcx.stmt_constraints,
                    [eq],
                );
                debug!("CHC: TypeId::of encoded as constant bv128 (Part of #4273)");
                return;
            }
        }
    }

    // Fallback: unconstrained return (sound over-approximation).
    debug!("CHC: TypeId::of fallback -- unconstrained (Part of #4273)");
    emit_sound_fallback_goto(
        ctx,
        dcx.from_app,
        target,
        dcx.modified_locals,
        &[dest_local],
        dcx.stmt_constraints,
    );
}

/// Handle the compile-time type-validity assertions `assert_inhabited`,
/// `assert_zero_valid`, and `assert_mem_uninitialized_valid`.
///
/// Emits a block-reachability-gated error rule (via `bool_const(false)`) only
/// when rustc definitively proves the target type violates the requirement;
/// otherwise it is a pure no-op. Control flow always continues through the
/// unconstrained transition so downstream blocks stay well-formed. An
/// undecidable / parametric / layout-error answer is treated as a no-op, so
/// e.g. `mem::zeroed::<u32>()` (which lowers to `assert_zero_valid::<u32>()`)
/// is never flagged.
fn codegen_assert_validity(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: MiscIntrinsicKind,
) {
    let requirement = match kind {
        MiscIntrinsicKind::AssertInhabited => ValidityRequirement::Inhabited,
        MiscIntrinsicKind::AssertZeroValid => ValidityRequirement::Zero,
        MiscIntrinsicKind::AssertMemUninitializedValid => {
            ValidityRequirement::UninitMitigated0x01Fill
        }
        _ => unreachable!("codegen_assert_validity called with non-assert kind: {kind:?}"),
    };

    if let Some(ty) = assert_validity_type_arg(ctx, dcx)
        && crate::kani_middle::type_validity::assert_requirement_definitely_violated(
            ctx.tcx,
            ty,
            requirement,
        )
    {
        debug!(?kind, "CHC: assert_* type-validity violated — emitting error rule");
        ctx.emit_error_rule_for_condition(
            dcx.from_app,
            Expr::bool_const(false),
            dcx.stmt_constraints,
            dcx.bb_idx,
        );
    }

    // The assert intrinsic itself returns `()`; continue the transition so the
    // rest of the encoding stays consistent regardless of the validity outcome.
    codegen_unconstrained_intrinsic(ctx, dcx, target, kind);
}

/// Extract the single generic type argument `T` from an `assert_*::<T>()` call.
///
/// Skips unresolved `Param` types — only concrete, monomorphized types can
/// answer the validity query. Mirrors `try_resolve_type_id_of`.
fn assert_validity_type_arg(
    ctx: &ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> Option<rustc_public::ty::Ty> {
    let func_ty = dcx.func.ty(ctx.body.locals()).ok()?;
    let substs = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(_, substs)) => substs,
        _ => return None,
    };
    let ty = substs
        .0
        .iter()
        .find_map(|arg| if let GenericArgKind::Type(ty) = arg { Some(*ty) } else { None })?;
    if matches!(ty.kind(), TyKind::Param(_)) {
        return None;
    }
    Some(ty)
}

/// Handle `volatile_copy_memory(dst, src, count)` and
/// `volatile_copy_nonoverlapping_memory(dst, src, count)`.
///
/// Rust's volatile copy intrinsics take `dst` before `src`, while the existing
/// CHC copy model is shaped like `copy_nonoverlapping(src, dst, count)`.
/// Part of #3703: avoid identity-retaining unconstrained fallback for modeled copies.
fn codegen_volatile_copy(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    intrinsic_name: &'static str,
) {
    if dcx.args.len() < 3 {
        debug!(
            intrinsic_name,
            arg_count = dcx.args.len(),
            "CHC: volatile copy missing args; emitting demoted fallback"
        );
        ctx.record_fallback();
        let out = ctx.build_output_args(dcx.modified_locals, &[]);
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
        return;
    }

    let copy = volatile_copy_to_copy_model(dcx.args).expect("volatile copy arg length checked");
    let mut extra_constraints: Vec<Expr> = Vec::new();
    let mut modified = dcx.modified_locals.clone();
    let mut last_constraint_for_local: HashMap<usize, usize> =
        HashMap::with_capacity(ctx.body.locals().len());

    let handled = {
        let mut acc = StmtAccumulator::new(
            &mut modified,
            &mut extra_constraints,
            &mut last_constraint_for_local,
        );
        // P4-1: volatile_copy_memory is the legal-overlap (memmove)
        // variant; only the nonoverlapping variant carries the
        // range-disjointness obligation.
        ctx.try_encode_copy_nonoverlapping_intrinsic(
            &copy,
            dcx.bb_idx,
            &mut acc,
            intrinsic_name == "volatile_copy_memory",
        )
    };

    let out = ctx.build_output_args(&modified, &[]);
    if handled {
        debug!(intrinsic_name, "CHC: volatile copy modeled via CopyNonOverlapping path");
        ctx.emit_goto_rule_extra(
            dcx.from_app,
            target,
            &out,
            dcx.stmt_constraints,
            extra_constraints,
        );
    } else {
        debug!(
            intrinsic_name,
            "CHC: volatile copy destination unresolved; emitting demoted fallback"
        );
        ctx.record_fallback();
        ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
    }
}

/// Adapt Rust volatile-copy intrinsic operands to the CHC copy model.
///
/// The Rust intrinsics use `(dst, src, count)`, but the reusable CHC copy
/// encoder takes the `CopyNonOverlapping` MIR shape `(src, dst, count)`.
fn volatile_copy_to_copy_model(args: &[Operand]) -> Option<CopyNonOverlapping> {
    if args.len() < 3 {
        return None;
    }
    Some(CopyNonOverlapping { src: args[1].clone(), dst: args[0].clone(), count: args[2].clone() })
}

/// Extract the type parameter T from `TypeId::of::<T>()` / `type_id::<T>()`
/// and compute the concrete bv128 hash.
fn try_resolve_type_id_of(ctx: &ChcCtx<'_, '_>, dcx: &DispatchCallContext<'_>) -> Option<Expr> {
    // Extract generic type arg T from the func operand's FnDef type.
    let func_ty = dcx.func.ty(ctx.body.locals()).ok()?;
    let fn_substs = match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(_, substs)) => substs,
        _ => return None,
    };
    let target_ty = fn_substs
        .0
        .iter()
        .find_map(|arg| if let GenericArgKind::Type(ty) = arg { Some(*ty) } else { None })?;

    // Only handle concrete (monomorphized) types -- skip unresolved Param types.
    if matches!(target_ty.kind(), TyKind::Param(_)) {
        return None;
    }

    // Compute the deterministic TypeId hash using the compiler's own method.
    // Wrap in catch_unwind because type_id_hash can ICE for exotic types.
    let internal_ty = rustc_internal::internal(ctx.tcx, target_ty);
    let type_id_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        ctx.tcx.type_id_hash(internal_ty).as_u128()
    }));
    let type_id_value = match type_id_result {
        Ok(v) => v,
        Err(_) => return None,
    };

    debug!(
        ?target_ty,
        type_id_value, "CHC: resolved TypeId::of type parameter to concrete hash (Part of #4273)"
    );
    Some(Expr::bitvec_const(type_id_value, 128))
}

/// Handle intrinsics with no dedicated CHC model (sound over-approximation).
/// Memory-mutating intrinsics (#3703) use record_fallback (DEMOTED).
fn codegen_unconstrained_intrinsic(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: BasicBlockIdx,
    kind: MiscIntrinsicKind,
) {
    let dest_local: usize = dcx.destination.local;
    debug!(?kind, "CHC: misc intrinsic handled as unconstrained (Part of #3444)");
    if matches!(
        kind,
        MiscIntrinsicKind::WriteBytes
            | MiscIntrinsicKind::VolatileCopyMemory
            | MiscIntrinsicKind::VolatileCopyNonOverlappingMemory
    ) {
        ctx.record_fallback();
    }
    let out = ctx.build_output_args(dcx.modified_locals, &[dest_local]);
    ctx.emit_goto_rule(dcx.from_app, target, &out, dcx.stmt_constraints);
}

#[cfg(test)]
mod tests {
    use super::*;
    use rustc_public::mir::Place;

    fn local_operand(local: usize) -> Operand {
        Operand::Copy(Place { local, projection: vec![] })
    }

    #[test]
    fn test_detect_runtime_ptr_ge() {
        // Part of #3783: runtime_ptr_ge within offset_from_unsigned must be detected.
        let path = "std::ptr::const_ptr::<impl *const T>::offset_from_unsigned::runtime_ptr_ge";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::RuntimePtrGe)),
            "runtime_ptr_ge in ptr path should detect as RuntimePtrGe, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_runtime_ptr_ge_not_matched_outside_ptr() {
        // Guard: runtime_ptr_ge in non-ptr paths should NOT match.
        let path = "my_crate::runtime_ptr_ge";
        assert!(detect_misc_intrinsic(path).is_none());
    }

    #[test]
    fn test_detect_offset_from_unsigned() {
        let path = "std::ptr::const_ptr::<impl *const [u64; 3]>::offset_from_unsigned";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::PtrOffsetFromUnsigned)),
            "offset_from_unsigned should detect as PtrOffsetFromUnsigned, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_check_language_ub() {
        let path = "core::ub_checks::check_language_ub";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::UbChecksEnabled)),
            "check_language_ub should detect as UbChecksEnabled, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_intrinsics_ub_checks() {
        let path = "core::intrinsics::ub_checks";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::UbChecksEnabled)),
            "intrinsics::ub_checks should detect as UbChecksEnabled, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_type_validity_assertions_require_compiler_intrinsic_authority() {
        assert!(matches!(
            detect_misc_intrinsic("core::intrinsics::assert_zero_valid::<&u8>"),
            Some(MiscIntrinsicKind::AssertZeroValid)
        ));
        assert!(matches!(
            detect_misc_intrinsic("std::intrinsics::assert_inhabited::<Never>"),
            Some(MiscIntrinsicKind::AssertInhabited)
        ));
        assert!(matches!(
            detect_misc_intrinsic("core::intrinsics::assert_mem_uninitialized_valid::<bool>"),
            Some(MiscIntrinsicKind::AssertMemUninitializedValid)
        ));
        assert!(
            detect_misc_intrinsic("my_crate::intrinsics::assert_zero_valid::<&u8>").is_none(),
            "a user-defined lookalike must not be treated as a compiler intrinsic"
        );
    }

    #[test]
    fn test_detect_volatile_copy_intrinsics() {
        let copy = detect_misc_intrinsic("core::intrinsics::volatile_copy_memory::<u32>");
        assert!(
            matches!(copy, Some(MiscIntrinsicKind::VolatileCopyMemory)),
            "volatile_copy_memory should detect as VolatileCopyMemory, got {copy:?}"
        );

        let copy_nonoverlapping =
            detect_misc_intrinsic("core::intrinsics::volatile_copy_nonoverlapping_memory::<u32>");
        assert!(
            matches!(
                copy_nonoverlapping,
                Some(MiscIntrinsicKind::VolatileCopyNonOverlappingMemory)
            ),
            "volatile_copy_nonoverlapping_memory should detect, got {copy_nonoverlapping:?}"
        );
    }

    #[test]
    fn test_volatile_copy_to_copy_model_reorders_dst_src() {
        let args = [local_operand(10), local_operand(20), local_operand(30)];
        let copy = volatile_copy_to_copy_model(&args).expect("three args should adapt");

        let Operand::Copy(src) = copy.src else { panic!("src operand shape") };
        let Operand::Copy(dst) = copy.dst else { panic!("dst operand shape") };
        let Operand::Copy(count) = copy.count else { panic!("count operand shape") };

        assert_eq!(src.local, 20, "Rust volatile-copy arg1 is CHC copy src");
        assert_eq!(dst.local, 10, "Rust volatile-copy arg0 is CHC copy dst");
        assert_eq!(count.local, 30, "Rust volatile-copy arg2 is CHC copy count");
    }

    #[test]
    fn test_volatile_copy_to_copy_model_requires_three_args() {
        let args = [local_operand(10), local_operand(20)];
        assert!(volatile_copy_to_copy_model(&args).is_none());
    }

    /// Part of #3798: discriminant_value intrinsic must be detected from both
    /// the bare intrinsic path and the std re-export.
    #[test]
    fn test_detect_discriminant_value() {
        let path = "core::intrinsics::discriminant_value";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::DiscriminantValue)),
            "discriminant_value should detect as DiscriminantValue, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_discriminant_value_std_reexport() {
        let path = "std::intrinsics::discriminant_value";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::DiscriminantValue)),
            "std::intrinsics::discriminant_value should detect, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_uninitialized_with_generic_suffix() {
        let path = "core::mem::uninitialized::<i32>";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::MemUninitialized)),
            "generic-suffixed mem::uninitialized should detect, got {kind:?}"
        );
    }

    /// Part of #4092: mem::replace must be detected from std and core paths.
    #[test]
    fn test_detect_mem_replace_std() {
        let path = "std::mem::replace::<i32>";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::MemReplace)),
            "std::mem::replace should detect as MemReplace, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_mem_replace_core() {
        let path = "core::mem::replace::<Pair>";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::MemReplace)),
            "core::mem::replace should detect as MemReplace, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_mem_replace_not_other_crate() {
        let path = "my_crate::mem::replace";
        assert!(
            detect_misc_intrinsic(path).is_none(),
            "replace in non-std/core path should not detect"
        );
    }

    /// Part of #4273: TypeId::of must be detected from std and core paths.
    #[test]
    fn test_detect_type_id_of_std() {
        let path = "std::any::TypeId::of::<i32>";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::TypeIdOf)),
            "std::any::TypeId::of should detect as TypeIdOf, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_type_id_of_core() {
        let path = "core::any::TypeId::of::<String>";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::TypeIdOf)),
            "core::any::TypeId::of should detect as TypeIdOf, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_type_id_intrinsic() {
        let path = "core::intrinsics::type_id::<u64>";
        let kind = detect_misc_intrinsic(path);
        assert!(
            matches!(kind, Some(MiscIntrinsicKind::TypeIdOf)),
            "core::intrinsics::type_id should detect as TypeIdOf, got {kind:?}"
        );
    }

    #[test]
    fn test_detect_type_id_not_other_crate() {
        // "of" in a non-TypeId path should NOT match.
        let path = "my_crate::Foo::of";
        assert!(detect_misc_intrinsic(path).is_none(), "'of' in non-TypeId path should not detect");
    }
}
