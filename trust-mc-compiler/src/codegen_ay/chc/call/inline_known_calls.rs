// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pure-call fast paths shared by inline translators.
//! Keeps exact encodings out of heavier MIR inliners to avoid inferable fallback.
//!
//! Raw pointer comparison: `inline_known_calls_raw_ptr.rs`
//! SIMD intrinsics: `inline_known_calls_simd.rs`

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use tracing::debug;

use super::codegen_call_cmp_string::bit_intrinsics::inline_bit_intrinsic_expr;
use super::codegen_call_cmp_string::float_predicates::{
    build_float_predicate_expr, detect_float_predicate,
};
use super::codegen_call_vec::ChcVecFields;
use super::codegen_types::CodegenTypes;
use super::inline_known_calls_raw_ptr::{
    inline_plain_eq_expr, inline_raw_pointer_cmp_expr, operand_is_raw_pointer_like,
};
use super::inline_known_calls_simd::inline_simd_intrinsic_expr;
use super::{ChcCtx, chc_fresh_name, declare_pending_var};
use crate::codegen_ay::chc::call::inline_known_calls_math::{
    infer_inline_arith_signedness, inline_exact_math_call, inline_saturating_arith_expr,
    inline_wrapping_arith_expr,
};
use crate::codegen_ay::chc::codegen_expr_array_eq::{
    build_spec_array_eq, recover_spec_array_eq_len,
};
use crate::codegen_ay::chc::pointer_step::{step_split_pointer, step_split_pointer_sub};
use crate::codegen_ay::chc::stubs_option_helpers::OptionHelpers;
use crate::codegen_ay::chc::ty_signedness;
use crate::codegen_ay::ptr_repr::PtrRepr;
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{
    POINTER_WIDTH, SignExtension, coerce_bitvec_width, unflatten_bitvec_to_datatype,
};

/// Element-scaled pointer arithmetic for the pure-expression inline path.
///
/// `<*const T>::wrapping_add(count)` / `wrapping_sub(count)` step by
/// `count * size_of::<T>()` BYTES. The statement path already scales
/// (`emit_ptr_wrapping_element_transition`); this is the same encoding for
/// call sites that must produce an expression — notably quantifier predicate
/// bodies, where an unscaled step reads the wrong element and refutes a true
/// `forall`.
///
/// FAIL-CLOSED: without a resolved receiver type or a known pointee size this
/// returns `None` (no inline) rather than falling back to a byte-sized step.
fn inline_wrapping_ptr_arith_expr<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    callee_path: &str,
    args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    let method = callee_path.rsplit("::").next()?;
    let is_sub = match method {
        "wrapping_add" => false,
        "wrapping_sub" => true,
        _ => return None,
    };
    if args.len() != 2 {
        return None;
    }
    let receiver = first_arg?;
    // Only a DIRECT raw-pointer receiver: for `&*const T` the translated
    // operand is the reference, not the pointer, so stepping it would move the
    // wrong address.
    let receiver_ty = receiver.ty(caller_locals).ok()?;
    let TyKind::RigidTy(RigidTy::RawPtr(pointee, _)) = receiver_ty.kind() else {
        return None;
    };
    let elem_size = ctx.get_type_size(pointee)?;
    let ptr = args[0].clone();
    if ptr.sort().bitvec_width() != Some(POINTER_WIDTH) {
        return None;
    }
    let count = args.get(1)?.clone();
    if !count.sort().is_bitvec() {
        return None;
    }
    let count = coerce_bitvec_width(count, POINTER_WIDTH, SignExtension::ZeroExtend);
    let offset_bytes = count.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH));
    let step = if is_sub {
        step_split_pointer_sub(ptr, offset_bytes)
    } else {
        step_split_pointer(ptr, offset_bytes)
    };
    debug!(elem_size, is_sub, "CHC: inline wrapping pointer arith - ptr +/- count * sizeof(T)");
    Some(step.result)
}

/// Inline pure call patterns that do not expose a simple MIR body.
pub(in crate::codegen_ay) fn inline_known_call_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    let callee_path = ctx.resolve_callee_path(func).or_else(|| ctx.resolve_fn_def_name(func))?;
    inline_known_call_expr_for_callee_path(
        ctx,
        func,
        &callee_path,
        translated_args,
        first_arg,
        caller_locals,
    )
}

/// Inline pure call patterns using a caller-supplied canonical callee path.
///
/// Ordinary fn-inline can resolve the monomorphized `Instance` even when the
/// call-operand path is too weak for helper detection, so it passes the
/// instance def-path through this entry point.
pub(in crate::codegen_ay) fn inline_known_call_expr_for_callee_path<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    callee_path: &str,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    if let Some(kind) = detect_float_predicate(&callee_path) {
        if translated_args.len() != 1 {
            return None;
        }
        let receiver = translated_args.first()?;
        return build_float_predicate_expr(receiver, kind);
    }
    if let Some(expr) = inline_exact_math_call(callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) =
        inline_wrapping_ptr_arith_expr(ctx, callee_path, translated_args, first_arg, caller_locals)
    {
        return Some(expr);
    }
    if let Some(expr) =
        inline_wrapping_arith_expr(callee_path, translated_args, first_arg, caller_locals)
    {
        return Some(expr);
    }
    if let Some(expr) =
        inline_saturating_arith_expr(callee_path, translated_args, first_arg, caller_locals)
    {
        return Some(expr);
    }
    if let Some(expr) = inline_bit_intrinsic_expr(callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) = inline_pin_identity_expr(callee_path, translated_args) {
        return Some(expr);
    }
    // Part of #4067: Mutex::new(value) is identity in single-threaded verification.
    // Mutex<T> is translated as T (transparent wrapper), so ::new just passes through.
    if let Some(expr) = inline_mutex_new_expr(callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) = inline_option_unwrap_expr(ctx, callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) = inline_option_unwrap_or_expr(ctx, callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) = inline_char_from_u32_unchecked_expr(callee_path, translated_args) {
        return Some(expr);
    }
    // CHAR_FROM_U32_OPTION_MODEL: model the CHECKED `char::from_u32(x)` so that
    // `char::from_u32(x).is_some()` inside `kani::any_where(...)` actually
    // constrains `x` to the valid-char range (see `inline_char_from_u32_expr`).
    if let Some(expr) =
        inline_char_from_u32_expr(ctx, func, callee_path, translated_args, caller_locals)
    {
        return Some(expr);
    }
    if let Some(expr) =
        inline_iter_compare_expr(ctx, func, callee_path, translated_args, caller_locals)
    {
        return Some(expr);
    }
    if let Some(expr) = inline_chars_iterator_eq_expr(callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) = inline_datatype_partial_eq_expr(callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) = inline_option_result_predicate_expr(ctx, callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) =
        inline_nonzero_new_expr(ctx, func, callee_path, translated_args, caller_locals)
    {
        return Some(expr);
    }
    if let Some(expr) =
        inline_primitive_cmp_expr(callee_path, translated_args, first_arg, caller_locals)
    {
        return Some(expr);
    }
    if callee_path.ends_with("::runtime_ptr_ge") && callee_path.contains("::ptr::") {
        return inline_runtime_ptr_ge_expr(translated_args);
    }
    if let Some(expr) = inline_ub_checks_expr(&callee_path, translated_args) {
        return Some(expr);
    }
    if let Some(expr) = inline_pointer_utility_expr(ctx, callee_path, translated_args) {
        return Some(expr);
    }
    // Part of #3875: SpecArrayEq::spec_eq — route fixed-size array equality
    // through the shared helper (inline body has a loop the walker can't handle).
    if let Some(expr) =
        inline_spec_array_eq_expr(callee_path, translated_args, first_arg, caller_locals)
    {
        return Some(expr);
    }
    // Part of #4101: raw_eq inside inlined bodies (e.g., PartialEq::eq for arrays).
    // Without this, assert_eq! on SIMD as_array() results hits raw_eq inside the
    // fn_inline'd PartialEq::eq body, the walker bails, and the result is
    // unconstrained — PDR picks false → spurious CTREX.
    if let Some(expr) = inline_raw_eq_expr(callee_path, translated_args, first_arg, caller_locals) {
        return Some(expr);
    }
    // Part of #4086: SIMD intrinsics inside inlined trait impls (e.g., Add::add
    // calling simd_add). Without this, the inline walker bails on the intrinsic
    // call, leaving the SIMD result unconstrained.
    if let Some(expr) =
        inline_simd_intrinsic_expr(callee_path, translated_args, first_arg, caller_locals)
    {
        return Some(expr);
    }

    // Use path-based stub lookup so this works for nested bodies (closures,
    // inlined functions) where `func` cannot be resolved against ctx.body.
    match ctx.stub_registry.lookup(callee_path)? {
        StubKind::VecLen => inline_vec_len_expr(translated_args),
        // Part of #4057: VecIsEmpty inline fast-path for closure-body Vec accessors.
        StubKind::VecIsEmpty => inline_vec_is_empty_expr(translated_args),
        _ => None,
    }
}

fn inline_pointer_utility_expr<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<Expr> {
    let stub = ctx.stub_registry.lookup(callee_path)?;
    if let Some(expr) = inline_ptr_wrapping_byte_expr(stub, translated_args) {
        return Some(expr);
    }
    match stub {
        StubKind::PtrNull => Some(Expr::bitvec_const(0u64, POINTER_WIDTH)),
        // `<*const T>::is_null` — the provenance is supplied by the CALLEE, not
        // guessed here: the stub kind says this argument is a pointer. What was
        // left to decide is only the *shape*, so the bare width test is replaced
        // by the decoder that answers exactly that and hands back a `Loc`.
        // `thin_address` accepts precisely `width == POINTER_WIDTH`, so the set
        // of accepted arguments is unchanged; a wide pointer still falls through
        // to the walker rather than being null-tested on half of itself.
        StubKind::PtrIsNull | StubKind::PtrIsNullRuntime if translated_args.len() == 1 => {
            let addr = PtrRepr::thin_address(&translated_args[0])?;
            Some(addr.into_expr().eq(Expr::bitvec_const(0u64, POINTER_WIDTH)))
        }
        // Part of #3768: Pointer identity passthrough for inline walker.
        // These are all identity at the BV level — the pointer value doesn't change.
        // Without this, Rc::new's chain (exchange_malloc → NonNull → Rc)
        // loses allocation identity at the NonNull step inside fn-inlined bodies.
        // Note: NonNullNew is excluded — it covers both NonNull::new (returns
        // Option<NonNull<T>>) and new_unchecked (returns NonNull<T>). Treating
        // both as identity loses the Option wrapping for ::new, causing CTREX.
        // Without this fast-path, the inline walker walks the callee body which
        // produces the correct Option construction for ::new and identity for
        // ::new_unchecked.
        StubKind::NonNullAsPtr
        | StubKind::NonNullCast
        | StubKind::NonNullAsNonNullPtr
        | StubKind::UniqueNewUnchecked
        | StubKind::BoxIntoRawWithAllocator
        | StubKind::PtrCast
        | StubKind::PtrCastConst
            if translated_args.len() == 1 =>
        {
            Some(translated_args[0].clone())
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum NonZeroConstructor {
    New,
    NewUnchecked,
}

fn detect_nonzero_constructor(callee_path: &str) -> Option<NonZeroConstructor> {
    if !(callee_path.contains("NonZero") || callee_path.contains("nonzero")) {
        return None;
    }
    match callee_path.rsplit("::").next()? {
        "new" => Some(NonZeroConstructor::New),
        "new_unchecked" => Some(NonZeroConstructor::NewUnchecked),
        _ => None,
    }
}

fn expr_is_nonzero(value: &Expr) -> Option<Expr> {
    if let Some(width) = value.sort().bitvec_width() {
        Some(value.clone().ne(Expr::bitvec_const(0u64, width)))
    } else if value.sort().is_int() {
        Some(value.clone().ne(Expr::int_const(0)))
    } else {
        None
    }
}

fn option_payload_signedness(output_ty: rustc_public::ty::Ty) -> bool {
    if let TyKind::RigidTy(RigidTy::Adt(def, args)) = output_ty.kind()
        && def.kind() == AdtKind::Enum
    {
        for variant in def.variants() {
            if let Some(field) = variant.fields().first() {
                return ty_signedness(field.ty_with_args(&args)).unwrap_or(false);
            }
        }
    }
    ty_signedness(output_ty).unwrap_or(false)
}

fn coerce_nonzero_payload_to_sort<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    payload: Expr,
    target_sort: &Sort,
    signed: bool,
) -> Option<Expr> {
    if payload.sort() == target_sort {
        return Some(payload);
    }
    if payload.sort().is_bitvec() && target_sort.is_datatype() {
        let rebuilt = unflatten_bitvec_to_datatype(&payload, target_sort)?;
        ctx.declare_datatype_sort_if_needed(target_sort);
        return Some(rebuilt);
    }
    ctx.coerce_value_to_sort(payload, target_sort, signed)
}

fn inline_nonzero_new_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    callee_path: &str,
    translated_args: &[Expr],
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    if translated_args.len() != 1 {
        return None;
    }
    let constructor = detect_nonzero_constructor(callee_path)?;

    let output_ty =
        ctx.resolve_body_ty(func.ty(caller_locals).ok()?.kind().fn_sig()?.skip_binder().output());
    let target_sort = ChcCtx::translate_ty(output_ty)?;
    let payload = translated_args.first()?.clone();

    if constructor == NonZeroConstructor::NewUnchecked {
        if target_sort.is_datatype() {
            let rebuilt = unflatten_bitvec_to_datatype(&payload, &target_sort)?;
            ctx.declare_datatype_sort_if_needed(&target_sort);
            return Some(rebuilt);
        }
        return ctx.coerce_value_to_sort(payload, &target_sort, ty_signedness(output_ty)?);
    }

    if !target_sort.is_datatype() {
        return None;
    }
    let is_some = expr_is_nonzero(&payload)?;
    let payload_signed = option_payload_signedness(output_ty);
    let payload_sort =
        crate::codegen_ay::chc::stubs_option_helpers::option_value_sort(&target_sort)?;
    let payload = coerce_nonzero_payload_to_sort(ctx, payload, &payload_sort, payload_signed)?;
    let some_expr = ctx.make_some_expr_for_option(payload, &target_sort)?;
    let none_expr = ctx.make_none_expr_for_option(&target_sort)?;
    ctx.declare_datatype_sort_if_needed(&target_sort);
    Some(Expr::ite(is_some, some_expr, none_expr))
}

fn inline_ptr_wrapping_byte_expr(stub: StubKind, translated_args: &[Expr]) -> Option<Expr> {
    let is_sub = matches!(stub, StubKind::PtrWrappingByteSub);
    let is_byte_offset = matches!(stub, StubKind::PtrWrappingByteOffset);
    if !matches!(
        stub,
        StubKind::PtrWrappingByteOffset
            | StubKind::PtrWrappingByteAdd
            | StubKind::PtrWrappingByteSub
    ) || translated_args.len() != 2
    {
        return None;
    }

    let ptr = coerce_inline_ptr_width(translated_args.first()?.clone(), SignExtension::ZeroExtend)?;
    let count_ext =
        if is_byte_offset { SignExtension::SignExtend } else { SignExtension::ZeroExtend };
    let byte_count = coerce_inline_ptr_width(translated_args.get(1)?.clone(), count_ext)?;

    // Split-add keeps the obj_id lane intact so the eventual deref's heap
    // bounds check still sees a foldable obj_id (whole-width bvadd smears a
    // symbolic count across the id bits and the bounds clause gets dropped).
    // Wrapping pointer arithmetic is defined even out of bounds, so no UB is
    // emitted here; an OOB deref of the result is caught by heap_access_checks.
    // Lane wrap at ±4GiB folds into the offset lane (obj_size is bv32, so
    // affected allocations are outside the model envelope anyway).
    Some(if is_sub {
        step_split_pointer_sub(ptr, byte_count).result
    } else {
        step_split_pointer(ptr, byte_count).result
    })
}

fn coerce_inline_ptr_width(expr: Expr, extension: SignExtension) -> Option<Expr> {
    if expr.sort().is_int() {
        Some(expr.int2bv(POINTER_WIDTH))
    } else if expr.sort().is_bitvec() {
        Some(coerce_bitvec_width(expr, POINTER_WIDTH, extension))
    } else {
        None
    }
}

fn inline_runtime_ptr_ge_expr(translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 2 {
        return None;
    }
    let lhs = translated_args.first()?.clone();
    let rhs = translated_args.get(1)?.clone();
    if lhs.sort() != rhs.sort() || !lhs.sort().is_bitvec() {
        return None;
    }
    Some(lhs.bvuge(rhs))
}

fn inline_option_result_predicate_expr<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<Expr> {
    if translated_args.len() != 1 {
        return None;
    }

    let stub = ctx.stub_registry.lookup(callee_path)?;
    let receiver = translated_args.first()?.clone();
    let predicate = if receiver.sort().is_bool() {
        receiver
    } else if let Some(width) = receiver.sort().bitvec_width() {
        receiver.eq(Expr::bitvec_const(0u64, width)).not()
    } else {
        // Part of #4075: bail when the receiver DT is clearly not an Option/Result.
        // The inline walker may have peeled the Option envelope (e.g., Option<Pin<Box<dyn Future>>>
        // becomes Pin<Box<...>> — a 1-ctor struct DT). Calling option_is_some on a non-Option DT
        // produces 21 spurious translation drops in the spawn scheduler.
        if let ay_bindings::SortInner::Datatype(dt) = receiver.sort().inner() {
            let is_option_shaped = dt.constructors.len() == 2
                || (dt.constructors.len() == 1
                    && dt.constructors[0].fields.first().is_some_and(|f| f.sort.is_bool()));
            if !is_option_shaped {
                return None;
            }
        }
        match stub {
            StubKind::OptionIsSome | StubKind::OptionIsNone => ctx.option_is_some(receiver),
            StubKind::ResultIsOk | StubKind::ResultIsErr => {
                ctx.result_variant_tester(receiver, "Ok", "result_is_ok")
            }
            _ => return None,
        }
    };

    Some(match stub {
        StubKind::OptionIsSome | StubKind::ResultIsOk => predicate,
        StubKind::OptionIsNone | StubKind::ResultIsErr => predicate.not(),
        _ => return None,
    })
}

fn inline_option_unwrap_expr<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<Expr> {
    let receiver = translated_args.first()?.clone();
    match ctx.stub_registry.lookup(callee_path)? {
        StubKind::OptionUnwrap | StubKind::OptionExpect | StubKind::OptionUnwrapUnchecked => {
            if receiver.sort().is_bitvec() || receiver.sort().is_bool() || receiver.sort().is_int()
            {
                return Some(receiver);
            }
            let is_some = ctx.option_is_some(receiver.clone());
            let inner = ctx.option_unwrap_value_on_some_path(receiver)?;
            let fallback = super::declare_pending_var(
                super::chc_fresh_name("__assert_fail_inline_option_unwrap"),
                inner.sort().clone(),
            );
            Some(Expr::ite(is_some, inner, fallback))
        }
        _ => None,
    }
}

fn inline_option_unwrap_or_expr<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<Expr> {
    if translated_args.len() != 2 {
        return None;
    }
    let receiver = translated_args.first()?.clone();
    match ctx.stub_registry.lookup(callee_path)? {
        StubKind::OptionUnwrapOr => {
            if !receiver.sort().is_datatype() {
                return Some(receiver);
            }
            let default = translated_args.get(1)?.clone();
            let is_some = ctx.option_is_some(receiver.clone());
            let inner = ctx.option_unwrap_value_on_some_path(receiver)?;
            Some(Expr::ite(is_some, inner, default))
        }
        _ => None,
    }
}

/// Inline `PartialEq::eq` / `PartialEq::ne` for Datatype-sorted types.
///
/// Handles Option, Result, tuples, and any other single/multi-constructor
/// Datatype where both operands share the same AY sort. The sort guard at
/// the end ensures only bool/int/bitvec/Datatype-sorted args are accepted.
///
/// Part of #4070: widened from Option/Result-only to cover tuple CAS results
/// that exceed the MIR pre-inlining budget.
fn inline_datatype_partial_eq_expr(callee_path: &str, translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 2 || !callee_path.contains("cmp::PartialEq") {
        return None;
    }
    let is_eq = match callee_path.rsplit("::").next()? {
        "eq" => true,
        "ne" => false,
        _ => return None,
    };
    let lhs = translated_args.first()?.clone();
    let rhs = translated_args.get(1)?.clone();
    let (lhs, rhs) = ChcCtx::coerce_eq_operands(lhs, rhs, false);
    if lhs.sort() != rhs.sort() {
        return None;
    }
    let sort = lhs.sort();
    if !(sort.is_bool() || sort.is_int() || sort.is_bitvec() || sort.datatype_name().is_some()) {
        return None;
    }
    ChcCtx::compute_partial_eq(lhs, rhs, false, is_eq)
}

fn inline_char_from_u32_unchecked_expr(
    callee_path: &str,
    translated_args: &[Expr],
) -> Option<Expr> {
    if !callee_path.ends_with("::from_u32_unchecked") || translated_args.len() != 1 {
        return None;
    }
    let value = translated_args.first()?.clone();
    if value.sort().bitvec_width() == Some(32) { Some(value) } else { None }
}

/// CHAR_FROM_U32_OPTION_MODEL: model the CHECKED `char::from_u32(x)` as an
/// `Option<char>` whose Some-discriminant is exactly the Unicode scalar-value
/// predicate (`x <= 0xD7FF || 0xE000..=0x10FFFF`), with the payload carrying `x`
/// verbatim. Without this, `char::from_u32(x)` is over-approximated (havoc), so
/// `char::from_u32(x).is_some()` inside `kani::any_where(|v| ...)` never
/// constrains `x` to the valid-char range — downstream `char` validity checks
/// then read an unconstrained value (spurious CTREX / chc_translation_drop).
///
/// Mirrors `inline_nonzero_new_expr`'s `New` arm exactly, swapping the non-zero
/// test for the shared `char_validity_predicate`. SOUND: the Some branch is
/// reachable iff `x` is a valid Unicode scalar value, so the model neither
/// over- nor under-constrains — it is bit-faithful to the real `from_u32`.
fn inline_char_from_u32_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    callee_path: &str,
    translated_args: &[Expr],
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    // `ends_with("::from_u32")` already excludes `::from_u32_unchecked`.
    if !callee_path.ends_with("::from_u32")
        || !callee_path.contains("char")
        || translated_args.len() != 1
    {
        return None;
    }
    let output_ty =
        ctx.resolve_body_ty(func.ty(caller_locals).ok()?.kind().fn_sig()?.skip_binder().output());
    let target_sort = ChcCtx::translate_ty(output_ty)?;
    // `char::from_u32` returns `Option<char>`, a 2-ctor datatype. Bail otherwise
    // so a differently-shaped `from_u32` (were one to exist) is left to normal
    // dispatch rather than mis-modeled here.
    if !target_sort.is_datatype() {
        return None;
    }
    let payload = translated_args.first()?.clone();
    let is_some = ChcCtx::char_validity_predicate(payload.clone())?;
    let payload_signed = option_payload_signedness(output_ty);
    let payload_sort =
        crate::codegen_ay::chc::stubs_option_helpers::option_value_sort(&target_sort)?;
    let payload = coerce_nonzero_payload_to_sort(ctx, payload, &payload_sort, payload_signed)?;
    let some_expr = ctx.make_some_expr_for_option(payload, &target_sort)?;
    let none_expr = ctx.make_none_expr_for_option(&target_sort)?;
    ctx.declare_datatype_sort_if_needed(&target_sort);
    Some(Expr::ite(is_some, some_expr, none_expr))
}

struct IteratorEqParts {
    ptr: Option<Expr>,
    data: Expr,
    len: Expr,
    pos: Expr,
}

fn inline_chars_iterator_eq_expr(callee_path: &str, translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 2
        || !callee_path.ends_with("::eq")
        || !callee_path.contains("Iterator")
        || callee_path.contains("PartialEq")
    {
        return None;
    }

    iterator_eq_condition(translated_args.first()?, translated_args.get(1)?)
}

fn inline_iter_compare_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    callee_path: &str,
    translated_args: &[Expr],
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    if !callee_path.ends_with("iter_compare") || translated_args.len() < 2 {
        return None;
    }
    debug!(
        args_len = translated_args.len(),
        arg0_sort = translated_args.first().map(|arg| format!("{}", arg.sort())),
        arg1_sort = translated_args.get(1).map(|arg| format!("{}", arg.sort())),
        "inline iter_compare: attempting iterator-state fast path"
    );
    let Some(state_eq) = iterator_eq_condition(translated_args.first()?, translated_args.get(1)?)
    else {
        debug!("inline iter_compare: iterator-state extraction failed");
        return None;
    };
    let output_ty =
        ctx.resolve_body_ty(func.ty(caller_locals).ok()?.kind().fn_sig()?.skip_binder().output());
    let Some(target_sort) = ChcCtx::translate_ty(output_ty) else {
        debug!("inline iter_compare: output sort translation failed");
        return None;
    };
    let result = build_iter_compare_control_flow_result(&target_sort, state_eq);
    if result.is_none() {
        debug!(sort = %target_sort, "inline iter_compare: ControlFlow result construction failed");
    }
    result
}

fn iterator_eq_condition(lhs_expr: &Expr, rhs_expr: &Expr) -> Option<Expr> {
    let lhs = iterator_eq_parts(lhs_expr)?;
    let rhs = iterator_eq_parts(rhs_expr)?;
    let storage_eq = match (lhs.ptr, rhs.ptr) {
        (Some(lhs_ptr), Some(rhs_ptr)) if lhs_ptr.sort() == rhs_ptr.sort() => lhs_ptr.eq(rhs_ptr),
        _ => lhs.data.eq(rhs.data),
    };
    Expr::try_and_many(vec![storage_eq, lhs.len.eq(rhs.len), lhs.pos.eq(rhs.pos)]).ok()
}

fn build_iter_compare_control_flow_result(target_sort: &Sort, state_eq: Expr) -> Option<Expr> {
    let dt = target_sort.datatype_sort()?;
    let continue_ctor = dt.constructors.iter().find(|ctor| ctor.name.contains("Continue"))?;
    let break_ctor = dt.constructors.iter().find(|ctor| ctor.name.contains("Break"))?;
    let ordering_sort = continue_ctor.fields.first()?.sort.clone();
    let equal = if let Some(ordering_dt) = ordering_sort.datatype_sort() {
        let equal_ctor =
            ordering_dt.constructors.iter().find(|ctor| ctor.name.contains("Equal"))?;
        Expr::datatype_constructor(
            &*ordering_dt.name,
            &*equal_ctor.name,
            Vec::new(),
            ordering_sort.clone(),
        )
    } else if let Some(width) = ordering_sort.bitvec_width() {
        Expr::bitvec_const(0u64, width)
    } else {
        return None;
    };
    let continue_equal = Expr::datatype_constructor(
        &*dt.name,
        &*continue_ctor.name,
        vec![equal],
        target_sort.clone(),
    );
    let break_payload_sort = break_ctor.fields.first()?.sort.clone();
    let break_payload =
        declare_pending_var(chc_fresh_name("__iter_compare_break"), break_payload_sort);
    let break_expr = Expr::datatype_constructor(
        &*dt.name,
        &*break_ctor.name,
        vec![break_payload],
        target_sort.clone(),
    );
    Expr::try_ite(state_eq, continue_equal, break_expr).ok()
}

fn iterator_eq_parts(expr: &Expr) -> Option<IteratorEqParts> {
    let iter = iterator_eq_carrier(expr.clone(), 0)?;
    let dt_name = iter.sort().datatype_name()?.to_owned();
    let pos = iter.clone().field_select(&dt_name, "fld_pos", Sort::bitvec(POINTER_WIDTH));
    let vec_sort = ChcCtx::get_dt_field_sort(&iter, "fld_vec")?;
    let vec = iter.clone().field_select(&dt_name, "fld_vec", vec_sort);
    let vec_dt_name = vec.sort().datatype_name()?.to_owned();
    let ptr = ChcCtx::get_dt_field_sort(&vec, "fld_ptr")
        .map(|ptr_sort| vec.clone().field_select(&vec_dt_name, "fld_ptr", ptr_sort));
    let len = vec.clone().field_select(&vec_dt_name, "fld_len", Sort::bitvec(POINTER_WIDTH));
    let data_sort = ChcCtx::get_dt_field_sort(&vec, "fld_data")?;
    let data = vec.field_select(&vec_dt_name, "fld_data", data_sort);
    Some(IteratorEqParts { ptr, data, len, pos })
}

fn iterator_eq_carrier(expr: Expr, depth: usize) -> Option<Expr> {
    if ChcCtx::get_dt_field_sort(&expr, "fld_pos").is_some()
        && ChcCtx::get_dt_field_sort(&expr, "fld_vec").is_some()
    {
        return Some(expr);
    }
    if depth >= 4 {
        return None;
    }
    let sort = expr.sort().clone();
    let dt = sort.datatype_sort()?;
    if dt.constructors.len() != 1 {
        return None;
    }
    let ctor = dt.constructors.first()?;
    for field in &ctor.fields {
        if !field.sort.is_datatype() {
            continue;
        }
        let child = expr.clone().field_select(&dt.name, &field.name, field.sort.clone());
        if let Some(carrier) = iterator_eq_carrier(child, depth + 1) {
            return Some(carrier);
        }
    }
    None
}

fn inline_primitive_cmp_expr(
    callee_path: &str,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    let method = ChcCtx::primitive_cmp_method(callee_path)?;
    if first_arg.is_some_and(|arg| operand_is_raw_pointer_like(arg, caller_locals)) {
        return inline_raw_pointer_cmp_expr(method, translated_args);
    }
    match method {
        "eq" | "ne" => inline_plain_eq_expr(method == "eq", translated_args),
        // Part of #4203: Handle ordering comparisons for BV types inside
        // inlined function bodies. Without this, nested calls to
        // lt/le/gt/ge/cmp/partial_cmp/min/max/clamp inside fn_inline'd
        // bodies cause the inline walker to bail, falling through to
        // call_dispatch_fallback and producing false CTREX.
        "lt" | "le" | "gt" | "ge" => {
            inline_bv_ord_pred(method, translated_args, first_arg, caller_locals, callee_path)
        }
        "cmp" | "partial_cmp" => {
            inline_bv_cmp_expr(translated_args, first_arg, caller_locals, callee_path)
        }
        "min" | "max" => {
            inline_bv_min_max_expr(method, translated_args, first_arg, caller_locals, callee_path)
        }
        "clamp" => inline_bv_clamp_expr(translated_args, first_arg, caller_locals, callee_path),
        _ => None,
    }
}

/// Part of #4203: Ordering predicate for inline walker.
///
/// Produces a Bool expression for `lt`/`le`/`gt`/`ge` on bitvec or Int operands,
/// using signed or unsigned comparison based on the operand type.
fn inline_bv_ord_pred(
    method: &str,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
    callee_path: &str,
) -> Option<Expr> {
    if translated_args.len() < 2 {
        return None;
    }
    let lhs = translated_args[0].clone();
    let rhs = translated_args[1].clone();
    // Int-sorted operands (e.g., char comparisons): use SMT int_lt/le/gt/ge.
    if lhs.sort().is_int() && rhs.sort().is_int() {
        return Some(match method {
            "lt" => lhs.int_lt(rhs),
            "le" => lhs.int_le(rhs),
            "gt" => lhs.int_gt(rhs),
            "ge" => lhs.int_ge(rhs),
            _ => return None,
        });
    }
    if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
        return None;
    }
    // Widen to common width if needed.
    let (lhs, rhs) = coerce_bv_pair(lhs, rhs, first_arg, caller_locals, callee_path)?;
    let is_signed =
        infer_inline_arith_signedness(first_arg, caller_locals, callee_path).unwrap_or(false);
    Some(match method {
        "lt" => {
            if is_signed {
                lhs.bvslt(rhs)
            } else {
                lhs.bvult(rhs)
            }
        }
        "le" => {
            if is_signed {
                lhs.bvsle(rhs)
            } else {
                lhs.bvule(rhs)
            }
        }
        "gt" => {
            if is_signed {
                lhs.bvsgt(rhs)
            } else {
                lhs.bvugt(rhs)
            }
        }
        "ge" => {
            if is_signed {
                lhs.bvsge(rhs)
            } else {
                lhs.bvuge(rhs)
            }
        }
        _ => return None,
    })
}

/// Part of #4203: `cmp`/`partial_cmp` for inline walker.
///
/// Produces a BV32 expression encoding `Ordering` (-1=Less, 0=Equal, 1=Greater).
/// Handles both BV-sorted and Int-sorted operands. `partial_cmp` on primitive
/// types always returns `Some(Ordering)`, and the caller (inline walker) consumes
/// the inner Ordering value, so the encoding is identical to `cmp`.
fn inline_bv_cmp_expr(
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
    callee_path: &str,
) -> Option<Expr> {
    if translated_args.len() < 2 {
        return None;
    }
    let lhs = translated_args[0].clone();
    let rhs = translated_args[1].clone();
    // Int-sorted operands: use SMT int_lt for the ITE chain.
    if lhs.sort().is_int() && rhs.sort().is_int() {
        let lt_expr = lhs.clone().int_lt(rhs.clone());
        let eq_expr = lhs.eq(rhs);
        return Some(Expr::ite(
            lt_expr,
            Expr::bitvec_const(-1i128, 32),
            Expr::ite(eq_expr, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
        ));
    }
    if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
        return None;
    }
    let (lhs, rhs) = coerce_bv_pair(lhs, rhs, first_arg, caller_locals, callee_path)?;
    let is_signed =
        infer_inline_arith_signedness(first_arg, caller_locals, callee_path).unwrap_or(false);
    let lt_expr =
        if is_signed { lhs.clone().bvslt(rhs.clone()) } else { lhs.clone().bvult(rhs.clone()) };
    let eq_expr = lhs.eq(rhs);
    Some(Expr::ite(
        lt_expr,
        Expr::bitvec_const(-1i128, 32),
        Expr::ite(eq_expr, Expr::bitvec_const(0, 32), Expr::bitvec_const(1, 32)),
    ))
}

/// Part of #4203: `min`/`max` for inline walker.
fn inline_bv_min_max_expr(
    method: &str,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
    callee_path: &str,
) -> Option<Expr> {
    if translated_args.len() < 2 {
        return None;
    }
    let lhs = translated_args[0].clone();
    let rhs = translated_args[1].clone();
    // Int-sorted operands.
    if lhs.sort().is_int() && rhs.sort().is_int() {
        let keep_lhs = if method == "min" {
            lhs.clone().int_le(rhs.clone())
        } else {
            lhs.clone().int_ge(rhs.clone())
        };
        return Some(Expr::ite(keep_lhs, lhs, rhs));
    }
    if !lhs.sort().is_bitvec() || !rhs.sort().is_bitvec() {
        return None;
    }
    let (lhs, rhs) = coerce_bv_pair(lhs, rhs, first_arg, caller_locals, callee_path)?;
    let is_signed =
        infer_inline_arith_signedness(first_arg, caller_locals, callee_path).unwrap_or(false);
    let keep_lhs = if method == "min" {
        if is_signed { lhs.clone().bvsle(rhs.clone()) } else { lhs.clone().bvule(rhs.clone()) }
    } else {
        if is_signed { lhs.clone().bvsge(rhs.clone()) } else { lhs.clone().bvuge(rhs.clone()) }
    };
    Some(Expr::ite(keep_lhs, lhs, rhs))
}

/// Part of #4203: BV `clamp` for inline walker.
fn inline_bv_clamp_expr(
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
    callee_path: &str,
) -> Option<Expr> {
    if translated_args.len() < 3 {
        return None;
    }
    let val = translated_args[0].clone();
    let min_bound = translated_args[1].clone();
    let max_bound = translated_args[2].clone();
    if !val.sort().is_bitvec() || !min_bound.sort().is_bitvec() || !max_bound.sort().is_bitvec() {
        return None;
    }
    // All three must have compatible BV widths.
    let (val, min_bound) = coerce_bv_pair(val, min_bound, first_arg, caller_locals, callee_path)?;
    let (val, max_bound) = coerce_bv_pair(val, max_bound, first_arg, caller_locals, callee_path)?;
    let (min_bound, max_bound) =
        coerce_bv_pair(min_bound, max_bound, first_arg, caller_locals, callee_path)?;
    let is_signed =
        infer_inline_arith_signedness(first_arg, caller_locals, callee_path).unwrap_or(false);
    let range_ok = if is_signed {
        min_bound.clone().bvsle(max_bound.clone())
    } else {
        min_bound.clone().bvule(max_bound.clone())
    };
    let lt_min = if is_signed {
        val.clone().bvslt(min_bound.clone())
    } else {
        val.clone().bvult(min_bound.clone())
    };
    let gt_max = if is_signed {
        val.clone().bvsgt(max_bound.clone())
    } else {
        val.clone().bvugt(max_bound.clone())
    };
    let clamped = Expr::ite(lt_min, min_bound, Expr::ite(gt_max, max_bound, val.clone()));
    // If min > max the clamp contract is violated. Use a fresh symbolic as
    // the panic placeholder (mirrors the raw-pointer clamp in
    // inline_known_calls_raw_ptr.rs).
    let fallback = super::declare_pending_var(
        super::chc_fresh_name("__assert_fail_inline_bv_clamp"),
        val.sort().clone(),
    );
    Some(Expr::ite(range_ok, clamped, fallback))
}

/// Coerce a pair of BV expressions to a common width via zero- or sign-extend.
fn coerce_bv_pair(
    lhs: Expr,
    rhs: Expr,
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
    callee_path: &str,
) -> Option<(Expr, Expr)> {
    let lw = lhs.sort().bitvec_width()?;
    let rw = rhs.sort().bitvec_width()?;
    if lw == rw {
        return Some((lhs, rhs));
    }
    let target = lw.max(rw);
    let is_signed =
        infer_inline_arith_signedness(first_arg, caller_locals, callee_path).unwrap_or(false);
    let lhs = if lw < target {
        if is_signed { lhs.sign_extend(target - lw) } else { lhs.zero_extend(target - lw) }
    } else {
        lhs
    };
    let rhs = if rw < target {
        if is_signed { rhs.sign_extend(target - rw) } else { rhs.zero_extend(target - rw) }
    } else {
        rhs
    };
    Some((lhs, rhs))
}

/// Part of #4067: Mutex/RwLock operations are identity in single-threaded
/// verification. Mutex<T> and RwLock<T> are translated as T (transparent
/// wrappers), and MutexGuard/RwLockReadGuard/RwLockWriteGuard deref to T.
///
/// Handled methods:
/// - `::new(value)` → identity (wrapping)
/// - `::lock(&self)` / `::read(&self)` / `::write(&self)` → identity (always-Ok in single-thread)
/// - `::into_inner(self)` → identity (unwrapping)
/// - `::get_mut(&mut self)` → identity
fn inline_mutex_new_expr(callee_path: &str, translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 1 {
        return None;
    }
    let is_sync_lock = callee_path.contains("sync::Mutex") || callee_path.contains("sync::RwLock");
    if !is_sync_lock {
        return None;
    }
    let method = callee_path.rsplit("::").next()?;
    match method {
        "new" | "into_inner" | "get_mut" => Some(translated_args[0].clone()),
        // Part of #4067 D2: lock/read/write are identity in single-threaded
        // verification. PoisonError<T> is transparent, so Result<T,T> same-sort
        // flattening makes recover_enum_payload_from_raw_value produce (true, T).
        "lock" | "read" | "write" => Some(translated_args[0].clone()),
        _ => None,
    }
}

fn inline_pin_identity_expr(callee_path: &str, translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 1 {
        return None;
    }
    if !callee_path.contains("pin::Pin") {
        return None;
    }
    let method = callee_path.rsplit("::").next()?;
    matches!(method, "as_mut" | "new_unchecked").then(|| translated_args[0].clone())
}

fn inline_ub_checks_expr(callee_path: &str, translated_args: &[Expr]) -> Option<Expr> {
    if !translated_args.is_empty() {
        return None;
    }
    let method = callee_path.rsplit("::").next()?;
    match method {
        // Verification keeps UB checks enabled so std/core precondition guards
        // remain reachable instead of leaving their Bool destinations nondet.
        "check_language_ub" | "check_library_ub" => Some(Expr::bool_const(true)),
        "ub_checks" if callee_path.contains("intrinsics::") => Some(Expr::bool_const(true)),
        _ => None,
    }
}

/// Part of #3875: Inline `SpecArrayEq::spec_eq` for fixed-size scalar arrays.
///
/// `spec_eq(&[T; N], &[U; N]) -> bool` delegates to slice comparison which has
/// a loop the inline walker cannot handle. Route the semantics through the
/// shared helper so both flat-BV and Array-sorted layouts use the same
/// fixed-array contract.
fn inline_spec_array_eq_expr(
    callee_path: &str,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    if translated_args.len() != 2 {
        return None;
    }
    if !callee_path.contains("SpecArrayEq") || !callee_path.contains("spec_eq") {
        return None;
    }
    let lhs = &translated_args[0];
    let rhs = &translated_args[1];
    let len = recover_spec_array_eq_len(Some(callee_path), first_arg, caller_locals);
    build_spec_array_eq(lhs, rhs, len)
}

/// Part of #4101: Inline `std::intrinsics::raw_eq` for the inline walker.
///
/// `raw_eq<T>(a: &T, b: &T) -> bool` compares two values by byte representation.
/// Inside fn_inline'd bodies (e.g., `PartialEq::eq` for `[u32; 4]`), the main
/// dispatch chain's raw_eq handler is unreachable — only inline_known_calls
/// can intercept nested calls. Delegates to `build_spec_array_eq` which handles
/// Array-sorted operands (element-wise lane equality) and BV/DT/bool operands
/// (direct SMT equality).
fn inline_raw_eq_expr(
    callee_path: &str,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    if translated_args.len() != 2 {
        return None;
    }
    if !(callee_path.contains("intrinsics::") && callee_path.contains("raw_eq")) {
        return None;
    }
    let lhs = &translated_args[0];
    let rhs = &translated_args[1];
    // Recover the array length from the operand type (raw_eq<[T; N]> args are &[T; N]).
    let len = recover_spec_array_eq_len(None, first_arg, caller_locals);
    build_spec_array_eq(lhs, rhs, len)
}

fn inline_vec_len_expr(translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 1 {
        return None;
    }
    let receiver = translated_args.first()?.clone();
    let (_, len, _, _) = ChcVecFields::extract_without_name(receiver)?;
    Some(len)
}

/// Part of #4057: Vec::is_empty inline fast-path.
/// Semantics: `self.len() == 0` — extract fld_len from Vec DT, compare to zero.
fn inline_vec_is_empty_expr(translated_args: &[Expr]) -> Option<Expr> {
    if translated_args.len() != 1 {
        return None;
    }
    let receiver = translated_args.first()?.clone();
    let (_, len, _, _) = ChcVecFields::extract_without_name(receiver)?;
    Some(len.eq(Expr::bitvec_const(0u64, POINTER_WIDTH)))
}

#[cfg(test)]
#[path = "inline_known_calls_option_tests.rs"]
mod option_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen_ay::chc::call::inline_body::extract_inline_assert_guard;
    use ay_bindings::Expr;

    #[test]
    fn test_inline_ub_checks_expr_returns_true_for_check_language_ub() {
        let expr = inline_ub_checks_expr("core::ub_checks::check_language_ub", &[])
            .expect("check_language_ub should inline");
        assert!(expr.sort().is_bool(), "UB checks should return Bool");
        assert_eq!(expr.to_string(), "true");
    }

    #[test]
    fn test_inline_ub_checks_expr_returns_true_for_intrinsics_ub_checks() {
        let expr = inline_ub_checks_expr("core::intrinsics::ub_checks", &[]).expect("ub_checks");
        assert!(expr.sort().is_bool(), "ub_checks should return Bool");
        assert_eq!(expr.to_string(), "true");
    }

    #[test]
    fn test_inline_ub_checks_expr_rejects_non_nullary_calls() {
        let expr = Expr::bitvec_const(1u64, 64);
        assert!(inline_ub_checks_expr("core::ub_checks::check_language_ub", &[expr]).is_none());
    }

    #[test]
    fn test_inline_raw_pointer_clamp_uses_assert_guard_fallback() {
        let x = Expr::bitvec_const(5u64, POINTER_WIDTH);
        let lo = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let hi = Expr::bitvec_const(9u64, POINTER_WIDTH);
        let expr = inline_raw_pointer_cmp_expr("clamp", &[x, lo, hi])
            .expect("raw pointer clamp fast path");
        let expr_text = expr.to_string();
        let guard = extract_inline_assert_guard(&expr)
            .expect("clamp fallback should propagate assert guard");

        assert!(
            expr_text.contains("__assert_fail_inline_raw_ptr_clamp"),
            "raw pointer clamp should use inline-assert fallback naming: {expr_text}"
        );
        assert!(
            !guard.to_string().is_empty(),
            "extracted clamp guard should be a concrete expression"
        );
    }

    #[test]
    fn test_inline_datatype_partial_eq_coerces_equality_operand_sorts() {
        let expr = inline_datatype_partial_eq_expr(
            "core::cmp::PartialEq::eq",
            &[Expr::bool_const(true), Expr::bitvec_const(1u64, 8)],
        )
        .expect("PartialEq::eq should coerce bool/BV equality operands");

        assert!(expr.sort().is_bool(), "inlined PartialEq must return Bool");
    }

    #[test]
    fn test_inline_char_from_u32_unchecked_is_identity_for_bv32() {
        let value = Expr::bitvec_const(0x68u64, 32);
        let expr = inline_char_from_u32_unchecked_expr(
            "std::char::convert::from_u32_unchecked",
            std::slice::from_ref(&value),
        )
        .expect("from_u32_unchecked should inline as char BV32 identity");

        assert_eq!(expr, value);
    }

    #[test]
    fn test_inline_chars_iterator_eq_uses_remaining_iterator_state() {
        let vec_sort = crate::codegen_ay::test_fixtures::vec_sort(Sort::bitvec(8));
        let iter_sort = crate::codegen_ay::names::struct_sort(
            "SliceIter_bv8",
            [("fld_vec", vec_sort.clone()), ("fld_pos", Sort::bitvec(64))],
        );
        let chars_sort =
            crate::codegen_ay::names::struct_sort("Chars_bv8", [("fld_iter", iter_sort.clone())]);
        let data = Expr::var("bytes", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
        let vec = Expr::datatype_constructor(
            "Vec",
            "Vec_mk",
            vec![
                Expr::bitvec_const(0u64, 64),
                Expr::bitvec_const(1u64, 64),
                Expr::bitvec_const(1u64, 64),
                data,
            ],
            vec_sort,
        );
        let iter = Expr::datatype_constructor(
            "SliceIter_bv8",
            "SliceIter_bv8_mk",
            vec![vec, Expr::bitvec_const(0u64, 64)],
            iter_sort,
        );
        let chars = Expr::datatype_constructor("Chars_bv8", "Chars_bv8_mk", vec![iter], chars_sort);

        let expr = inline_chars_iterator_eq_expr(
            "core::iter::traits::iterator::Iterator::eq",
            &[chars.clone(), chars],
        )
        .expect("Iterator::eq over Chars should inline");

        assert!(expr.sort().is_bool(), "iterator eq result must be Bool");
        let expr_text = expr.to_string();
        // At ay 232304e1, try_field_select constant-folds selector-over-constructor
        // for single-ctor datatypes, so the fld_ptr/fld_data selector-name text this
        // test used to key on is folded away. Pin the structural result instead:
        // pointer identity + remaining iterator state, folded to constants, with NO
        // reference to the pruned backing array `bytes` (which would appear only if
        // the encoding regressed to the data-array fallback).
        assert_eq!(
            expr_text,
            "(and (= #x0000000000000000 #x0000000000000000) (= #x0000000000000001 #x0000000000000001) (= #x0000000000000000 #x0000000000000000))",
            "chars-iterator eq must fold to remaining-state identity ptr(0)==ptr(0) ^ len(1)==len(1) ^ pos(0)==pos(0), with no dependence on the pruned backing array `bytes`: {expr_text}"
        );
    }

    #[test]
    fn test_build_iter_compare_result_continues_with_equal_ordering() {
        let no_fields: Vec<(&str, Sort)> = Vec::new();
        let ordering_sort = Sort::enum_type(
            "OrderingProof",
            vec![("Less", no_fields.clone()), ("Equal", no_fields.clone()), ("Greater", no_fields)],
        );
        let control_flow_sort = Sort::enum_type(
            "ControlFlowProof",
            vec![
                ("Break", vec![("value", Sort::bool())]),
                ("Continue", vec![("value", ordering_sort)]),
            ],
        );

        let result =
            build_iter_compare_control_flow_result(&control_flow_sort, Expr::bool_const(true))
                .expect("iter_compare result should build for ControlFlow<_, Ordering>");

        assert_eq!(result.sort(), &control_flow_sort);
        assert!(result.to_string().contains("Continue"), "expected Continue branch: {result}");
        assert!(result.to_string().contains("Equal"), "expected Equal payload: {result}");
    }

    #[test]
    fn test_build_iter_compare_result_accepts_bitvec_ordering() {
        let control_flow_sort = Sort::enum_type(
            "ControlFlowBvOrderingProof",
            vec![
                ("Break", vec![("value", Sort::bool())]),
                ("Continue", vec![("value", Sort::bitvec(8))]),
            ],
        );

        let result =
            build_iter_compare_control_flow_result(&control_flow_sort, Expr::bool_const(true))
                .expect("iter_compare result should build for bitvector Ordering payload");

        assert_eq!(result.sort(), &control_flow_sort);
        assert!(result.to_string().contains("#x00"), "expected Equal as Ordering=0: {result}");
    }

    #[test]
    fn test_inline_ptr_wrapping_byte_offset_coerces_int_count_to_bv64() {
        let ptr = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);
        let count = Expr::int_const(7);
        let expr = inline_ptr_wrapping_byte_expr(StubKind::PtrWrappingByteOffset, &[ptr, count])
            .expect("wrapping_byte_offset should inline");

        assert_eq!(expr.sort().bitvec_width(), Some(POINTER_WIDTH));
        // Fully-constant inputs fold to a literal address (split-step const fast-path).
        assert_eq!(expr, Expr::bitvec_const(0x1007u64, POINTER_WIDTH));
    }

    #[test]
    fn test_inline_ptr_wrapping_byte_sub_uses_bvsub() {
        let ptr = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);
        let count = Expr::bitvec_const(4u64, 8);
        let expr = inline_ptr_wrapping_byte_expr(StubKind::PtrWrappingByteSub, &[ptr, count])
            .expect("wrapping_byte_sub should inline");

        assert_eq!(expr.sort().bitvec_width(), Some(POINTER_WIDTH));
        // Fully-constant inputs fold to a literal address (split-step const fast-path).
        assert_eq!(expr, Expr::bitvec_const(0x0FFCu64, POINTER_WIDTH));
    }

    /// Split-add must preserve a constant obj_id lane through a symbolic count:
    /// the heap bounds check at the eventual deref requires the obj_id to fold.
    #[test]
    fn test_inline_ptr_wrapping_byte_add_preserves_const_obj_id() {
        use crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value;

        // ptr = concat(obj_id=0x42, offset=0x10), count symbolic.
        let ptr = Expr::bitvec_const(0x42u64, 32).concat(Expr::bitvec_const(0x10u64, 32));
        let count = Expr::var("sym_count", Sort::bitvec(POINTER_WIDTH));
        let expr = inline_ptr_wrapping_byte_expr(StubKind::PtrWrappingByteAdd, &[ptr, count])
            .expect("wrapping_byte_add should inline");

        let obj_id = expr.extract(63, 32);
        let (value, width) = const_bv_value(&obj_id)
            .expect("obj_id lane must const-fold after split-add with symbolic count");
        assert_eq!(width, 32);
        assert_eq!(value, num_bigint::BigInt::from(0x42u32));
    }

    #[test]
    fn test_inline_exact_math_call_expr_handles_method_abs() {
        let neg = Expr::bitvec_const(0xC000_0000u64, 32);
        let abs = inline_exact_math_call("core::f32::math::abs", &[neg])
            .expect("abs method should inline via exact math fast path");
        let expected =
            Expr::bitvec_const(0xC000_0000u64, 32).bvand(Expr::bitvec_const(0x7FFF_FFFFu64, 32));
        assert_eq!(abs, expected);
    }

    #[test]
    fn test_inline_exact_math_call_expr_handles_intrinsic_copysign() {
        let mag = Expr::bitvec_const(0x4040_0000u64, 32);
        let sign = Expr::bitvec_const(0xBF80_0000u64, 32);
        let copied = inline_exact_math_call("core::intrinsics::copysignf32", &[mag, sign])
            .expect("copysign intrinsic should inline via exact math fast path");
        let expected = Expr::bitvec_const(0x4040_0000u64, 32)
            .bvand(Expr::bitvec_const(0x7FFF_FFFFu64, 32))
            .bvor(
                Expr::bitvec_const(0xBF80_0000u64, 32)
                    .bvand(Expr::bitvec_const(0x8000_0000u64, 32)),
            );
        assert_eq!(copied, expected);
    }

    #[test]
    fn test_inline_pin_identity_expr_returns_receiver_for_as_mut() {
        let arg = Expr::bitvec_const(0x1234u64, 64);
        let inlined =
            inline_pin_identity_expr("std::pin::Pin::<Ptr>::as_mut", std::slice::from_ref(&arg))
                .expect("Pin::as_mut should inline as identity");
        assert_eq!(inlined, arg);
    }

    #[test]
    fn test_inline_pin_identity_expr_returns_receiver_for_new_unchecked() {
        let arg = Expr::bitvec_const(0x1234u64, 64);
        let inlined = inline_pin_identity_expr(
            "std::pin::Pin::<Ptr>::new_unchecked",
            std::slice::from_ref(&arg),
        )
        .expect("Pin::new_unchecked should inline as identity");
        assert_eq!(inlined, arg);
    }

    #[test]
    fn test_inline_wrapping_arith_expr_wrapping_add() {
        let a = Expr::bitvec_const(3u64, 64);
        let b = Expr::bitvec_const(5u64, 64);
        let result = inline_wrapping_arith_expr(
            "core::num::<impl i64>::wrapping_add",
            &[a.clone(), b.clone()],
            None,
            &[],
        )
        .expect("wrapping_add should inline");
        assert_eq!(result, a.bvadd(b));
    }

    #[test]
    fn test_inline_saturating_arith_expr_unsigned_add() {
        let a = Expr::bitvec_const(3u64, 8);
        let b = Expr::bitvec_const(5u64, 8);
        let result = inline_saturating_arith_expr(
            "core::num::<impl u8>::saturating_add",
            &[a.clone(), b.clone()],
            None,
            &[],
        )
        .expect("saturating_add should inline");
        assert_eq!(
            result,
            Expr::ite(
                a.clone().bvadd_no_overflow_unsigned(b.clone()).not(),
                Expr::bitvec_const(255u64, 8),
                a.bvadd(b)
            )
        );
    }

    #[test]
    fn test_inline_wrapping_arith_expr_wrapping_neg() {
        let a = Expr::bitvec_const(7u64, 64);
        let result = inline_wrapping_arith_expr(
            "core::num::<impl i64>::wrapping_neg",
            std::slice::from_ref(&a),
            None,
            &[],
        )
        .expect("wrapping_neg should inline");
        assert_eq!(result, a.bvneg());
    }

    #[test]
    fn test_inline_wrapping_arith_expr_unsigned_abs() {
        let a = Expr::bitvec_const(0u64, 64);
        let result =
            inline_wrapping_arith_expr("core::num::<impl i64>::unsigned_abs", &[a], None, &[])
                .expect("unsigned_abs should inline");
        // Result is an ite expression — just check it produced something
        assert!(result.sort().is_bitvec());
    }

    /// Part of #4057: inline_vec_is_empty_expr returns Bool (len == 0).
    #[test]
    fn test_inline_vec_is_empty_expr_returns_bool() {
        use crate::codegen_ay::names::struct_sort;
        use ay_bindings::Sort;
        let data_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
        let vec_sort = struct_sort(
            "Vec_bv32",
            [
                ("fld_ptr", Sort::bitvec(64)),
                ("fld_len", Sort::bitvec(64)),
                ("fld_cap", Sort::bitvec(64)),
                ("fld_data", data_sort),
            ],
        );
        let vec_expr = Expr::var("test_vec", vec_sort);
        let result =
            inline_vec_is_empty_expr(&[vec_expr]).expect("VecIsEmpty should inline for Vec DT");
        assert!(result.sort().is_bool(), "VecIsEmpty should produce Bool sort");
    }

    /// Part of #4057: inline_vec_is_empty_expr rejects non-Vec args.
    #[test]
    fn test_inline_vec_is_empty_expr_rejects_scalar() {
        let scalar = Expr::bitvec_const(42u64, 64);
        assert!(
            inline_vec_is_empty_expr(&[scalar]).is_none(),
            "VecIsEmpty should return None for non-Vec arg"
        );
    }

    /// Part of #4067: Mutex::new is identity passthrough.
    #[test]
    fn test_inline_mutex_new_returns_identity() {
        let val = Expr::bitvec_const(42u64, 32);
        let result =
            inline_mutex_new_expr("std::sync::Mutex::<u32>::new", std::slice::from_ref(&val))
                .expect("Mutex::new should inline as identity");
        assert_eq!(result, val);
    }

    /// Part of #4067 D2: Mutex::lock is identity in single-threaded verification.
    /// PoisonError<T> is transparent, so Result<T,T> same-sort flattening
    /// makes recover_enum_payload_from_raw_value produce (true, T).
    #[test]
    fn test_inline_mutex_lock_returns_identity() {
        let val = Expr::bitvec_const(7u64, 64);
        let result =
            inline_mutex_new_expr("std::sync::Mutex::<i64>::lock", std::slice::from_ref(&val))
                .expect("Mutex::lock should inline as identity (#4067 D2)");
        assert_eq!(result, val);
    }

    /// Part of #4067 D2: RwLock::read is identity in single-threaded verification.
    #[test]
    fn test_inline_rwlock_read_returns_identity() {
        let val = Expr::bitvec_const(99u64, 16);
        let result =
            inline_mutex_new_expr("std::sync::RwLock::<u8>::read", std::slice::from_ref(&val))
                .expect("RwLock::read should inline as identity (#4067 D2)");
        assert_eq!(result, val);
    }

    /// Part of #4067: RwLock::new is identity passthrough.
    #[test]
    fn test_inline_rwlock_new_returns_identity() {
        let val = Expr::bitvec_const(99u64, 16);
        let result =
            inline_mutex_new_expr("std::sync::RwLock::<u16>::new", std::slice::from_ref(&val))
                .expect("RwLock::new should inline as identity");
        assert_eq!(result, val);
    }

    /// Part of #4067: rejects unrelated sync paths.
    #[test]
    fn test_inline_mutex_rejects_unrelated_path() {
        let val = Expr::bitvec_const(1u64, 64);
        assert!(
            inline_mutex_new_expr("std::sync::Condvar::new", std::slice::from_ref(&val)).is_none(),
            "Condvar::new should not be intercepted"
        );
    }

    /// Part of #4067: rejects multi-arg calls.
    #[test]
    fn test_inline_mutex_rejects_multi_arg() {
        let a = Expr::bitvec_const(1u64, 64);
        let b = Expr::bitvec_const(2u64, 64);
        assert!(
            inline_mutex_new_expr("std::sync::Mutex::<i64>::new", &[a, b]).is_none(),
            "Mutex::new with 2 args should be rejected"
        );
    }
}
