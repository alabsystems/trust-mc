// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Pure-call fast paths shared by inline translators.
//! Keeps exact encodings out of heavier MIR inliners to avoid inferable fallback.
//!
//! Raw pointer comparison: `inline_known_calls_raw_ptr.rs`
//! SIMD intrinsics: `inline_known_calls_simd.rs`

use crate::codegen_ay::chc::codegen_ctx::ExactVar;
use crate::codegen_ay::shared::mono_ty;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{LocalDecl, Operand};
use rustc_public::ty::{AdtKind, RigidTy, TyKind};
use tracing::debug;

use super::ChcCtx;
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
use crate::codegen_ay::chc::call::inline_known_calls_math::{
    infer_inline_arith_signedness, inline_exact_math_call, inline_saturating_arith_expr,
    inline_wrapping_arith_expr,
};
use crate::codegen_ay::chc::codegen_expr_array_eq::{
    build_spec_array_eq, recover_spec_array_eq_len,
};
use crate::codegen_ay::chc::pointer_step::step_pointer_data_keep_metadata;
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
///
/// The step is exact mod 2^64 (`step_wrapping_pointer`), as on the statement
/// path: the wrapping family is defined out of bounds, and the in-bounds lane
/// step keeps only the low 32 bits of the byte offset.
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
    let stepped = ctx.step_wrapping_address(ptr, offset_bytes, is_sub);
    debug!(elem_size, is_sub, "CHC: inline wrapping pointer arith - ptr +/- count * sizeof(T)");
    Some(stepped)
}

/// Inline pure call patterns that do not expose a simple MIR body.
pub(in crate::codegen_ay) fn inline_known_call_expr<'tcx, 'body>(
    ctx: &mut ChcCtx<'tcx, 'body>,
    func: &Operand,
    translated_args: &[Expr],
    arg_operands: &[Operand],
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    let callee_path = ctx.resolve_callee_path(func).or_else(|| ctx.resolve_fn_def_name(func))?;
    inline_known_call_expr_for_callee_path(
        ctx,
        func,
        &callee_path,
        translated_args,
        arg_operands,
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
    arg_operands: &[Operand],
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    let first_arg = arg_operands.first();
    // The comparison fast paths below compare encodings. A comparison whose
    // `==` or order is not its encodings' (a float, a reference or a
    // hand-written `PartialEq` in it; `codegen_call_cmp_semantic.rs`) is
    // refused, and the caller walks the callee's body; so is one whose
    // compared type is unknown here (a call through a fn pointer).
    if let Some(kind) = crate::codegen_ay::shared::compare_loops::comparison_call(callee_path) {
        if matches!(kind, crate::codegen_ay::shared::compare_loops::ComparisonCall::Eq { .. })
            && ctx.has_heterogeneous_sequence_elements(func, caller_locals)
        {
            return None;
        }
        let faithful = first_arg.and_then(|arg| arg.ty(caller_locals).ok()).is_some_and(|ty| {
            crate::codegen_ay::shared::compare_loops::comparison_is_faithful(
                kind,
                ctx.resolve_body_ty(ty),
            )
        });
        if !faithful {
            return None;
        }
    }
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
    if let Some(expr) = super::inline_iterator_eq::inline_iterator_eq_expr(
        ctx,
        func,
        callee_path,
        translated_args,
        arg_operands,
        caller_locals,
    ) {
        return Some(expr);
    }
    // `iter_compare` also implements cmp_by/partial_cmp_by/eq_by. Its third
    // argument is an arbitrary comparator, so equal iterator states or even
    // equal elements do not establish its ControlFlow result. Walk its body.
    if !compared_type_holds_address(ctx, first_arg, caller_locals)
        && let Some(expr) = inline_datatype_partial_eq_expr(callee_path, translated_args)
    {
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
        inline_primitive_cmp_expr(ctx, callee_path, translated_args, first_arg, caller_locals)
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
    if let Some(is_ne) = ctx.spec_array_comparison_for_operand(func, caller_locals)
        && let Some(expr) = inline_spec_array_eq_expr(
            ctx,
            callee_path,
            is_ne,
            ctx.spec_array_elements_are_faithful(func, caller_locals),
            translated_args,
            first_arg,
            caller_locals,
        )
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
    if let Some(expr) = inline_ptr_wrapping_byte_expr_with(stub, translated_args, |p, k, sub| {
        ctx.step_wrapping_address(p, k, sub)
    }) {
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
                return mono_ty::field_ty(field, &args).and_then(ty_signedness).unwrap_or(false);
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

#[cfg(test)]
fn inline_ptr_wrapping_byte_expr(stub: StubKind, translated_args: &[Expr]) -> Option<Expr> {
    inline_ptr_wrapping_byte_expr_with(
        stub,
        translated_args,
        crate::codegen_ay::chc::pointer_step::step_wrapping_pointer,
    )
}

/// The wrapping byte step of `stub`, with `step` the address step
/// (`ChcCtx::step_wrapping_address` in a body).
fn inline_ptr_wrapping_byte_expr_with(
    stub: StubKind,
    translated_args: &[Expr],
    step: impl FnOnce(Expr, Expr, bool) -> Expr,
) -> Option<Expr> {
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

    let count_ext =
        if is_byte_offset { SignExtension::SignExtend } else { SignExtension::ZeroExtend };
    let byte_count = coerce_inline_ptr_width(translated_args.get(1)?.clone(), count_ext)?;

    // Wrapping pointer arithmetic is defined even out of bounds, so no UB is
    // emitted here, and the step is exact mod 2^64 (`step_wrapping_pointer`),
    // as on the statement path (`translate_ptr_wrapping_byte_call`). This used
    // the in-bounds lane step, which drops the count's high 32 bits and the
    // carry out of the low lane: `p.wrapping_byte_add(1 << 32) == p` was
    // derivable. A symbolic count leaves the result's obj_id lane symbolic,
    // so a later deref gets the conservative `obj_valid` select from
    // heap_access_checks instead of a resolved allocation bound.
    //
    // A fat operand (`*const [T]`, `*const str`, `*const dyn Trait`) keeps its
    // metadata half: `wrapping_byte_*` is `cast::<u8>().wrapping_*(n)
    // .with_metadata_of(self)`, so only the data word moves.
    step_pointer_data_keep_metadata(translated_args.first()?.clone(), |ptr| {
        let ptr = coerce_inline_ptr_width(ptr, SignExtension::ZeroExtend)?;
        Some(step(ptr, byte_count, is_sub))
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
            let fallback = ExactVar::nondet(
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

/// Does the type an inlined `PartialEq::eq(&T, &T)` compares hold an address?
///
/// `PartialEq` on a type that holds a reference compares REFERENTS: `Option<&u8>`
/// ends in `*l == *r`. SMT structural equality on the translated datatype
/// compares the reference VALUES, i.e. addresses, so `Some(&x) == Some(&5)` with
/// `x == 5` folded to false and `!(o == Some(&5))` was proved under --ay-chc
/// (tools/soundness-duals/negative/joined_enum_referent_duals.rs). Such a
/// comparison must not take [`inline_datatype_partial_eq_expr`]. A type this
/// cannot classify counts as holding one: the fast path is skipped, never trusted.
fn compared_type_holds_address<'tcx, 'body>(
    ctx: &ChcCtx<'tcx, 'body>,
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> bool {
    let Some(arg_ty) = first_arg.and_then(|arg| arg.ty(caller_locals).ok()) else {
        return true;
    };
    let compared = match ctx.resolve_body_ty(arg_ty).kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => pointee,
        _ => arg_ty,
    };
    super::inline_ref_arg_binding::ty_holds_address(
        ctx,
        compared,
        super::inline_ref_arg_binding::SHAPE_DEPTH,
    )
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

fn inline_primitive_cmp_expr(
    ctx: &ChcCtx<'_, '_>,
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
        // Plain SMT equality is `PartialEq` only for a type that holds no
        // reference: for `Option<&u8>` (or `&u8` itself) `eq` compares REFERENTS
        // and the translated terms are addresses. Same gate, same reason, as the
        // datatype fast path (`compared_type_holds_address`).
        "eq" | "ne" if compared_type_holds_address(ctx, first_arg, caller_locals) => None,
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
    let fallback = ExactVar::nondet(
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
        // UB checks evaluate to false, as Kani (see
        // `rustc_compat::runtime_checks_value`); the destination is decided, not
        // left nondeterministic.
        "check_language_ub" | "check_library_ub" => Some(Expr::bool_const(false)),
        "ub_checks" if callee_path.contains("intrinsics::") => Some(Expr::bool_const(false)),
        _ => None,
    }
}

/// Model `SpecArrayEq::{spec_eq,spec_ne}` only for established array data.
///
/// Nested callers hand over untagged terms. Match the declared array sort at
/// exactly one reference boundary, rather than interpreting any bitvector as
/// a value. An inner reference (`&&[T; N]`) is not an array datum.
fn inline_spec_array_eq_expr(
    ctx: &ChcCtx<'_, '_>,
    callee_path: &str,
    negated: bool,
    faithful_elements: bool,
    translated_args: &[Expr],
    first_arg: Option<&Operand>,
    caller_locals: &[LocalDecl],
) -> Option<Expr> {
    let [lhs, rhs] = translated_args else { return None };
    let arg_ty = ctx.resolve_body_ty(first_arg?.ty(caller_locals).ok()?);
    let value_ty = match arg_ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, pointee, _) | RigidTy::RawPtr(pointee, _)) => {
            ctx.resolve_body_ty(pointee)
        }
        _ => arg_ty,
    };
    let TyKind::RigidTy(RigidTy::Array(_, len_const)) = value_ty.kind() else {
        return None;
    };
    let expected = ChcCtx::translate_ty(value_ty)?;
    if !expected.is_array() || lhs.sort() != &expected || rhs.sort() != &expected {
        return None;
    }
    let declared_len = len_const.eval_target_usize().ok()? as usize;
    if declared_len != 0 && !faithful_elements {
        return None;
    }
    let len = recover_spec_array_eq_len(Some(callee_path), first_arg, caller_locals)?;
    if len != declared_len {
        return None;
    }
    let eq = build_spec_array_eq(lhs, rhs, Some(len))?;
    Some(if negated { eq.not() } else { eq })
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
    fn test_inline_ub_checks_expr_returns_false_for_check_language_ub() {
        let expr = inline_ub_checks_expr("core::ub_checks::check_language_ub", &[])
            .expect("check_language_ub should inline");
        assert!(expr.sort().is_bool(), "UB checks should return Bool");
        assert_eq!(expr.to_string(), "false");
    }

    #[test]
    fn test_inline_ub_checks_expr_returns_false_for_intrinsics_ub_checks() {
        let expr = inline_ub_checks_expr("core::intrinsics::ub_checks", &[]).expect("ub_checks");
        assert!(expr.sort().is_bool(), "ub_checks should return Bool");
        assert_eq!(expr.to_string(), "false");
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

    /// A wrapping byte step with a symbolic count is full-width address
    /// arithmetic: the count's high 32 bits and the carry out of the low lane
    /// reach the result. The lane step used to keep the obj_id lane constant,
    /// which made `p.wrapping_byte_add(1 << 32) == p` derivable.
    #[test]
    fn test_inline_ptr_wrapping_byte_add_symbolic_count_is_full_width() {
        // ptr = concat(obj_id=0x42, offset=0x10), count symbolic.
        let ptr = Expr::bitvec_const(0x42u64, 32).concat(Expr::bitvec_const(0x10u64, 32));
        let count = Expr::var("sym_count", Sort::bitvec(POINTER_WIDTH));
        let expr = inline_ptr_wrapping_byte_expr(
            StubKind::PtrWrappingByteAdd,
            &[ptr.clone(), count.clone()],
        )
        .expect("wrapping_byte_add should inline");

        assert_eq!(
            expr,
            crate::codegen_ay::chc::pointer_step::identity_address_view(
                crate::codegen_ay::chc::pointer_step::identity_address_view(ptr).bvadd(count)
            ),
            "wrapping byte step must be a full-width add on the address view"
        );
    }

    /// A constant 2^32-byte wrapping step moves the address: the carry lands in
    /// the lane's high offset bits, not in the object field (object 0x42 stays).
    #[test]
    fn test_inline_ptr_wrapping_byte_add_two_pow_32_moves_the_address() {
        let ptr = Expr::bitvec_const(0x0000_0042_0000_0010u64, POINTER_WIDTH);
        let count = Expr::bitvec_const(1u64 << 32, POINTER_WIDTH);
        let expr = inline_ptr_wrapping_byte_expr(StubKind::PtrWrappingByteAdd, &[ptr, count])
            .expect("wrapping_byte_add should inline");
        assert_eq!(expr, Expr::bitvec_const(0x0001_0042_0000_0010u64, POINTER_WIDTH));
    }

    /// A large backwards wrapping byte step keeps every bit of the count.
    #[test]
    fn test_inline_ptr_wrapping_byte_sub_symbolic_count_is_full_width() {
        let ptr = Expr::var("p", Sort::bitvec(POINTER_WIDTH));
        let count = Expr::var("k", Sort::bitvec(POINTER_WIDTH));
        let expr = inline_ptr_wrapping_byte_expr(
            StubKind::PtrWrappingByteSub,
            &[ptr.clone(), count.clone()],
        )
        .expect("wrapping_byte_sub should inline");
        assert_eq!(
            expr,
            crate::codegen_ay::chc::pointer_step::identity_address_view(
                crate::codegen_ay::chc::pointer_step::identity_address_view(ptr).bvsub(count)
            ),
            "wrapping byte sub must be a full-width subtraction on the address view"
        );
    }

    /// A fat slice pointer keeps its length through a byte step: only the data
    /// word moves (ptr_to_ref_cast/slice check_with_byte_add_sub_pass).
    #[test]
    fn test_inline_ptr_wrapping_byte_add_keeps_fat_pointer_metadata() {
        use crate::codegen_ay::chc::expr::codegen_expr_heap_bv_eval::const_bv_value;

        let len = Expr::bitvec_const(5u64, POINTER_WIDTH);
        let data = Expr::bitvec_const(0x2_0000_0000u64, POINTER_WIDTH);
        let fat = len.concat(data);
        let count = Expr::bitvec_const(3u64, POINTER_WIDTH);
        let expr = inline_ptr_wrapping_byte_expr(StubKind::PtrWrappingByteAdd, &[fat, count])
            .expect("wrapping_byte_add on a fat pointer should inline");

        assert_eq!(expr.sort().bitvec_width(), Some(2 * POINTER_WIDTH));
        let (meta, _) = const_bv_value(&expr.clone().extract(127, 64)).expect("metadata folds");
        assert_eq!(meta, num_bigint::BigInt::from(5u32), "slice length must survive");
        let (addr, _) = const_bv_value(&expr.extract(63, 0)).expect("data word folds");
        assert_eq!(addr, num_bigint::BigInt::from(0x2_0000_0003u64));
    }

    /// add-then-sub by the same symbolic count on a fat pointer is the original
    /// pointer, metadata included, once the data words cancel.
    #[test]
    fn test_inline_ptr_wrapping_byte_add_sub_roundtrip_keeps_symbolic_metadata() {
        let fat = Expr::var("fat_ptr", Sort::bitvec(2 * POINTER_WIDTH));
        let count = Expr::var("k", Sort::bitvec(POINTER_WIDTH));
        let added = inline_ptr_wrapping_byte_expr(
            StubKind::PtrWrappingByteAdd,
            &[fat.clone(), count.clone()],
        )
        .expect("add inlines");
        let back = inline_ptr_wrapping_byte_expr(StubKind::PtrWrappingByteSub, &[added, count])
            .expect("sub inlines");
        assert_eq!(back.sort().bitvec_width(), Some(2 * POINTER_WIDTH));
        // The metadata half is the operand's own high half, not padding.
        let rendered = back.to_string();
        assert!(rendered.contains("(_ extract 127 64)"), "metadata taken from operand: {rendered}");
        assert!(!rendered.contains("zero_extend"), "no widened-thin padding: {rendered}");
    }

    /// A thin pointer is unchanged: same width, same value as before.
    #[test]
    fn test_inline_ptr_wrapping_byte_add_thin_pointer_unchanged() {
        let ptr = Expr::bitvec_const(0x1000u64, POINTER_WIDTH);
        let count = Expr::bitvec_const(2u64, POINTER_WIDTH);
        let expr = inline_ptr_wrapping_byte_expr(StubKind::PtrWrappingByteAdd, &[ptr, count])
            .expect("thin wrapping_byte_add inlines");
        assert_eq!(expr, Expr::bitvec_const(0x1002u64, POINTER_WIDTH));
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

    #[test]
    fn test_fixed_array_inline_comparison_requires_array_data_and_keeps_polarity() {
        use crate::codegen_ay::chc::ChcConfig;
        use crate::codegen_ay::context::with_test_ay_ctx_for_source;
        use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
        use rustc_public::CrateDef;
        use rustc_public::mir::Place;
        with_test_ay_ctx_for_source("pub fn arrays(value: [u32; 2]) { let _ = value; }", |ctx| {
            let body = find_instance_by_suffix(ctx.tcx, "arrays").body().unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, "arrays", ChcConfig::default());
            let arg = Operand::Copy(Place { local: 1, projection: vec![] });
            let eq_path = "<u32 as core::array::equality::SpecArrayEq<u32, 2>>::spec_eq";
            let ne_path = "<u32 as core::array::equality::SpecArrayEq<u32, 2>>::spec_ne";
            let pointer = Expr::var("pointer", Sort::bv64());
            assert!(
                inline_spec_array_eq_expr(
                    &chc,
                    eq_path,
                    false,
                    true,
                    &[pointer.clone(), pointer],
                    Some(&arg),
                    body.locals()
                )
                .is_none()
            );
            let array = Expr::const_array(Sort::bv64(), Expr::bitvec_const(5u64, 32));
            let args = [array.clone(), array];
            let eq = inline_spec_array_eq_expr(
                &chc,
                eq_path,
                false,
                true,
                &args,
                Some(&arg),
                body.locals(),
            )
            .unwrap();
            let ne = inline_spec_array_eq_expr(
                &chc,
                ne_path,
                true,
                true,
                &args,
                Some(&arg),
                body.locals(),
            )
            .unwrap();
            assert_eq!(ne, eq.not());
            assert!(
                inline_spec_array_eq_expr(&chc, eq_path, false, true, &args, None, body.locals())
                    .is_none()
            );
        });
    }
}
