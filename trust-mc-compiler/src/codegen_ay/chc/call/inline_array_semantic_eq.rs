// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The core default array comparison over established values, without inventing
//! addresses for them. Only a value-only element body can use this lane.

#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::mir::mono::{Instance, InstanceKind};
use rustc_public::mir::{
    Body, CastKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{AdtKind, FloatTy, FnDef, GenericArgKind, GenericArgs, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};
use std::collections::{BTreeMap, HashMap};

use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_misc::CallMisc;
use super::codegen_types::CodegenTypes;
use super::inline_body::{
    InlineReturn, extract_inline_assert_guard, speculative_inline, strip_inline_assert_fallback,
    translate_inline_body_with_metadata,
};
use super::inline_ref_arg_binding::ty_holds_address;

impl ChcCtx<'_, '_> {
    /// The semantic array lane walks the element implementation instead of
    /// core's slice loop. Discover that same admitted body before memory
    /// seeding closes, just as the ordinary direct-callee prescan does.
    /// Otherwise a promoted array's field type is first noted by the walker
    /// after the entry rule, and correctly triggers `const_object_unseeded`.
    pub(in crate::codegen_ay::chc) fn prescan_array_semantic_eq(&mut self, body: &Body) {
        let mut elements = Vec::new();
        for block in &body.blocks {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                continue;
            };
            let Ok(ty) = func.ty(body.locals()) else { continue };
            let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = self.resolve_body_ty(ty).kind()
            else {
                continue;
            };
            let Ok(instance) = Instance::resolve(def, &generics) else { continue };
            if !self.spec_array_has_default_body(&instance) {
                continue;
            }
            let Some((_, elem, count)) = array_input_shape(self, args, body.locals()) else {
                continue;
            };
            if count != 0 && count <= Self::SLICE_EQ_EXPAND_MAX_ELEMS && !elements.contains(&elem) {
                elements.push(elem);
            }
        }
        for elem in elements {
            if let Some((_, body)) = value_only_element_eq(self, elem) {
                self.register_callee_body_consts(&body);
            }
        }
    }
}

/// Top-level counterpart of the nested semantic lane. Preprocessing preserves
/// this authenticated boundary in CHC, so it must run before the generic
/// unfaithful-comparison fallback consumes the call.
pub(super) fn try_codegen_array_semantic_eq(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
    target: usize,
    path: &str,
) -> bool {
    if dcx.args.len() != 2 || !dcx.destination.projection.is_empty() {
        return false;
    }
    let locals = ctx.body.locals().to_vec();
    let Ok(ty) = dcx.func.ty(&locals) else { return false };
    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ctx.resolve_body_ty(ty).kind() else {
        return false;
    };
    let Ok(instance) = Instance::resolve(def, &args) else { return false };
    if !ctx.spec_array_has_default_body(&instance) {
        return false;
    }
    let values: Option<Vec<_>> = dcx
        .args
        .iter()
        .map(|arg| {
            ctx.resolve_ref_or_const_referent_tagged(arg, dcx.modified_locals)
                .and_then(|referent| ctx.fixed_array_eq_referent_datum(arg, referent))
                .or_else(|| {
                    ctx.try_load_traced_fixed_array_referent(arg).map(|value| value.into_expr())
                })
        })
        .collect();
    // Keep checks from every attempted referent load, including a decline.
    super::ptr_receiver_mem::drain_pending_checks(ctx, dcx, target);
    let Some(values) = values else { return false };
    let Some(result) = try_inline_array_semantic_eq(ctx, &instance, dcx.args, &values, &locals, 0)
    else {
        return false;
    };
    // This evaluates element bodies, not the outer comparison loop. Leave
    // call_replays_body false so explicit call-unwinding checks remain active.
    ctx.emit_translated_inline_call_result(
        dcx,
        target,
        result.value,
        result.vtable,
        result.alias_updates,
        result.deferred_checks,
        &BTreeMap::new(),
        &HashMap::new(),
        Some(path),
        "spec_array_semantic_eq",
        "spec_array_semantic_alias",
    )
}
use crate::codegen_ay::chc::codegen_ctx::ExactVar;

/// The input references must already carry their exact array *values*. A
/// reference/pointer datum, nested reference, heterogeneous pair, or effectful
/// element implementation is not a value-only comparison.
pub(super) fn try_inline_array_semantic_eq(
    ctx: &mut ChcCtx<'_, '_>,
    instance: &Instance,
    args: &[Operand],
    values: &[Expr],
    locals: &[rustc_public::mir::LocalDecl],
    inline_depth: usize,
) -> Option<InlineReturn> {
    if !ctx.spec_array_has_default_body(instance) || args.len() != 2 || values.len() != 2 {
        return None;
    }
    let negated = ctx.authenticated_spec_array_comparison_is_ne(instance.def.def_id())?;
    let (array_ty, elem, count) = array_input_shape(ctx, args, locals)?;
    let sort = ChcCtx::translate_ty(array_ty)?;
    if !sort.is_array() || values.iter().any(|value| value.sort() != &sort) {
        return None;
    }
    // Reuse the existing bound for explicit semantic slice comparisons.
    if count > ChcCtx::SLICE_EQ_EXPAND_MAX_ELEMS {
        return None;
    }
    if count == 0 {
        return Some(InlineReturn::value_only(Expr::bool_const(!negated)));
    }
    let (eq, body) = value_only_element_eq(ctx, elem)?;
    let elem_sort = ChcCtx::translate_ty(elem)?;
    let width = values[0].sort().array_sort()?.index_sort.bitvec_width()?;
    speculative_inline(ctx, |ctx| {
        let diagnostics_before = value_lane_diagnostics(ctx);
        let mut result = InlineReturn::value_only(Expr::bool_const(true));
        let mut normal = Expr::bool_const(true);
        for index in 0..count {
            let index = Expr::bitvec_const(index as u64, width);
            let mut params = Vec::with_capacity(2);
            for value in values {
                let value = value.clone().select(index.clone());
                let value = ctx.try_unflatten_bv_to_datatype(value, elem);
                if value.sort() != &elem_sort {
                    return None;
                }
                params.push(value);
            }
            let walked = translate_inline_body_with_metadata(
                ctx,
                &body,
                &params,
                0,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
                Some(eq),
                inline_depth + 1,
            )?;
            if !walked.value.sort().is_bool()
                || !walked.alias_updates.is_empty()
                || walked.alloc_id.is_some()
                || walked.vtable.is_some()
            {
                return None;
            }
            let prefix = normal.clone().and(result.value.clone());
            result.deferred_checks.extend(
                walked.deferred_checks.into_iter().map(|check| check.weaken_by_guard(&prefix)),
            );
            // Extract BEFORE combining: the standard extractor follows ITEs,
            // and cannot recover an assertion sentinel hidden inside AND.
            let guard = extract_inline_assert_guard(&walked.value)
                .unwrap_or_else(|| Expr::bool_const(true));
            normal = normal.and(prefix.not().or(guard));
            let value = strip_inline_assert_fallback(&walked.value)
                .unwrap_or_else(|| Expr::bool_const(false));
            result.value = result.value.and(value);
        }
        if value_lane_diagnostics(ctx) != diagnostics_before {
            return None;
        }
        if negated {
            result.value = result.value.not();
        }
        let fallback = ExactVar::nondet(
            super::chc_fresh_name("__assert_fail_inline"),
            result.value.sort().clone(),
        );
        result.value = Expr::ite(normal, result.value, fallback);
        Some(result)
    })
}

/// The shared shape check keeps prescanning and evaluation on the same pair
/// of homogeneous, single-reference array inputs.
fn array_input_shape(
    ctx: &ChcCtx<'_, '_>,
    args: &[Operand],
    locals: &[rustc_public::mir::LocalDecl],
) -> Option<(Ty, Ty, usize)> {
    if args.len() != 2 {
        return None;
    }
    let mut exact_ty = None;
    for arg in args {
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) =
            ctx.resolve_body_ty(arg.ty(locals).ok()?).kind()
        else {
            return None;
        };
        let ty = ctx.resolve_body_ty(pointee);
        if !matches!(ty.kind(), TyKind::RigidTy(RigidTy::Array(..)))
            || exact_ty.is_some_and(|previous| previous != ty)
        {
            return None;
        }
        exact_ty = Some(ty);
    }
    let array_ty = exact_ty?;
    let TyKind::RigidTy(RigidTy::Array(elem, count)) = array_ty.kind() else { return None };
    Some((
        array_ty,
        ctx.resolve_body_ty(elem),
        usize::try_from(count.eval_target_usize().ok()?).ok()?,
    ))
}

/// Resolve exactly the body the value lane will execute, including the
/// default-ne and active-stub guards. Discovery must not create authority for
/// a body that evaluation would refuse.
fn value_only_element_eq(ctx: &ChcCtx<'_, '_>, elem: Ty) -> Option<(Instance, Body)> {
    if !value_type_supported(ctx, elem, 8) {
        return None;
    }
    let trait_id = ctx.tcx.lang_items().eq_trait()?;
    if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(ctx.tcx, trait_id) {
        return None;
    }
    let resolve = |name: &str| {
        let method = ctx
            .tcx
            .associated_item_def_ids(trait_id)
            .iter()
            .copied()
            .find(|def| ctx.tcx.item_name(*def).as_str() == name)?;
        let stable = rustc_internal::stable(method);
        let instance = Instance::resolve(
            FnDef(stable),
            &GenericArgs(vec![GenericArgKind::Type(elem), GenericArgKind::Type(elem)]),
        )
        .ok()?;
        Some((method, instance))
    };
    let (ne_method, ne) = resolve("ne")?;
    // The core array default calls element.ne. Its complement may be replaced
    // by eq only when resolution chose the actual core default, not a custom ne.
    if rustc_internal::internal(ctx.tcx, ne.def.def_id()) != ne_method
        || matches!(ne.kind, InstanceKind::Virtual { .. })
        || crate::kani_middle::transform::instance_has_unit_stub(&ne)
    {
        return None;
    }
    let (_, eq) = resolve("eq")?;
    if matches!(eq.kind, InstanceKind::Virtual { .. }) {
        return None;
    }
    let body = crate::kani_middle::transform::walker_transformed_body(ctx.tcx, eq)?;
    if !value_only_body(ctx, &body, elem) {
        return None;
    }
    Some((eq, body))
}

fn value_place(place: &Place) -> bool {
    let mut projection = place.projection.as_slice();
    if matches!(place.local, 1 | 2) {
        let Some((ProjectionElem::Deref, tail)) = projection.split_first() else { return false };
        projection = tail;
    }
    // Field-only access cannot observe the address of the receiver or follow
    // another pointer. Indexing and downcasts need additional checks.
    projection.iter().all(|p| matches!(p, ProjectionElem::Field(..)))
}

fn value_operand(ctx: &ChcCtx<'_, '_>, operand: &Operand, body: &Body) -> bool {
    operand.ty(body.locals()).ok().is_some_and(|ty| value_type_supported(ctx, ty, 8))
        && match operand {
            Operand::Copy(place) | Operand::Move(place) => value_place(place),
            Operand::Constant(_) => true,
            #[cfg(trust_toolchain)]
            Operand::RuntimeChecks(_) => true,
        }
}

fn value_only_body(ctx: &ChcCtx<'_, '_>, body: &Body, elem: Ty) -> bool {
    if body.arg_locals().len() != 2 || body.locals().len() < 3 {
        return false;
    }
    if !matches!(body.locals()[0].ty.kind(), TyKind::RigidTy(RigidTy::Bool)) {
        return false;
    }
    for (index, local) in body.locals().iter().enumerate() {
        if matches!(index, 1 | 2) {
            if !matches!(local.ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, inner, rustc_public::mir::Mutability::Not)) if ctx.resolve_body_ty(inner) == elem)
            {
                return false;
            }
        } else if !value_type_supported(ctx, local.ty, 8) {
            return false;
        }
    }
    let operand = |value: &Operand| value_operand(ctx, value, body);
    for block in &body.blocks {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Assign(place, rvalue)
                    if place.projection.is_empty() && !matches!(place.local, 1 | 2) =>
                {
                    let allowed = match rvalue {
                        Rvalue::Use(value, ..) | Rvalue::UnaryOp(_, value) => operand(value),
                        Rvalue::BinaryOp(_, lhs, rhs) | Rvalue::CheckedBinaryOp(_, lhs, rhs) => {
                            operand(lhs) && operand(rhs)
                        }
                        Rvalue::Cast(
                            CastKind::IntToInt
                            | CastKind::IntToFloat
                            | CastKind::FloatToInt
                            | CastKind::FloatToFloat,
                            value,
                            _,
                        ) => operand(value),
                        Rvalue::Aggregate(_, values) => values.iter().all(operand),
                        _ => false,
                    };
                    if !allowed {
                        return false;
                    }
                }
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::Nop
                | StatementKind::Coverage(_)
                | StatementKind::ConstEvalCounter => {}
                _ => return false,
            }
        }
        match &block.terminator.kind {
            TerminatorKind::Return | TerminatorKind::Goto { .. } => {}
            TerminatorKind::SwitchInt { discr, .. } if operand(discr) => {}
            TerminatorKind::Assert { cond, .. } if operand(cond) => {}
            _ => return false,
        }
    }
    true
}

// Exact value-only evaluation must not inherit an unrelated width-based
// fallback for f16/f128 casts or negation. Inspect every encountered type,
// including fields and temporaries rather than only the array element root.
fn value_type_supported(ctx: &ChcCtx<'_, '_>, ty: Ty, depth: usize) -> bool {
    if depth == 0 || ty_holds_address(ctx, ty, depth) || ctx.ty_has_interior_mut(ty) {
        return false;
    }
    match ctx.resolve_body_ty(ty).kind() {
        TyKind::RigidTy(
            RigidTy::Bool
            | RigidTy::Char
            | RigidTy::Int(_)
            | RigidTy::Uint(_)
            | RigidTy::Float(FloatTy::F32 | FloatTy::F64),
        ) => true,
        TyKind::RigidTy(RigidTy::Tuple(fields)) => {
            fields.iter().all(|ty| value_type_supported(ctx, *ty, depth - 1))
        }
        TyKind::RigidTy(RigidTy::Array(elem, _)) => value_type_supported(ctx, elem, depth - 1),
        TyKind::RigidTy(RigidTy::Adt(def, args))
            if matches!(def.kind(), AdtKind::Struct | AdtKind::Enum) =>
        {
            def.variants_iter().all(|variant| {
                variant.fields().iter().all(|field| {
                    crate::codegen_ay::shared::mono_ty::field_ty(field, &args)
                        .is_some_and(|ty| value_type_supported(ctx, ty, depth - 1))
                })
            })
        }
        _ => false,
    }
}

// A successful body walk must not hide a new fallback behind its returned
// Bool. Preserve diagnostics on decline; never erase the recorded refusal.
fn value_lane_diagnostics(ctx: &ChcCtx<'_, '_>) -> [usize; 15] {
    let d = &ctx.diagnostics;
    [
        ctx.fallback_count,
        d.place_translation_drop.get(),
        d.sound_havoc_drop.get(),
        d.const_translation_drop.get(),
        d.unsupported_field_projection.get(),
        d.unhandled_call.get(),
        d.assume_dropped_transition.get(),
        d.assert_untranslatable.get(),
        d.heap_check_untranslatable.get(),
        d.heap_check_unknown_layout.get(),
        d.store_dropped_transition.get(),
        d.aggregate_encoding_gap.get(),
        d.recursive_unwind_exhausted.get(),
        d.offset_provenance_unresolved.get(),
        d.coerce_eq_dropped_constraint.get(),
    ]
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
mod tests {
    use super::*;
    use crate::codegen_ay::chc::ChcConfig;
    use crate::codegen_ay::context::with_test_ay_ctx_for_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;

    #[test]
    fn test_value_only_array_respects_outer_and_default_ne_stubs() {
        use ay_bindings::Sort;
        const SOURCE: &str = r#"
            #![allow(dead_code)]
            #[derive(Clone, Copy)] pub struct Parity(u8);
            impl PartialEq for Parity {
                fn eq(&self, other: &Self) -> bool { self.0 % 2 == other.0 % 2 }
            }
            pub fn arrays(a: &[Parity; 2], b: &[Parity; 2]) -> bool { a == b }
            pub fn ne_stub<T: ?Sized, U: ?Sized>(_: &T, _: &U) -> bool { false }
            pub fn array_stub<T, U, const N: usize>(_: &[T; N], _: &[U; N]) -> bool { false }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let root = find_instance_by_suffix(ctx.tcx, "arrays");
            let body = crate::callee_body::CalleeBody::callee_body(&root).unwrap();
            let mut pending = vec![(root, 0)];
            let mut spec = None;
            while let Some((candidate, depth)) = pending.pop() {
                if crate::kani_middle::std_abstraction::is_default_spec_array_comparison(
                    ctx.tcx, &candidate,
                ) {
                    spec = Some(candidate);
                    break;
                }
                if depth >= 4 {
                    continue;
                }
                let Some(callee_body) = crate::callee_body::CalleeBody::callee_body(&candidate)
                else {
                    continue;
                };
                for block in &callee_body.blocks {
                    let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                        continue;
                    };
                    let Ok(ty) = func.ty(callee_body.locals()) else { continue };
                    let TyKind::RigidTy(RigidTy::FnDef(def, args)) = ty.kind() else { continue };
                    if let Ok(next) = Instance::resolve(def, &args) {
                        pending.push((next, depth + 1));
                    }
                }
            }
            let spec = spec.expect("default array method");
            let TyKind::RigidTy(RigidTy::FnDef(spec_def, _)) = spec.ty().kind() else {
                panic!("FnDef")
            };
            let trait_id = ctx.tcx.lang_items().eq_trait().unwrap();
            let ne_def = ctx
                .tcx
                .associated_item_def_ids(trait_id)
                .iter()
                .copied()
                .find(|def| ctx.tcx.item_name(*def).as_str() == "ne")
                .unwrap();
            let ne_def = FnDef(rustc_internal::stable(ne_def));
            let stub = |name: &str| {
                let item = rustc_public::all_local_items()
                    .into_iter()
                    .find(|item| item.name().ends_with(name))
                    .unwrap();
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = item.ty().kind() else {
                    panic!("stub FnDef")
                };
                def
            };
            let args = [1, 2].map(|local| Operand::Copy(Place { local, projection: vec![] }));
            let value = Expr::const_array(Sort::bv64(), Expr::bitvec_const(1u64, 8));
            let values = [value.clone(), value];
            let mut chc = ChcCtx::new(ctx.tcx, &body, "arrays", ChcConfig::default());
            assert!(
                try_inline_array_semantic_eq(&mut chc, &spec, &args, &values, body.locals(), 0)
                    .is_some()
            );
            for (original, replacement) in
                [(ne_def, stub("ne_stub")), (spec_def, stub("array_stub"))]
            {
                let _scope = crate::kani_middle::transform::UnitStubsTestScope::install(
                    [(original, replacement)].into_iter().collect(),
                );
                assert!(
                    try_inline_array_semantic_eq(&mut chc, &spec, &args, &values, body.locals(), 0)
                        .is_none(),
                    "an active body replacement must not inherit original semantic authority"
                );
            }
        });
    }

    #[test]
    fn test_value_only_array_excludes_unmodeled_float_fields_and_temporaries() {
        const SOURCE: &str = r#"
            #![feature(f16, f128)]
            #![allow(dead_code, unused_variables)]
            pub struct Half(f16);
            pub struct Single(f32);
            pub fn carriers(a: f16, b: f128, c: f32, d: f64, e: Half, f: Single) {}
            pub fn half_eq(a: &u8, b: &u8) -> bool { -(*a as f16) == *b as f16 }
        "#;
        with_test_ay_ctx_for_source(SOURCE, |ctx| {
            let body = crate::callee_body::CalleeBody::callee_body(&find_instance_by_suffix(
                ctx.tcx, "carriers",
            ))
            .unwrap();
            let chc = ChcCtx::new(ctx.tcx, &body, "carriers", ChcConfig::default());
            for (local, supported) in
                [false, false, true, true, false, true].into_iter().enumerate()
            {
                assert_eq!(value_type_supported(&chc, body.locals()[local + 1].ty, 8), supported);
            }
            let body = crate::callee_body::CalleeBody::callee_body(&find_instance_by_suffix(
                ctx.tcx, "half_eq",
            ))
            .unwrap();
            let elem = body.locals()[1].ty.kind();
            let TyKind::RigidTy(RigidTy::Ref(_, elem, _)) = elem else {
                panic!("reference argument")
            };
            assert!(!value_only_body(&chc, &body, elem), "f16 temporary must be refused");
        });
    }
}
