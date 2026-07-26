// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Devirtualization of `dyn Trait` calls for the function inlining pass.
//!
//! Provides two strategies for resolving virtual (dyn Trait) calls to concrete
//! implementations:
//!
//! 1. **Single-impl devirtualization** (`try_devirtualize`): uses
//!    `tcx.trait_impls_of()` to find a unique concrete implementation.
//!
//! 2. **Receiver-tracing devirtualization** (`try_devirtualize_via_receiver`):
//!    traces the receiver operand backward through MIR assignments to find the
//!    concrete type from an Unsize coercion.
//!
//! Part of #3159: DynTrait category recovery.

use crate::kani_middle::transform::body::MutableBody;
use rustc_middle::ty::{TyCtxt, TypeVisitableExt};
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    BasicBlock, CastKind, Local, Operand, PointerCoercion, ProjectionElem, Rvalue, StatementKind,
};
use rustc_public::rustc_internal;
use rustc_public::ty::{FnDef, GenericArgKind, RigidTy, Ty, TyKind};
use tracing::debug;

/// Attempt to devirtualize a virtual (dyn Trait) call to a concrete implementation.
///
/// Uses `tcx.trait_impls_of()` to enumerate all implementations of the trait,
/// then resolves the method for each concrete type. Returns `Some(instance)` when
/// exactly one concrete implementation exists (single-impl devirtualization).
///
/// Part of #3159: DynTrait category recovery.
pub(super) fn try_devirtualize(
    tcx: TyCtxt<'_>,
    fn_def: FnDef,
    fn_args: &rustc_public::ty::GenericArgs,
) -> Option<Instance> {
    let method_def_id = fn_def.def_id();
    let internal_method_def_id = rustc_internal::internal(tcx, method_def_id);

    let parent_def_id = tcx.parent(internal_method_def_id);
    if !tcx.is_trait(parent_def_id) {
        return None;
    }

    let trait_impls = tcx.trait_impls_of(parent_def_id);

    // Part of #3159: If blanket impls exist, single-impl devirtualization is
    // unsound — a blanket impl (e.g., `impl<T: ?Sized> Trait for Outer<T>`)
    // might be the actual callee but is not in non_blanket_impls(). Fall through
    // to receiver-tracing devirtualization which resolves the concrete type.
    if !trait_impls.blanket_impls().is_empty() {
        debug!(
            "FunctionInlinePass: devirtualize: blanket impls exist for {} — deferring to receiver-tracing",
            fn_def.0.name()
        );
        return None;
    }

    let mut concrete_instances: Vec<Instance> = Vec::new();
    let mut has_generic_impls = false;

    for impl_def_id in trait_impls.non_blanket_impls().values().flatten() {
        let impl_self_ty = tcx.type_of(*impl_def_id).skip_binder();
        if impl_self_ty.has_param() {
            // Part of #3159: Track that a generic impl was skipped. When
            // generic impls exist (e.g., `impl<T: ?Sized> Trait for Outer<T>`),
            // single-impl devirtualization is unsound — the generic impl might
            // match the actual callee type but isn't enumerated here.
            has_generic_impls = true;
            continue;
        }

        let stable_self_ty = rustc_internal::stable(impl_self_ty);
        let Some(concrete_args) = replace_dyn_self(fn_args, stable_self_ty) else {
            continue;
        };

        if let Ok(concrete_instance) = Instance::resolve(fn_def, &concrete_args) {
            if concrete_instance.has_body() {
                concrete_instances.push(concrete_instance);
                if concrete_instances.len() > 1 {
                    debug!(
                        "FunctionInlinePass: devirtualize: multiple impls for {} — skipping",
                        fn_def.0.name()
                    );
                    return None;
                }
            }
        }
    }

    // Part of #3159: Do not claim single-impl when generic impls were skipped.
    // A generic impl like `impl<T: ?Sized> Identity for Outer<T>` matches
    // `Outer<Inner>`, `Outer<dyn Identity>`, etc. — the concrete call might go
    // through the generic impl, not the single non-blanket impl found here.
    if has_generic_impls {
        debug!(
            "FunctionInlinePass: devirtualize: generic impls skipped for {} — deferring to receiver-tracing",
            fn_def.0.name()
        );
        return None;
    }

    if concrete_instances.len() == 1 {
        let inst = concrete_instances.into_iter().next().expect("checked len == 1");
        debug!("FunctionInlinePass: devirtualized {} to {}", fn_def.0.name(), inst.name());
        Some(inst)
    } else {
        None
    }
}

/// Replace the first `dyn Trait` Self type in generic args with a concrete type.
///
/// Part of #3159: used by devirtualization to substitute concrete types.
fn replace_dyn_self(
    fn_args: &rustc_public::ty::GenericArgs,
    concrete_ty: Ty,
) -> Option<rustc_public::ty::GenericArgs> {
    let mut new_args: Vec<GenericArgKind> = Vec::new();
    let mut replaced = false;
    for arg in &fn_args.0 {
        match arg {
            GenericArgKind::Type(ty) if !replaced => {
                if matches!(ty.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                    new_args.push(GenericArgKind::Type(concrete_ty));
                    replaced = true;
                } else {
                    new_args.push(arg.clone());
                }
            }
            _ => new_args.push(arg.clone()),
        }
    }
    replaced.then_some(rustc_public::ty::GenericArgs(new_args))
}

/// Attempt to devirtualize by tracing the receiver (first argument) backward
/// through MIR assignments to find the concrete type from an Unsize coercion.
///
/// This handles the multi-impl case where `try_devirtualize` fails because
/// there are multiple implementations of the trait. By tracing the receiver
/// operand backward, we can find the concrete type that was coerced to `dyn Trait`.
///
/// Part of #3159: DynTrait category recovery.
pub(super) fn try_devirtualize_via_receiver(
    _tcx: TyCtxt<'_>,
    fn_def: FnDef,
    fn_args: &rustc_public::ty::GenericArgs,
    call_args: &[Operand],
    body: &MutableBody,
) -> Option<Instance> {
    let receiver = call_args.first()?;
    let concrete_ty = trace_receiver_concrete_type(receiver, body)?;
    let concrete_args = replace_dyn_self(fn_args, concrete_ty)?;
    match Instance::resolve(fn_def, &concrete_args) {
        Ok(inst) if inst.has_body() => {
            debug!(
                "FunctionInlinePass: devirtualized via receiver {} to {}",
                fn_def.0.name(),
                inst.name()
            );
            Some(inst)
        }
        _ => None,
    }
}

/// Trace a receiver operand backward through MIR assignments to find the
/// concrete type from an Unsize coercion (e.g., `&ConcreteType` → `&dyn Trait`).
///
/// Follows chains of `Use(Copy/Move)`, `Ref`, and `Cast(Unsize)` assignments
/// to find the source type of the unsizing coercion.
fn trace_receiver_concrete_type(receiver: &Operand, body: &MutableBody) -> Option<Ty> {
    let mut current_local = match receiver {
        Operand::Copy(p) | Operand::Move(p) => p.local,
        Operand::Constant(_) => return None,
    };

    let blocks = body.blocks();
    let locals = body.locals();

    for _ in 0..20 {
        let rvalue = find_last_assignment(current_local, &blocks)?;

        match rvalue {
            Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize), operand, _) => {
                // Found the Unsize coercion — extract the source concrete type
                let source_ty = match operand {
                    Operand::Copy(p) | Operand::Move(p) => locals[p.local].ty,
                    Operand::Constant(c) => c.ty(),
                };
                return extract_self_type(source_ty);
            }
            Rvalue::Use(Operand::Copy(p) | Operand::Move(p)) => {
                current_local = p.local;
            }
            Rvalue::Ref(_, _, p) => {
                if p.projection.is_empty() {
                    // Simple reference: check if local type is concrete
                    let local_ty = locals[p.local].ty;
                    if let Some(inner) = extract_self_type(local_ty) {
                        return Some(inner);
                    }
                    current_local = p.local;
                } else if p.projection.len() == 1
                    && matches!(p.projection[0], ProjectionElem::Deref)
                {
                    // Re-borrow pattern: `_x = &(*_y)` — follow through
                    current_local = p.local;
                } else {
                    return None;
                }
            }
            _ => return None,
        }
    }
    None
}

/// Find the unique assignment to a local variable across all blocks.
///
/// Returns `None` if the target has zero or multiple assignments, since multiple
/// assignments indicate a CFG-dependent value where array-order scanning would
/// be unsound (blocks are not ordered by execution flow).
fn find_last_assignment(target: Local, blocks: &[BasicBlock]) -> Option<Rvalue> {
    let mut found: Option<Rvalue> = None;
    let mut count = 0;
    for block in blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                if place.local == target && place.projection.is_empty() {
                    found = Some(rvalue.clone());
                    count += 1;
                }
            }
        }
    }
    // Only safe when exactly one assignment exists (SSA property).
    // Multiple assignments means CFG-dependent value — bail out.
    if count == 1 { found } else { None }
}

/// Extract the concrete Self type from a reference, Box, or raw pointer type.
/// Returns `Some(T)` for `&T`, `&mut T`, `*const T`, `*mut T`, or `Box<T>`.
fn extract_self_type(ty: Ty) -> Option<Ty> {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                None
            } else {
                Some(inner)
            }
        }
        TyKind::RigidTy(RigidTy::Adt(adt_def, args)) => {
            // Check for Box<T>
            let name = adt_def.name();
            if name.ends_with("::Box") || name == "Box" {
                if let Some(GenericArgKind::Type(inner)) = args.0.first() {
                    if !matches!(inner.kind(), TyKind::RigidTy(RigidTy::Dynamic(..))) {
                        return Some(*inner);
                    }
                }
            }
            None
        }
        _ => None,
    }
}
