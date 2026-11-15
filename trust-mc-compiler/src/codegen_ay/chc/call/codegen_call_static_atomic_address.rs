// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Atomic::as_ptr is storage identity, not a read of the Atomic's value.
//! Admit only closed static-array origins and a layout-validated zero-offset
//! scalar window. All other receivers keep their existing dispatch/fallback.
use super::ChcCtx;
use super::chc_call_context::DispatchCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_rules::CodegenRules;
use crate::codegen_ay::chc::decl::static_path::static_path;
use crate::codegen_ay::ptr_repr::PtrRepr;
use rustc_public::CrateDef;
use rustc_public::ty::{RigidTy, TyKind};

/// Private constructor: evidence is minted only after the guarded model emits.
pub(in crate::codegen_ay) struct ExactAtomicAddressModel<'a> {
    root: Option<rustc_public::mir::mono::Instance>,
    body: &'a rustc_public::mir::Body,
    block: usize,
    callee: rustc_public::mir::mono::Instance,
}
impl<'a> ExactAtomicAddressModel<'a> {
    pub(in crate::codegen_ay) fn into_parts(
        self,
    ) -> (
        Option<rustc_public::mir::mono::Instance>,
        &'a rustc_public::mir::Body,
        usize,
        rustc_public::mir::mono::Instance,
    ) {
        (self.root, self.body, self.block, self.callee)
    }
}

pub(super) fn try_static_atomic_as_ptr(
    ctx: &mut ChcCtx<'_, '_>,
    dcx: &DispatchCallContext<'_>,
) -> bool {
    // This shortcut binds one whole output slot. A projected destination is
    // a store through/into that local and must use the existing general path.
    if !dcx.destination.projection.is_empty() {
        return false;
    }
    let Some(target) = dcx.target else { return false };
    let [receiver] = dcx.args else { return false };
    let Some(TyKind::RigidTy(RigidTy::FnDef(def, fn_args))) =
        dcx.func.ty(ctx.body.locals()).ok().map(|ty| ty.kind())
    else {
        return false;
    };
    if !crate::kani_middle::std_abstraction::is_sysroot_core_definition(
        ctx.tcx,
        rustc_public::rustc_internal::internal(ctx.tcx, def.def_id()),
    ) || !def.name().contains("sync::atomic")
        || def.name().rsplit("::").next() != Some("as_ptr")
    {
        return false;
    }
    let Ok(callee) = rustc_public::mir::mono::Instance::resolve(def, &fn_args) else {
        return false;
    };
    if ctx.static_array_address_origins(receiver).is_none() {
        return false;
    }
    let Some(TyKind::RigidTy(RigidTy::Ref(_, atomic, _))) =
        receiver.ty(ctx.body.locals()).ok().map(|ty| ty.kind())
    else {
        return false;
    };
    let Some(TyKind::RigidTy(RigidTy::RawPtr(scalar, _))) =
        dcx.destination.ty(ctx.body.locals()).ok().map(|ty| ty.kind())
    else {
        return false;
    };
    if ctx.get_type_size(atomic).is_none()
        || ctx.get_type_size(atomic) != ctx.get_type_size(scalar)
        || static_path(atomic, 0, scalar).is_none()
    {
        return false;
    }
    let Some(pointer) = ctx.translate_operand_with_modified(receiver, dcx.modified_locals) else {
        return false;
    };
    let Some(PtrRepr::Thin(addr)) = PtrRepr::classify(&pointer) else { return false };
    let Some((_, dest)) = ctx.resolve_destination(dcx.destination.local) else { return false };
    if dest.sort() != addr.as_expr().sort() {
        return false;
    }
    let out = ctx.build_output_args(dcx.modified_locals, &[dcx.destination.local]);
    ctx.emit_goto_rule_extra(
        dcx.from_app,
        *target,
        &out,
        dcx.stmt_constraints,
        [dest.eq(addr.into_expr())],
    );
    // The dispatch context must name this actual MIR call, including every
    // operand and return place; an artificial/substituted context earns no receipt.
    if let Some(block) = ctx.body.blocks.get(dcx.bb_idx)
        && let rustc_public::mir::TerminatorKind::Call { func, args, destination, target, .. } =
            &block.terminator.kind
        && func == dcx.func
        && args == dcx.args
        && destination == dcx.destination
        && target == dcx.target
    {
        crate::codegen_ay::unstubbed_accounting::record_exact_address(ExactAtomicAddressModel {
            root: ctx.current_instance,
            body: ctx.body,
            block: dcx.bb_idx,
            callee,
        });
    }
    // No ref_target or value snapshot is forwarded: the result reads/writes
    // the live typed image at precisely this address.
    true
}

#[cfg(all(test, feature = "compiler-corpus-tests"))]
#[path = "codegen_call_static_atomic_address_tests.rs"]
mod tests;
