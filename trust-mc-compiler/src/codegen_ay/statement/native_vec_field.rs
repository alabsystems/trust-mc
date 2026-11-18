// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Typed reads of the real Vec header's declared fields.
//!
//! Rust's `buf: RawVec` is not field zero of the flattened model Vec. Recover
//! that view from a current, live owner; a cached field sort grants no custody.

use super::{IntoOption, StatementCodegen};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use ay_bindings::Expr;
use rustc_public::mir::{
    BorrowKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{AdtDef, GenericArgs, RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

#[derive(Clone)]
struct HeaderTarget {
    owner: usize,
    // At most String.vec then Vec.buf, each checked against its actual ADT.
    fields: Vec<usize>,
}

impl StatementCodegen<'_, '_, '_> {
    pub(super) fn native_live_string_owner(&self, owner: usize) -> bool {
        matches!(self.body.locals().get(owner).map(|l| l.ty.kind()),
            Some(TyKind::RigidTy(RigidTy::Adt(def, _))) if Self::is_native_string_adt(def))
            && self
                .current_native_header_value(&HeaderTarget { owner, fields: Vec::new() })
                .is_some()
    }

    pub(super) fn native_live_string_receiver_owner(
        &mut self,
        receiver: &Operand,
    ) -> Option<usize> {
        let (Operand::Copy(place) | Operand::Move(place)) = receiver else { return None };
        if !place.projection.is_empty()
            || !matches!(
                receiver.ty(self.body.locals()).ok()?.kind(),
                TyKind::RigidTy(RigidTy::Ref(_, _, rustc_public::mir::Mutability::Not))
            )
        {
            return None;
        }
        let target = self.native_vec_reference_target(place.local, &mut 4096, &mut Vec::new())?;
        (target.fields.is_empty() && self.native_live_string_owner(target.owner))
            .then_some(target.owner)
    }

    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay) fn test_native_rawvec_ptr_call(&self, func: &Operand) -> bool {
        self.native_rawvec_ptr_call(func)
    }

    #[cfg(all(test, feature = "compiler-corpus-tests"))]
    pub(in crate::codegen_ay) fn test_native_vec_field_place(
        &mut self,
        place: &Place,
    ) -> Option<Option<Expr>> {
        self.native_vec_field_place(place)
    }

    pub(super) fn is_native_rawvec_adt(def: AdtDef) -> bool {
        rustc_middle::ty::tls::with(|tcx| {
            crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
                tcx,
                rustc_internal::internal(tcx, def.def_id()),
                &["raw_vec", "RawVec"],
            )
        })
    }

    fn native_vec_ty(ty: Ty) -> Option<(AdtDef, GenericArgs)> {
        match ty.kind() {
            TyKind::RigidTy(RigidTy::Adt(def, args)) if Self::is_native_vec_adt(def) => {
                Some((def, args))
            }
            _ => None,
        }
    }

    fn native_header_owner_ty(ty: Ty) -> bool {
        matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _))
            if Self::is_native_vec_adt(def) || Self::is_native_string_adt(def))
    }

    fn native_header_declared_field(ty: Ty, index: usize) -> Option<Ty> {
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
        let variants = def.variants();
        let [variant] = variants.as_slice() else { return None };
        let fields = variant.fields();
        let field = fields.get(index)?;
        let actual = crate::codegen_ay::shared::mono_ty::field_ty(field, &args)?;
        // These are roles within authenticated library definitions. A foreign
        // spelling, a cached projected value, or a model sort grants no type.
        if Self::is_native_string_adt(def) && field.name.as_str() == "vec" {
            let (_, args) = Self::native_vec_ty(actual)?;
            return matches!(args.0.first(), Some(rustc_public::ty::GenericArgKind::Type(t))
                if matches!(t.kind(), TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::U8))))
            .then_some(actual);
        }
        if Self::is_native_vec_adt(def)
            && field.name.as_str() == "buf"
            && matches!(actual.kind(), TyKind::RigidTy(RigidTy::Adt(raw, _)) if Self::is_native_rawvec_adt(raw))
        {
            return Some(actual);
        }
        None
    }

    fn native_header_target_ty(&self, target: &HeaderTarget) -> Option<Ty> {
        if target.fields.len() > 2 {
            return None;
        }
        let mut ty = self.body.locals().get(target.owner)?.ty;
        if !Self::native_header_owner_ty(ty) {
            return None;
        }
        for index in &target.fields {
            ty = Self::native_header_declared_field(ty, *index)?;
        }
        Some(ty)
    }

    fn native_header_field_target(
        &self,
        mut target: HeaderTarget,
        fields: &[ProjectionElem],
        work: &mut usize,
    ) -> Option<HeaderTarget> {
        for field in fields {
            *work = work.checked_sub(1)?;
            let ProjectionElem::Field(index, declared) = field else { return None };
            if target.fields.len() >= 2
                || Self::native_header_declared_field(
                    self.native_header_target_ty(&target)?,
                    *index,
                )? != *declared
            {
                return None;
            }
            target.fields.push(*index);
        }
        Some(target)
    }

    // One budget covers every scanned block, statement and terminator through
    // the complete chain. No joins, carrier retargets, exposed slots or casts.
    fn native_vec_reference_target(
        &mut self,
        local: usize,
        work: &mut usize,
        seen: &mut Vec<usize>,
    ) -> Option<HeaderTarget> {
        *work = work.checked_sub(1)?;
        if seen.len() >= 32
            || seen.contains(&local)
            || self.stack_local_is_live(local) != Some(true)
        {
            return None;
        }
        seen.push(local);
        let TyKind::RigidTy(RigidTy::Ref(_, pointee, capability)) =
            self.body.locals().get(local)?.ty.kind()
        else {
            return None;
        };
        let mut definition = None;
        for block in &self.body.blocks {
            *work = work.checked_sub(1)?;
            for statement in &block.statements {
                *work = work.checked_sub(1)?;
                let StatementKind::Assign(lhs, rhs) = &statement.kind else { continue };
                if let Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place) = rhs
                    && place.local == local
                    && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
                {
                    return None;
                }
                if lhs.local == local {
                    *work = work.checked_sub(lhs.projection.len())?;
                }
                if lhs.local == local
                    && !lhs.projection.iter().any(|p| matches!(p, ProjectionElem::Deref))
                {
                    if !lhs.projection.is_empty() || definition.is_some() {
                        return None;
                    }
                    match rhs {
                        Rvalue::Use(Operand::Copy(place) | Operand::Move(place), ..)
                        | Rvalue::CopyForDeref(place)
                            if place.projection.is_empty() => {}
                        Rvalue::Ref(_, _, place) | Rvalue::AddressOf(_, place)
                            if place.projection.len() <= 2 => {}
                        _ => return None,
                    }
                    definition = Some(rhs.clone());
                }
            }
            *work = work.checked_sub(1)?;
            if let TerminatorKind::Call { destination, .. } = &block.terminator.kind
                && destination.local == local
            {
                return None;
            }
        }
        let definition = definition?;
        if capability == rustc_public::mir::Mutability::Mut
            && (matches!(&definition, Rvalue::Ref(_, BorrowKind::Shared, _))
                || matches!(
                    &definition,
                    Rvalue::AddressOf(rustc_public::mir::RawPtrKind::Const, _)
                ))
        {
            return None;
        }
        let target = match definition {
            Rvalue::Use(Operand::Copy(source) | Operand::Move(source), ..)
            | Rvalue::CopyForDeref(source)
                if source.projection.is_empty() =>
            {
                let TyKind::RigidTy(RigidTy::Ref(_, source_pointee, source_capability)) =
                    self.body.locals().get(source.local)?.ty.kind()
                else {
                    return None;
                };
                if source_pointee != pointee
                    || (capability == rustc_public::mir::Mutability::Mut
                        && source_capability != capability)
                {
                    return None;
                }
                self.native_vec_reference_target(source.local, work, seen)?
            }
            Rvalue::Ref(_, BorrowKind::Shared | BorrowKind::Mut { .. }, source)
            | Rvalue::AddressOf(_, source) => {
                let (target, tail) = if let Some(ProjectionElem::Deref) = source.projection.first()
                {
                    let TyKind::RigidTy(RigidTy::Ref(_, source_pointee, source_capability)) =
                        self.body.locals().get(source.local)?.ty.kind()
                    else {
                        return None;
                    };
                    if capability == rustc_public::mir::Mutability::Mut
                        && source_capability != capability
                    {
                        return None;
                    }
                    let target = self.native_vec_reference_target(source.local, work, seen)?;
                    if self.native_header_target_ty(&target)? != source_pointee {
                        return None;
                    }
                    (target, &source.projection[1..])
                } else {
                    let owner_ty = self.body.locals().get(source.local)?.ty;
                    if !Self::native_header_owner_ty(owner_ty)
                        || self.stack_local_is_live(source.local) != Some(true)
                    {
                        return None;
                    }
                    (
                        HeaderTarget { owner: source.local, fields: Vec::new() },
                        source.projection.as_slice(),
                    )
                };
                self.native_header_field_target(target, tail, work)?
            }
            _ => return None,
        };
        if self.native_header_target_ty(&target)? != pointee {
            return None;
        }
        // The actual typed producer fixes this key; never parse a key to infer
        // a Rust type or choose an owner, and never consult a durable snapshot.
        let mut expected =
            crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), target.owner);
        for index in &target.fields {
            expected = crate::codegen_ay::names::indexed_field_name(&expected, *index);
        }
        let reference = self.ssa_base_name(&Place { local, projection: Vec::new() });
        if self.ref_pointees.is_poisoned(reference.as_str()) {
            return None;
        }
        self.ref_pointees
            .get(reference.as_str())
            .is_some_and(|actual| actual.as_ref() == expected)
            .then_some(target)
    }

    #[cfg(all(test, trust_toolchain))]
    fn current_native_vec_value(&self, owner: usize) -> Option<Expr> {
        Self::native_vec_ty(self.body.locals().get(owner)?.ty)?;
        self.current_native_header_value(&HeaderTarget { owner, fields: Vec::new() })
    }

    fn current_native_header_value(&self, target: &HeaderTarget) -> Option<Expr> {
        if self.stack_local_is_live(target.owner) != Some(true) {
            return None;
        }
        let mut ty = self.body.locals().get(target.owner)?.ty;
        if !Self::native_header_owner_ty(ty)
            || crate::codegen_ay::shared::mono_ty::has_unresolved_params(ty)
            || target.fields.len() > 2
        {
            return None;
        }
        let base = crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), target.owner);
        let mut value = self.env_lookup(&base)?.clone();
        if value.sort() != &Self::infer_sort_from_ty(ty)? {
            return None;
        }
        for index in &target.fields {
            let next = Self::native_header_declared_field(ty, *index)?;
            let sort = Self::infer_sort_from_ty(next)?;
            let from = value.sort().datatype_name()?.to_owned();
            let name = sort.datatype_name()?.to_owned();
            let ctor = crate::codegen_ay::names::resolve_ctor_name(&sort, &name);
            let values = if Self::native_vec_ty(next).is_some() {
                let data_sort = ay_bindings::Sort::array(
                    crate::codegen_ay::types::ptr_sort(),
                    crate::codegen_ay::types::bv8_sort(),
                );
                vec![
                    value.clone().field_select(
                        &from,
                        "fld_ptr",
                        crate::codegen_ay::types::ptr_sort(),
                    ),
                    value.clone().field_select(
                        &from,
                        "fld_len",
                        crate::codegen_ay::types::ptr_sort(),
                    ),
                    value.clone().field_select(
                        &from,
                        "fld_cap",
                        crate::codegen_ay::types::ptr_sort(),
                    ),
                    value.field_select(&from, "fld_data", data_sort),
                ]
            } else {
                vec![
                    value.clone().field_select(
                        &from,
                        "fld_ptr",
                        crate::codegen_ay::types::ptr_sort(),
                    ),
                    value.field_select(&from, "fld_cap", crate::codegen_ay::types::ptr_sort()),
                ]
            };
            value = Expr::datatype_constructor(name, ctor, values, sort);
            ty = next;
        }
        Some(value)
    }

    /// `Some(None)` refuses an actual native field whose custody is missing;
    /// generic positional projection must not reinterpret its flattened model.
    pub(super) fn native_vec_field_place(&mut self, place: &Place) -> Option<Option<Expr>> {
        let local_ty = self.body.locals().get(place.local)?.ty;
        let (owner_ty, tail, through_ref) = match place.projection.as_slice() {
            [ProjectionElem::Deref, tail @ ..] if !tail.is_empty() => {
                let TyKind::RigidTy(RigidTy::Ref(_, owner, _)) = local_ty.kind() else {
                    return None;
                };
                (owner, tail, true)
            }
            fields if !fields.is_empty() => (local_ty, fields, false),
            _ => return None,
        };
        if !Self::native_header_owner_ty(owner_ty) || tail.len() > 2 {
            return None;
        }
        let mut declared = owner_ty;
        for field in tail {
            let ProjectionElem::Field(index, _) = field else {
                return None;
            };
            declared = Self::native_header_declared_field(declared, *index)?;
        }
        let result = (|| {
            let mut work = 4096;
            let target = if through_ref {
                let target =
                    self.native_vec_reference_target(place.local, &mut work, &mut Vec::new())?;
                if self.native_header_target_ty(&target)? != owner_ty {
                    return None;
                }
                target
            } else {
                HeaderTarget { owner: place.local, fields: Vec::new() }
            };
            let target = self.native_header_field_target(target, tail, &mut work)?;
            if self.native_header_target_ty(&target)? != declared {
                return None;
            }
            self.current_native_header_value(&target)
        })();
        if result.is_none() {
            self.ctx.unsupported_with_fallback("native_vec_field_custody", format!("{place:?}"));
        }
        Some(result)
    }

    pub(super) fn native_rawvec_ptr_from_reference(&mut self, arg: &Operand) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = arg else {
            return None;
        };
        if !place.projection.is_empty() {
            return None;
        }
        let TyKind::RigidTy(RigidTy::Ref(_, rawvec_ty, _)) =
            arg.ty(self.body.locals()).into_option()?.kind()
        else {
            return None;
        };
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = rawvec_ty.kind() else {
            return None;
        };
        if !Self::is_native_rawvec_adt(def) {
            return None;
        }
        let target = self.native_vec_reference_target(place.local, &mut 4096, &mut Vec::new())?;
        if target.fields.is_empty() || self.native_header_target_ty(&target)? != rawvec_ty {
            return None;
        }
        let value = self.current_native_header_value(&target)?;
        let name = value.sort().datatype_name()?.to_owned();
        Some(value.field_select(&name, "fld_ptr", crate::codegen_ay::types::ptr_sort()))
    }

    /// The registry's text match is only a candidate. Grant this consumer to
    /// the resolved inherent sysroot method, never a same-spelled foreign one.
    pub(super) fn native_rawvec_ptr_call(&self, func: &Operand) -> bool {
        (|| {
            if self.ctx.unit_has_stubs() { return None; }
            let ty = func.ty(self.body.locals()).into_option()?;
            if crate::codegen_ay::shared::mono_ty::has_unresolved_params(ty) { return None; }
            let TyKind::RigidTy(RigidTy::FnDef(original, args)) = ty.kind() else { return None };
            let instance = rustc_public::mir::mono::Instance::resolve(original, &args).ok()?;
            if matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. }) { return None; }
            let tcx = self.ctx.tcx;
            let id = rustc_internal::internal(tcx, instance.def.def_id());
            if id != rustc_internal::internal(tcx, original.def_id())
                || !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition(tcx, id)
                || tcx.item_name(id).as_str() != "ptr"
            { return None; }
            let implementation = tcx.parent(id);
            if !matches!(tcx.def_kind(implementation), rustc_hir::def::DefKind::Impl { .. })
                || crate::rustc_compat::impl_opt_trait_ref(tcx, implementation).is_some()
            { return None; }
            let signature = instance.ty().kind().fn_sig()?.skip_binder();
            let [input] = signature.inputs() else { return None };
            let TyKind::RigidTy(RigidTy::Ref(_, owner, rustc_public::mir::Mutability::Not)) = input.kind()
            else { return None };
            let TyKind::RigidTy(RigidTy::Adt(def, owner_args)) = owner.kind() else { return None };
            if !Self::is_native_rawvec_adt(def) { return None; }
            let owner_id = rustc_internal::internal(tcx, def.def_id());
            let self_ty = crate::rustc_compat::skip_normalization(tcx.type_of(implementation).instantiate_identity());
            if !matches!(self_ty.kind(), rustc_middle::ty::Adt(actual, _) if actual.did() == owner_id) { return None; }
            let Some(rustc_public::ty::GenericArgKind::Type(element)) = owner_args.0.first() else { return None };
            matches!(signature.output().kind(), TyKind::RigidTy(RigidTy::RawPtr(actual, rustc_public::mir::Mutability::Mut)) if actual == *element)
                .then_some(())
        })().is_some()
    }
}

#[cfg(all(test, trust_toolchain))]
fn native_header_test_flags() -> Vec<String> {
    let sdk = std::path::PathBuf::from(
        std::env::var_os("TRUST_MC_NATIVE_VEC_SDK")
            .expect("attested bundled std MIR is required for this native consumer control"),
    );
    assert!(
        sdk.join("lib/libkani.rlib").is_file()
            && sdk.join("lib/libstd.rlib").is_file()
            && sdk.join("lib/rustlib").is_dir()
    );
    let flags = [
        "-Cpanic=abort".to_owned(),
        "-Zunstable-options".to_owned(),
        "-Zinline-mir=no".to_owned(),
        "-Zmir-enable-passes=-RemoveStorageMarkers".to_owned(),
        "--cfg=kani".to_owned(),
        "--cfg=trust_mc".to_owned(),
        format!("--sysroot={}", sdk.display()),
        format!("--extern=kani={}", sdk.join("lib/libkani.rlib").display()),
        format!("--extern=noprelude:std={}", sdk.join("lib/libstd.rlib").display()),
        format!("-Ldependency={}", sdk.join("lib").display()),
    ];
    flags.into_iter().collect()
}

#[cfg(all(test, trust_toolchain))]
#[path = "native_string_field_tests.rs"]
mod string_tests;

#[cfg(all(test, trust_toolchain))]
mod tests {
    use super::*;
    use crate::callee_body::CalleeBody;
    use crate::codegen_ay::context::with_test_ay_ctx_for_external_source;
    use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
    use crate::kani_middle::std_abstraction::StdAbstraction;
    use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
    use crate::kani_middle::tuple_usage::TupleUsageAnalysis;
    use ay_bindings::ExprValue;
    use rustc_public::mir::Body;
    use std::sync::{
        Arc,
        atomic::{AtomicBool, Ordering},
    };

    const SOURCE: &str = r#"
#![allow(dead_code, unused_assignments)]
extern crate external_vec_lookalike;
use external_vec_lookalike::LibraryVec as Vec;
pub fn owned_safe() { let v=Vec::from([3u64]); let _pointer=v.as_ptr(); assert!(v.len() == 1); }
pub fn owned_bug() { let v=Vec::from([3u64]); let _pointer=v.as_ptr(); assert!(v.len() == 2); }
pub fn retargeted() {
    let mut a=Vec::from([3u64]); let mut b=Vec::from([4u64]);
    let mut r=&mut a; r=&mut b;
    let _pointer=r.as_ptr();
    unsafe { std::ptr::drop_in_place(r); }
    std::mem::forget(a); std::mem::forget(b);
}
pub fn exposed() {
    let mut a=Vec::from([3u64]); let mut b=Vec::from([4u64]);
    let mut r=&mut a; let slot=&raw mut r;
    unsafe { *slot=&mut b; } let _pointer=r.as_ptr();
    unsafe { std::ptr::drop_in_place(r); }
    std::mem::forget(a); std::mem::forget(b);
}
pub fn raw_derived() {
    let mut a=Vec::from([3u64]); let p=&raw mut a;
    let r=unsafe { &mut *p }; let _pointer=r.as_ptr();
    unsafe { std::ptr::drop_in_place(r); }
    std::mem::forget(a);
}
mod foreign {
    pub struct RawVec { pub ptr:*mut u64, pub cap:usize }
    impl RawVec { #[inline(never)] pub fn ptr(&self)->*mut u64 { self.ptr } }
    pub struct Vec { pub buf:RawVec, pub len:usize }
    pub trait Ptr { fn ptr(&self)->*mut u64; }
    impl Ptr for std::vec::Vec<u64> { fn ptr(&self)->*mut u64 { std::ptr::null_mut() } }
}
pub fn foreign_inherent(v:&foreign::RawVec)->*mut u64 { v.ptr() }
pub fn foreign_trait(v:&Vec<u64>)->*mut u64 { foreign::Ptr::ptr(v) }
pub fn foreign_field(v:&foreign::Vec)->&foreign::RawVec { &v.buf }
"#;

    fn context(
        callback: impl for<'tcx> FnOnce(crate::codegen_ay::context::AYCtx<'tcx, 'static>) + Send,
    ) {
        let flags = native_header_test_flags();
        let flags: Vec<_> = flags.iter().map(String::as_str).collect();
        let completed = Arc::new(AtomicBool::new(false));
        let observed = Arc::clone(&completed);
        with_test_ay_ctx_for_external_source(
            "pub use std::vec::Vec as LibraryVec;",
            SOURCE,
            &flags,
            move |ctx| {
                callback(ctx);
                observed.store(true, Ordering::SeqCst);
            },
        );
        assert!(completed.load(Ordering::SeqCst), "actual compiler callback must complete");
    }

    fn transformed(
        ctx: &crate::codegen_ay::context::AYCtx<'_, '_>,
        suffix: &str,
    ) -> (rustc_public::mir::mono::Instance, Body) {
        let instance = find_instance_by_suffix(ctx.tcx, suffix);
        let abstraction = StdAbstraction::resolve(ctx.tcx);
        let (_, body) = FunctionInlinePass::new(InlineConfig {
            max_depth: ctx.config.inline_depth,
            enabled: ctx.config.function_inlining,
            preserve_block_on: false,
            preserve_array_comparisons: false,
            bmc_native_box_validity: true,
            chc_native_box_drop: false,
        })
        .transform_with_body_provider(
            ctx.tcx,
            instance.callee_body().unwrap(),
            instance,
            |callee| {
                if abstraction.abstracts_public_instance(ctx.tcx, callee) {
                    None
                } else {
                    callee.callee_body()
                }
            },
        );
        if let Some(directory) = std::env::var_os("MC_VEC_APPEND_ARTIFACT_DIR") {
            std::fs::write(
                std::path::Path::new(&directory).join(format!("native-vec-consumer-{suffix}.mir")),
                format!("{body:#?}"),
            )
            .expect("retain actual transformed Vec consumer MIR");
        }
        (instance, body)
    }

    #[test]
    #[ignore = "requires an attested bundled TRUST_MC_NATIVE_VEC_SDK; run explicitly with --ignored"]
    fn actual_native_vec_fields_and_ptr_use_current_owner_keep_constructor_debt() {
        context(|mut ctx| {
            ctx.init_memory();
            for (suffix, expected) in [
                ("owned_safe", "assertion failed: v.len() == 1"),
                ("owned_bug", "assertion failed: v.len() == 2"),
            ] {
                let (instance, body) = transformed(&ctx, suffix);
                ctx.set_current_fn(instance);
                let name = ctx.current_fn_name().to_owned();
                let (order, reachable) =
                    crate::codegen_ay::codegen_function::native_test_compute_topo(&body);
                assert_eq!(order.len(), reachable, "actual fixture must remain acyclic");
                let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                let (mut fields, mut calls, mut expired, mut refused_calls) = (0, 0, 0, 0);
                let mut witnessed = Vec::new();
                for bb in order {
                    cg.initialize_block_entry_env(bb);
                    for statement in &body.blocks[bb].statements {
                        cg.codegen_statement(statement);
                        if let StatementKind::Assign(_, Rvalue::Ref(_, _, place)) = &statement.kind
                            && let Some(Some(value)) = cg.native_vec_field_place(place)
                            && let TyKind::RigidTy(RigidTy::Adt(def, _)) =
                                place.ty(body.locals()).unwrap().kind()
                            && StatementCodegen::is_native_rawvec_adt(def)
                        {
                            let ExprValue::DatatypeConstructor { args, .. } = value.value() else {
                                panic!("typed RawVec view")
                            };
                            assert_eq!(args.len(), 2);
                            let owner = cg
                                .native_vec_reference_target(
                                    place.local,
                                    &mut 4096,
                                    &mut Vec::new(),
                                )
                                .unwrap()
                                .owner;
                            let current = cg.current_native_vec_value(owner).unwrap();
                            let model = current.sort().datatype_name().unwrap().to_owned();
                            assert_eq!(
                                args[0],
                                current.clone().field_select(
                                    &model,
                                    "fld_ptr",
                                    crate::codegen_ay::types::ptr_sort()
                                )
                            );
                            assert_eq!(
                                args[1],
                                current.field_select(
                                    &model,
                                    "fld_cap",
                                    crate::codegen_ay::types::ptr_sort()
                                )
                            );
                            assert_eq!(
                                value.sort(),
                                &StatementCodegen::infer_sort_from_ty(
                                    place.ty(body.locals()).unwrap()
                                )
                                .unwrap()
                            );
                            witnessed.push(owner);
                            fields += 1;
                        }
                        if let StatementKind::StorageDead(owner) = statement.kind {
                            for witnessed_owner in &witnessed {
                                // Check only the actual expired owning Vec, not a dead temporary reference.
                                if owner == *witnessed_owner {
                                    assert_eq!(cg.stack_local_is_live(owner), Some(false));
                                    assert!(cg.current_native_vec_value(owner).is_none());
                                    expired += 1;
                                }
                            }
                        }
                    }
                    let term = &body.blocks[bb].terminator;
                    if let TerminatorKind::Call { func, args, .. } = &term.kind
                        && cg.native_rawvec_ptr_call(func)
                    {
                        assert_eq!(args.len(), 1);
                        let (Operand::Copy(place) | Operand::Move(place)) = &args[0] else {
                            panic!("actual receiver")
                        };
                        if let Some(target) =
                            cg.native_vec_reference_target(place.local, &mut 4096, &mut Vec::new())
                        {
                            let current = cg.current_native_vec_value(target.owner).unwrap();
                            let model = current.sort().datatype_name().unwrap().to_owned();
                            let expected = current.field_select(
                                &model,
                                "fld_ptr",
                                crate::codegen_ay::types::ptr_sort(),
                            );
                            assert_eq!(
                                cg.native_rawvec_ptr_from_reference(&args[0]),
                                Some(expected)
                            );
                            // Missing/retargeted cache state grants no custody, even with the same actual FnDef.
                            let key = cg.ssa_base_name(place);
                            let saved = cg.ref_pointees.clone();
                            assert_eq!(cg.ref_pointees.forget_rooted_at(key.as_str()), 1);
                            assert!(cg.native_rawvec_ptr_from_reference(&args[0]).is_none());
                            cg.ref_pointees.insert(key.clone().into(), "unknown_owner".into());
                            assert!(cg.native_rawvec_ptr_from_reference(&args[0]).is_none());
                            cg.ref_pointees = saved;
                            let saved = cg.ref_pointees.clone();
                            let generation = cg.ref_pointees.generation();
                            cg.ref_pointees.poison_stale_since(key.as_str(), generation);
                            assert!(
                                cg.native_rawvec_ptr_from_reference(&args[0]).is_none(),
                                "poisoned paths refuse"
                            );
                            cg.ref_pointees = saved;
                            assert!(
                                cg.native_vec_reference_target(
                                    place.local,
                                    &mut 0,
                                    &mut Vec::new()
                                )
                                .is_none(),
                                "bounded work refuses"
                            );
                            calls += 1;
                        } else {
                            assert!(
                                cg.native_rawvec_ptr_from_reference(&args[0]).is_none(),
                                "a separate raw-derived drop path grants no typed custody"
                            );
                            refused_calls += 1;
                        }
                    }
                    let successors = cg.codegen_terminator_with_successors(term);
                    if let TerminatorKind::Call { destination, .. } = &term.kind {
                        cg.forget_joined_ref_pointees(destination);
                    }
                    for (target, condition) in successors {
                        cg.record_outgoing_edge(target, condition);
                    }
                }
                eprintln!(
                    "actual Vec consumer sites: {suffix}: fields={fields} calls={calls} expired={expired} refused_calls={refused_calls}"
                );
                assert!(
                    fields > 0 && calls > 0 && expired > 0,
                    "actual private field/ptr/expiration sites must execute"
                );
                assert!(
                    cg.ctx.bmc_vc.violations.iter().any(|v| v.message.as_deref() == Some(expected)),
                    "exact source assertion remains encoded"
                );
                drop(cg);
                let debt = crate::codegen_ay::chc::take_sound_havoc_drop_by_fn();
                assert!(
                    debt.get(&name).copied().unwrap_or(0) > 0,
                    "constructor/slice debt cannot be cleared"
                );
            }
        });
    }

    #[test]
    #[ignore = "requires an attested bundled TRUST_MC_NATIVE_VEC_SDK; run explicitly with --ignored"]
    fn actual_native_vec_ref_consumers_refuse_retarget_exposure_and_raw_sources() {
        context(|mut ctx| {
            ctx.init_memory();
            for suffix in ["retargeted", "exposed", "raw_derived"] {
                let (instance, body) = transformed(&ctx, suffix);
                ctx.set_current_fn(instance);
                let (order, reachable) =
                    crate::codegen_ay::codegen_function::native_test_compute_topo(&body);
                assert_eq!(order.len(), reachable);
                let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                let mut calls = 0;
                let mut source_refusals = 0;
                for bb in order {
                    cg.initialize_block_entry_env(bb);
                    for statement in &body.blocks[bb].statements {
                        cg.codegen_statement(statement);
                        if let StatementKind::Assign(lhs, rhs) = &statement.kind
                            && lhs.projection.is_empty()
                            && let TyKind::RigidTy(RigidTy::Ref(_, owner, _)) =
                                body.locals()[lhs.local].ty.kind()
                            && StatementCodegen::native_vec_ty(owner).is_some()
                        {
                            let witnessed = match suffix {
                                "retargeted" => body.blocks.iter().flat_map(|b| &b.statements).filter(|s|
                                    matches!(&s.kind, StatementKind::Assign(p, _) if p.local == lhs.local && p.projection.is_empty())).count() > 1,
                                "exposed" => body.blocks.iter().flat_map(|b| &b.statements).any(|s|
                                    matches!(&s.kind, StatementKind::Assign(_, Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p))
                                        if p.local == lhs.local && p.projection.is_empty())),
                                "raw_derived" => matches!(rhs, Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p)
                                    if p.projection.first() == Some(&ProjectionElem::Deref)
                                        && matches!(body.locals()[p.local].ty.kind(), TyKind::RigidTy(RigidTy::RawPtr(..)))),
                                _ => false,
                            };
                            if witnessed {
                                assert!(
                                    cg.native_vec_reference_target(
                                        lhs.local,
                                        &mut 4096,
                                        &mut Vec::new()
                                    )
                                    .is_none(),
                                    "actual source carrier: {suffix}"
                                );
                                source_refusals += 1;
                            }
                        }
                    }
                    let term = &body.blocks[bb].terminator;
                    if let TerminatorKind::Call { func, args, .. } = &term.kind
                        && cg.native_rawvec_ptr_call(func)
                    {
                        assert_eq!(args.len(), 1);
                        assert!(
                            cg.native_rawvec_ptr_from_reference(&args[0]).is_none(),
                            "{suffix}"
                        );
                        calls += 1;
                    }
                    let successors = cg.codegen_terminator_with_successors(term);
                    if let TerminatorKind::Call { destination, .. } = &term.kind {
                        cg.forget_joined_ref_pointees(destination);
                    }
                    for (target, condition) in successors {
                        cg.record_outgoing_edge(target, condition);
                    }
                }
                eprintln!(
                    "actual Vec consumer refusal sites: {suffix}: calls={calls} source_refusals={source_refusals}"
                );
                assert!(calls > 0, "actual private RawVec::ptr refusal site required: {suffix}");
                assert!(
                    source_refusals > 0,
                    "actual retarget/exposure/raw producer required: {suffix}"
                );
            }
        });
    }

    #[test]
    #[ignore = "requires an attested bundled TRUST_MC_NATIVE_VEC_SDK; run explicitly with --ignored"]
    fn actual_native_rawvec_call_rejects_foreign_methods_and_attached_stubs() {
        context(|mut ctx| {
            let mut foreign_calls = 0;
            let mut replacement = None;
            for suffix in ["foreign_inherent", "foreign_trait"] {
                let instance = find_instance_by_suffix(ctx.tcx, suffix);
                let body = instance.callee_body().unwrap();
                ctx.set_current_fn(instance);
                let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                for block in &body.blocks {
                    if let TerminatorKind::Call { func, .. } = &block.terminator.kind {
                        assert!(!cg.native_rawvec_ptr_call(func));
                        let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
                            func.ty(body.locals()).unwrap().kind()
                        else {
                            panic!("actual foreign FnDef")
                        };
                        replacement = Some(def);
                        foreign_calls += 1;
                    }
                }
            }
            assert_eq!(foreign_calls, 2);
            let instance = find_instance_by_suffix(ctx.tcx, "foreign_field");
            let body = instance.callee_body().unwrap();
            ctx.set_current_fn(instance);
            let mut cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let mut fields = 0;
            for block in &body.blocks {
                for statement in &block.statements {
                    if let StatementKind::Assign(_, Rvalue::Ref(_, _, place)) = &statement.kind {
                        assert!(
                            cg.native_vec_field_place(place).is_none(),
                            "foreign fields never select native views"
                        );
                        fields += 1;
                    }
                }
            }
            assert!(fields > 0);
            drop(cg);
            let (instance, body) = transformed(&ctx, "owned_safe");
            ctx.set_current_fn(instance);
            let actual: Vec<_> = body
                .blocks
                .iter()
                .filter_map(|block| {
                    let TerminatorKind::Call { func, .. } = &block.terminator.kind else {
                        return None;
                    };
                    let cg = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
                    cg.native_rawvec_ptr_call(func).then_some(func.clone())
                })
                .collect();
            assert!(!actual.is_empty(), "actual native FnDef is required");
            for func in actual {
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
                    func.ty(body.locals()).unwrap().kind()
                else {
                    unreachable!()
                };
                let mut transformer =
                    crate::kani_middle::transform::BodyTransformation::new_for_tests_with_stubs(
                        std::collections::HashMap::from([(def, replacement.unwrap())]),
                    );
                let mut replaced = crate::codegen_ay::context::AYCtx::new(
                    ctx.tcx,
                    crate::kani_queries::QueryDb::default(),
                    crate::codegen_ay::context::AYConfig { use_chc: false, ..Default::default() },
                    &mut transformer,
                );
                replaced.set_current_fn(instance);
                assert!(
                    !crate::kani_middle::transform::unit_has_stubs(),
                    "BMC transformer, no CHC TLS"
                );
                assert!(replaced.unit_has_stubs());
                let cg =
                    StatementCodegen::new(&mut replaced, &body, TupleUsageAnalysis::run(&body));
                assert!(!cg.native_rawvec_ptr_call(&func));
            }
        });
    }
}
