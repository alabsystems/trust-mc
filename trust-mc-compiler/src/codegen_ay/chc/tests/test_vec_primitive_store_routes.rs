// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Native controls. No solver calls or new runtime budget knobs.
#![cfg(trust_toolchain)]

use super::super::codegen_ctx::RefTarget;
use super::common::*;
use super::test_trust_box_new::{mem_config, with_native_box_ctx};
use crate::callee_body::CalleeBody;
use crate::kani_middle::std_abstraction::StdAbstraction;
use crate::kani_middle::transform::inline::{FunctionInlinePass, InlineConfig};
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, Ty, TyKind};
use rustc_public::{CrateDef, rustc_internal};

const SOURCE: &str = r#"
#![feature(allocator_api)]
#![allow(dead_code, unused_variables, stable_features)]
use std::alloc::{AllocError, Allocator, Global, Layout};
use std::ptr::NonNull;

pub fn route_u64() {
    let mut values = vec![1u64];
    unsafe { *values.as_mut_ptr() = 9; }
    assert!(unsafe { *values.as_ptr() } == 9);
}
pub fn route_u8() {
    let mut values = vec![1u8];
    unsafe { *values.as_mut_ptr() = 9; }
    assert!(unsafe { *values.as_ptr() } == 9);
}
pub fn route_copied() {
    let mut values = vec![1u8];
    let pointer = values.as_mut_ptr(); let copied = pointer;
    unsafe { *copied = 9; }
    assert!(unsafe { *values.as_ptr() } == 9);
}
#[inline(never)] pub fn route_nine() -> u64 { 9 }
pub fn route_call_destination() {
    let mut values = vec![1u64];
    let pointer = values.as_mut_ptr();
    unsafe { *pointer = route_nine(); }
    assert!(unsafe { *values.as_ptr() } == 9);
}
pub struct Element(pub u8);
impl Drop for Element { fn drop(&mut self) { assert!(self.0 == 3); } }
pub fn route_effectful_element(values: Vec<Element>) {}

pub struct UserAllocator;
unsafe impl Allocator for UserAllocator {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        Global.allocate(layout)
    }
    unsafe fn deallocate(&self, pointer: NonNull<u8>, layout: Layout) {
        unsafe { Global.deallocate(pointer, layout); }
    }
}
pub fn route_custom_allocator(values: Vec<u8, UserAllocator>) {}

mod alloc { pub mod raw_vec {
    pub struct RawVec<T, A>(pub std::marker::PhantomData<T>, pub A);
    impl<T, A> Drop for RawVec<T, A> {
        fn drop(&mut self) { assert!(false); }
    }
} }
pub fn route_fake_rawvec(values: alloc::raw_vec::RawVec<u8, Global>) {}
pub fn route_stub_marker() {}
"#;

fn fixture_owner(tcx: TyCtxt<'_>, body: &Body, name: &str, depth: usize) -> usize {
    // Negative fixtures receive their actual owned value as the sole argument.
    // Its type also supplies the actual compiler-generated Drop glue below.
    if !body.arg_locals().is_empty() {
        assert_eq!(
            body.arg_locals().len(),
            1,
            "one typed fixture owner: {name} depth={depth}: {body:#?}"
        );
        assert!(
            matches!(body.locals()[1].ty.kind(), TyKind::RigidTy(RigidTy::Adt(..))),
            "the incoming negative fixture owns an ADT: {name} depth={depth}"
        );
        return 1;
    }
    // For getter fixtures, recover custody from actual resolved native getter
    // receivers and their unique whole-owner borrow. Debug names are optional
    // metadata and do not identify the MIR value after transformations.
    let mut owners = std::collections::HashSet::new();
    for block in &body.blocks {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else { continue };
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = func.ty(body.locals()).unwrap().kind()
        else {
            continue;
        };
        let instance = Instance::resolve(def, &generics).unwrap();
        let id = rustc_internal::internal(tcx, instance.def.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition(tcx, id)
            || !matches!(tcx.item_name(id).as_str(), "as_ptr" | "as_mut_ptr")
        {
            continue;
        }
        let [Operand::Copy(receiver) | Operand::Move(receiver)] = args.as_slice() else { continue };
        assert!(
            receiver.projection.is_empty(),
            "whole getter receiver: {name} depth={depth}: {body:#?}"
        );
        let TyKind::RigidTy(RigidTy::Ref(_, owner_ty, _)) =
            receiver.ty(body.locals()).unwrap().kind()
        else {
            continue;
        };
        let TyKind::RigidTy(RigidTy::Adt(owner, _)) = owner_ty.kind() else { continue };
        let owner_id = rustc_internal::internal(tcx, owner.def_id());
        if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            tcx,
            owner_id,
            &["vec", "Vec"],
        ) {
            continue;
        }
        let implementation = tcx.parent(id);
        assert!(
            matches!(tcx.def_kind(implementation), rustc_hir::def::DefKind::Impl { .. })
                && crate::rustc_compat::impl_opt_trait_ref(tcx, implementation).is_none(),
            "native inherent getter implementation"
        );
        let self_ty = crate::rustc_compat::skip_normalization(
            tcx.type_of(implementation).instantiate_identity(),
        );
        assert!(
            matches!(self_ty.kind(), rustc_middle::ty::Adt(adt, _) if adt.did() == owner_id),
            "the actual getter belongs to the receiver's Vec definition"
        );
        let mut borrowed = None;
        for source in &body.blocks {
            assert!(
                !matches!(&source.terminator.kind, TerminatorKind::Call { destination, .. }
                if destination.local == receiver.local),
                "getter receiver is a direct unique borrow"
            );
            for statement in &source.statements {
                let StatementKind::Assign(lhs, rhs) = &statement.kind else { continue };
                if lhs.local != receiver.local {
                    continue;
                }
                assert!(
                    lhs.projection.is_empty() && borrowed.is_none(),
                    "unique whole getter receiver definition: {name} depth={depth}: {body:#?}"
                );
                let Rvalue::Ref(_, _, place) = rhs else {
                    panic!("retain a typed getter owner borrow: {name} depth={depth}: {body:#?}");
                };
                borrowed = Some(place);
            }
        }
        let place = borrowed
            .unwrap_or_else(|| panic!("getter owner borrow: {name} depth={depth}: {body:#?}"));
        assert!(
            place.projection.is_empty() && body.locals()[place.local].ty == owner_ty,
            "whole typed native Vec owner: {name} depth={depth}: {body:#?}"
        );
        owners.insert(place.local);
    }
    assert_eq!(
        owners.len(),
        1,
        "one actual getter owner: {name} depth={depth}: owners={owners:?}; MIR={body:#?}"
    );
    *owners.iter().next().unwrap()
}

fn native_backing(tcx: TyCtxt<'_>, ty: Ty) -> Option<Ty> {
    let TyKind::RigidTy(RigidTy::Adt(def, args)) = ty.kind() else { return None };
    if !crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
        tcx,
        rustc_internal::internal(tcx, def.def_id()),
        &["vec", "Vec"],
    ) {
        return None;
    }
    def.variants().into_iter().flat_map(|v| v.fields()).find_map(|field| {
        let ty = crate::codegen_ay::shared::mono_ty::field_ty(&field, &args)?;
        let TyKind::RigidTy(RigidTy::Adt(def, _)) = ty.kind() else { return None };
        crate::kani_middle::std_abstraction::is_sysroot_alloc_definition_at(
            tcx,
            rustc_internal::internal(tcx, def.def_id()),
            &["raw_vec", "RawVec"],
        )
        .then_some(ty)
    })
}

// Expand the actual compiler-produced Vec/RawVec drop glue while retaining
// their actual Drop::drop Calls. The ordinary helper stops at VecDrop and did
// not exercise the production-style backing-drop Call. No private type is
// forged from a printed name; the glue comes from the actual owner field type.
fn body_with_backing_drop_calls(tcx: TyCtxt<'_>, name: &str, depth: usize) -> (Body, usize) {
    let instance = find_instance_by_suffix(tcx, name);
    let body = instance.callee_body().unwrap();
    let owner = fixture_owner(tcx, &body, name, depth);
    let owner_ty = body.locals()[owner].ty;
    let mut glue = vec![Instance::resolve_drop_in_place(owner_ty)];
    if let Some(backing) = native_backing(tcx, owner_ty) {
        glue.push(Instance::resolve_drop_in_place(backing));
    }
    let opaque_nine = find_instance_by_suffix(tcx, "route_nine").def.def_id();
    let abstraction = StdAbstraction::resolve(tcx);
    let (_, transformed) = FunctionInlinePass::new(InlineConfig {
        max_depth: depth,
        chc_native_box_drop: true,
        ..InlineConfig::default()
    })
    .transform_with_body_provider(tcx, body, instance, |callee| {
        if glue.iter().any(|actual| actual.def == callee.def) {
            callee.callee_body()
        } else {
            let id = rustc_internal::internal(tcx, callee.def.def_id());
            if tcx.item_name(id).as_str() == "drop"
                || callee.def.def_id() == opaque_nine
                || abstraction.abstracts_public_instance(tcx, callee)
            {
                None
            } else {
                callee.callee_body()
            }
        }
    });
    assert_eq!(
        transformed.locals()[owner].ty,
        owner_ty,
        "inlining retains the selected actual owner slot: {name} depth={depth}"
    );
    (transformed, owner)
}

fn assert_positive_custody(tcx: TyCtxt<'_>, body: &Body, owner: usize, name: &str) {
    let expected = RefTarget::with_projections(owner, Vec::new());
    let context = ChcCtx::new(tcx, body, name, mem_config());
    let mut sites = 0;
    for block in &body.blocks {
        for statement in &block.statements {
            let StatementKind::Assign(lhs, _) = &statement.kind else { continue };
            if lhs.projection.as_slice() != [ProjectionElem::Deref] {
                continue;
            }
            let TyKind::RigidTy(RigidTy::RawPtr(element, _)) = body.locals()[lhs.local].ty.kind()
            else {
                continue;
            };
            if !matches!(element.kind(), TyKind::RigidTy(RigidTy::Uint(_))) {
                continue;
            }
            sites += 1;
            assert_eq!(
                context.native_vec_primitive_store_owner(lhs.local, &expected, element),
                Some(owner),
                "actual pointee store is not a pointer-value writer: {name}: {body:#?}"
            );
        }
    }
    assert!(sites > 0, "retain actual typed Vec pointee writes: {name}");
}

fn assert_retained_drop_calls(tcx: TyCtxt<'_>, body: &Body, name: &str, accepted: bool) {
    let context = ChcCtx::new(tcx, body, name, mem_config());
    let mut raw_calls = 0;
    for block in &body.blocks {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else { continue };
        let TyKind::RigidTy(RigidTy::FnDef(def, generics)) = func.ty(body.locals()).unwrap().kind()
        else {
            continue;
        };
        let instance = Instance::resolve(def, &generics).unwrap();
        let id = rustc_internal::internal(tcx, instance.def.def_id());
        if tcx.item_name(id).as_str() != "drop" {
            continue;
        }
        let owner = tcx.parent(id);
        if !matches!(tcx.def_kind(owner), rustc_hir::def::DefKind::Impl { .. }) {
            continue;
        }
        let self_ty =
            crate::rustc_compat::skip_normalization(tcx.type_of(owner).instantiate_identity());
        let rustc_middle::ty::Adt(adt, _) = self_ty.kind() else { continue };
        if tcx.item_name(adt.did()).as_str() != "RawVec" {
            continue;
        }
        raw_calls += 1;
        assert_eq!(
            context.vec_region_drop_call_has_no_model_observation_for_test(func, args),
            accepted,
            "actual retained RawVec Drop call: {name}: {instance:?}"
        );
    }
    assert!(
        raw_calls > 0,
        "retain the actual backing Drop Call, not empty coverage: {name}: {body:#?}"
    );
}

#[test]
fn native_vec_pointer_definitions_and_retained_backing_drop_are_precise() {
    with_native_box_ctx(SOURCE, |ctx| {
        for depth in [0, 32] {
            for name in ["route_u64", "route_u8", "route_copied"] {
                let (body, owner) = body_with_backing_drop_calls(ctx.tcx, name, depth);
                assert_positive_custody(ctx.tcx, &body, owner, name);
                // Depth0 need not expand glue; depth32 must retain RawVecDrop.
                if depth == 32 {
                    assert_retained_drop_calls(ctx.tcx, &body, name, true);
                }
                let (vc, _, diagnostics) =
                    ChcCtx::new(ctx.tcx, &body, name, mem_config()).translate_with_diagnostics();
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                    .remove(name)
                    .unwrap_or_default();
                assert!(reasons.is_empty(), "{name} d{depth}: {reasons:?}");
                assert!(
                    vc.approximation_identity_complete,
                    "identity incomplete: {name} depth={depth}: place={} havoc={} reasons={reasons:?}",
                    diagnostics.place_translation_drop.get(),
                    diagnostics.sound_havoc_drop.get()
                );
                assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name} depth={depth}");
                assert_eq!(diagnostics.sound_havoc_drop.get(), 0, "{name} depth={depth}");
            }
        }

        // A valid, typed Call destination can write the pointee too. Move the
        // existing u64 result directly into its sole assignment destination;
        // this fixture is used ONLY for custody, not semantic or UB evidence.
        let (mut body, owner) = body_with_backing_drop_calls(ctx.tcx, "route_call_destination", 32);
        let nine = find_instance_by_suffix(ctx.tcx, "route_nine");
        let (call_bb, temporary) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb, block)| {
                let TerminatorKind::Call { func, destination, .. } = &block.terminator.kind else {
                    return None;
                };
                let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
                    func.ty(body.locals()).ok()?.kind()
                else {
                    return None;
                };
                (Instance::resolve(def, &generics).ok()?.def == nine.def)
                    .then_some((bb, destination.clone()))
            })
            .expect("actual preserved u64 result call");
        let (store_bb, store_si, destination) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb, block)| {
                block.statements.iter().enumerate().find_map(|(si, statement)| {
                    let StatementKind::Assign(
                        lhs,
                        Rvalue::Use(Operand::Copy(value) | Operand::Move(value), ..),
                    ) = &statement.kind
                    else {
                        return None;
                    };
                    (lhs.projection.as_slice() == [ProjectionElem::Deref] && *value == temporary)
                        .then_some((bb, si, lhs.clone()))
                })
            })
            .expect("sole typed result-to-pointee assignment");
        let TerminatorKind::Call { destination: actual, .. } =
            &mut body.blocks[call_bb].terminator.kind
        else {
            unreachable!()
        };
        *actual = destination.clone();
        body.blocks[store_bb].statements.remove(store_si);
        let element = destination.ty(body.locals()).unwrap();
        let context = ChcCtx::new(ctx.tcx, &body, "call_destination_custody", mem_config());
        assert_eq!(
            context.native_vec_primitive_store_owner(
                destination.local,
                &RefTarget::with_projections(owner, Vec::new()),
                element
            ),
            Some(owner)
        );

        for name in ["route_effectful_element", "route_custom_allocator", "route_fake_rawvec"] {
            let (body, _) = body_with_backing_drop_calls(ctx.tcx, name, 32);
            assert_retained_drop_calls(ctx.tcx, &body, name, false);
        }

        let marker = find_instance_by_suffix(ctx.tcx, "route_stub_marker");
        let TyKind::RigidTy(RigidTy::FnDef(marker, _)) = marker.ty().kind() else {
            panic!("marker FnDef")
        };
        let (body, owner) = body_with_backing_drop_calls(ctx.tcx, "route_u8", 32);
        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            std::collections::HashMap::from([(marker, marker)]),
        );
        assert_retained_drop_calls(ctx.tcx, &body, "transitive_stub", false);
        let context = ChcCtx::new(ctx.tcx, &body, "transitive_stub_custody", mem_config());
        let mut denied = 0;
        for block in &body.blocks {
            for statement in &block.statements {
                let StatementKind::Assign(lhs, _) = &statement.kind else { continue };
                if lhs.projection.as_slice() != [ProjectionElem::Deref] {
                    continue;
                }
                let TyKind::RigidTy(RigidTy::RawPtr(element, _)) =
                    body.locals()[lhs.local].ty.kind()
                else {
                    continue;
                };
                if !matches!(element.kind(), TyKind::RigidTy(RigidTy::Uint(_))) {
                    continue;
                }
                denied += 1;
                assert!(
                    context
                        .native_vec_primitive_store_owner(
                            lhs.local,
                            &RefTarget::with_projections(owner, Vec::new()),
                            element
                        )
                        .is_none()
                );
            }
        }
        assert!(denied > 0);
    });
}

#[test]
fn native_vec_backing_drop_does_not_erase_custom_global_allocator_effects() {
    let source = format!(
        r#"
        #![feature(allocator_api)]
        #![allow(dead_code, unused_variables, stable_features)]
        struct UserGlobal;
        unsafe impl std::alloc::GlobalAlloc for UserGlobal {{
            unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {{
                unsafe {{ std::alloc::GlobalAlloc::alloc(&std::alloc::System, layout) }}
            }}
            unsafe fn dealloc(&self, pointer: *mut u8, layout: std::alloc::Layout) {{
                unsafe {{ std::alloc::GlobalAlloc::dealloc(&std::alloc::System, pointer, layout) }}
            }}
        }}
        #[global_allocator] static GLOBAL: UserGlobal = UserGlobal;
        {}
    "#,
        SOURCE
            .replace("#![feature(allocator_api)]", "")
            .replace("#![allow(dead_code, unused_variables, stable_features)]", "")
    );
    with_native_box_ctx(&source, |ctx| {
        assert!(crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(
            ctx.tcx
        ));
        let (body, _) = body_with_backing_drop_calls(ctx.tcx, "route_u8", 32);
        assert_retained_drop_calls(ctx.tcx, &body, "custom_global", false);
    });
}
