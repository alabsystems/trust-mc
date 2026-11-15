// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Host casts must retain the exact native owner and return its UB checks.

use super::common::*;
use crate::callee_body::CalleeBody;
use rustc_public::mir::{
    Body, CastKind, Operand, Place, ProjectionElem, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, Ty};

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub trait Tv { fn get(&self) -> u8; }
    pub struct Value { value: u8, other: u8 }
    impl Tv for Value { fn get(&self) -> u8 { self.value } }
    pub struct Empty;
    impl Tv for Empty { fn get(&self) -> u8 { 0 } }
    pub struct Pointer { pointer: *const u8 }
    impl Tv for Pointer { fn get(&self) -> u8 { unsafe { *self.pointer } } }
    pub fn pointer_type(pointer: *const u8) { std::hint::black_box(pointer); }
    pub fn pointer_oob() -> u8 {
        let bytes = [1u8, 2];
        let owner: Box<dyn Tv> = Box::new(Pointer { pointer: bytes.as_ptr().wrapping_add(2) });
        owner.get()
    }
    pub fn native(value: u8) -> u8 {
        let owner: Box<dyn Tv> = Box::new(Value { value, other: 1 });
        owner.get()
    }
    pub fn copied(value: u8) -> u8 {
        let first: Box<dyn Tv> = Box::new(Value { value, other: 1 });
        let second = first;
        second.get()
    }
    pub fn joined(choose: bool, value: u8) -> u8 {
        let owner: Box<dyn Tv>;
        if choose {
            owner = Box::new(Value { value, other: 1 });
        } else {
            owner = Box::new(Value { value, other: 2 });
        }
        owner.get()
    }
    pub fn exposed(value: u8) -> u8 {
        let mut owner: Box<dyn Tv> = Box::new(Value { value, other: 1 });
        std::hint::black_box(&raw mut owner);
        owner.get()
    }
    pub fn empty() -> u8 {
        let owner: Box<dyn Tv> = Box::new(Empty);
        owner.get()
    }
    pub fn exposed_receiver(value: u8) -> u8 {
        let owner: Box<dyn Tv> = Box::new(Value { value, other: 1 });
        let mut receiver: &dyn Tv = &*owner;
        std::hint::black_box(&raw mut receiver);
        receiver.get()
    }
    pub fn argument_receiver(receiver: &dyn Tv) -> u8 { receiver.get() }
"#;

fn cast(body: &Body) -> (Operand, Ty) {
    body.blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| match &statement.kind {
            StatementKind::Assign(
                _,
                Rvalue::Cast(CastKind::BoxDerefTransmute, operand, target),
            ) => Some((operand.clone(), *target)),
            _ => None,
        })
        .expect("native host Box dereference cast")
}

fn memory_config() -> ChcConfig {
    ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() }
}

fn receiver(body: &Body) -> Operand {
    body.blocks
        .iter()
        .find_map(|block| {
            let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                return None;
            };
            let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
                func.ty(body.locals()).ok()?.kind()
            else {
                return None;
            };
            let instance = rustc_public::mir::mono::Instance::resolve(def, &generics).ok()?;
            matches!(instance.kind, rustc_public::mir::mono::InstanceKind::Virtual { .. })
                .then(|| args.first().cloned())
                .flatten()
        })
        .expect("actual virtual receiver")
}

/// Run the actual allocator operations before requesting their birth facts.
/// No test-created object ID or synthetic pointer grants this authority.
fn allocate(chc: &mut ChcCtx<'_, '_>) {
    let calls: Vec<_> = chc
        .body
        .blocks
        .iter()
        .enumerate()
        .filter_map(|(block, body)| match &body.terminator.kind {
            TerminatorKind::Call { func, args, destination, .. }
                if chc.detect_stub(func) == Some(StubKind::BoxNew) =>
            {
                Some((block, args.clone(), destination.local))
            }
            _ => None,
        })
        .collect();
    for (block, args, destination) in calls {
        chc.current_encode_bb = block;
        chc.heap_state.encode_bb = block;
        let result = chc.translate_alloc_call(StubKind::BoxNew, &args, &HashSet::new()).unwrap();
        chc.record_alloc_dest(destination, result.alloc_obj_id);
        chc.heap_state.reset_modified_arrays();
    }
}

#[test]
fn host_native_dyn_box_cast_authenticates_the_actual_owner_and_projection() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["native", "copied"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (operand, target) = cast(&body);
            let (Operand::Copy(place) | Operand::Move(place)) = &operand else { unreachable!() };
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, memory_config());
            assert!(
                chc.checked_host_native_dyn_box_deref(&operand, target).is_none(),
                "before the allocator operation, there is no birth certificate"
            );
            allocate(&mut chc);
            let owner = Operand::Copy(Place { local: place.local, projection: vec![] });
            let origin = chc
                .host_native_dyn_origin(&owner)
                .unwrap_or_else(|| panic!("{name}: unique native typed origin"));
            let checked = chc
                .checked_host_native_dyn_box_deref(&operand, target)
                .expect("actual host cast retains its allocation authority");
            assert!(!checked.checks.is_empty(), "validity obligations travel with the value");
            assert_eq!(
                ChcCtx::try_extract_constant_addr(&checked.value),
                Some((origin.allocation, 0))
            );
            assert!(chc.checked_host_native_dyn_box_deref(&owner, target).is_none());
            let scalar = body.locals()[1].ty;
            let wrong_target =
                Ty::from_rigid_kind(RigidTy::RawPtr(scalar, rustc_public::mir::Mutability::Mut));
            assert!(chc.checked_host_native_dyn_box_deref(&operand, wrong_target).is_none());
            for projection in [
                vec![ProjectionElem::Field(0, scalar)],
                vec![ProjectionElem::Field(1, operand.ty(body.locals()).unwrap())],
            ] {
                let malformed = Operand::Copy(Place { local: place.local, projection });
                assert!(chc.checked_host_native_dyn_box_deref(&malformed, target).is_none());
            }
            chc.with_inline_walk_frame(&body, |chc| {
                assert!(chc.checked_host_native_dyn_box_deref(&operand, target).is_none());
            });
        }
    });
}

#[test]
fn host_native_dyn_box_cast_refuses_ambiguous_exposed_and_zero_sized_owners() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["joined", "exposed", "empty"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let (operand, target) = cast(&body);
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, memory_config());
            allocate(&mut chc);
            assert!(
                chc.checked_host_native_dyn_box_deref(&operand, target).is_none(),
                "{name}: no general address may be invented from a dyn carrier"
            );
        }
    });
}

#[test]
fn host_native_dyn_box_cast_preserves_the_custom_global_allocator_boundary() {
    let source = format!(
        "{SOURCE}\n#[global_allocator] static ALLOCATOR: std::alloc::System = std::alloc::System;"
    );
    with_test_ay_ctx_for_source(&source, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "native").callee_body().unwrap();
        let (operand, target) = cast(&body);
        let mut chc = ChcCtx::new(ctx.tcx, &body, "native", memory_config());
        allocate(&mut chc);
        assert!(chc.checked_host_native_dyn_box_deref(&operand, target).is_none());
    });
}

#[test]
fn host_native_dyn_receiver_carries_only_its_actual_box_coercion() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["native", "copied"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let argument = receiver(&body);
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, memory_config());
            assert!(chc.host_native_dyn_receiver_origin(&argument).is_none());
            allocate(&mut chc);
            let origin = chc.host_native_dyn_receiver_origin(&argument).unwrap_or_else(|| {
                panic!("{name}: actual coercion survives its raw cast and reborrow")
            });
            let (cast_operand, target) = cast(&body);
            let cast_origin =
                chc.host_native_dyn_box_deref_origin(&cast_operand, target).unwrap().2;
            assert_eq!(origin, cast_origin, "{name}: exact allocation and typed vtable");
            chc.with_inline_walk_frame(&body, |chc| {
                assert!(chc.host_native_dyn_receiver_origin(&argument).is_none());
            });
        }
    });
}

#[test]
fn host_native_dyn_receiver_declines_exposed_ambiguous_and_unknown_carriers() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for name in ["joined", "exposed", "empty", "exposed_receiver", "argument_receiver"] {
            let body = find_instance_by_suffix(ctx.tcx, name).callee_body().unwrap();
            let argument = receiver(&body);
            let mut chc = ChcCtx::new(ctx.tcx, &body, name, memory_config());
            allocate(&mut chc);
            assert!(chc.host_native_dyn_receiver_origin(&argument).is_none(), "{name}");
        }
    });
}

#[test]
fn host_native_dyn_body_read_types_are_discovered_before_entry_seeding() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "pointer_oob").callee_body().unwrap();
        let pointer_ty = fn_sig_by_suffix(ctx.tcx, "pointer_type").inputs()[0];
        let mut chc = ChcCtx::new(ctx.tcx, &body, "pointer_oob", memory_config());
        chc.prescan_callee_statics();
        assert!(
            chc.ref_resolution.extra_read_types.contains(&pointer_ty),
            "the real virtual body's pointer-field read must precede entry seeding"
        );
        assert!(chc.known_alloc_ids.is_empty(), "read discovery grants no allocation birth");
        assert!(
            chc.host_native_dyn_receiver_origin(&receiver(&body)).is_none(),
            "prescanning alone grants no receiver authority"
        );
    });
}
