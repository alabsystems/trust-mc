// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use crate::codegen_ay::context::with_test_ay_ctx_for_source;
use crate::codegen_ay::test_fixtures::find_instance_by_suffix;
use crate::kani_middle::tuple_usage::TupleUsageAnalysis;
use rustc_public::mir::{Body, CastKind, Place, Rvalue, StatementKind, TerminatorKind};
mod observations;
mod receiver_boundaries;

const SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(allocator_api)]
    #![feature(core_intrinsics)]
    #![allow(internal_features)]
    pub fn scalar(b: Box<u32>) -> u32 { *b }
    pub fn narrow(b: Box<u16>) -> u16 { *b }
    pub fn unit(b: Box<()>) -> *const () { &*b }
    #[repr(align(32))] pub struct Aligned;
    pub fn aligned(b: Box<Aligned>) -> *const Aligned { &*b }
    pub enum Void {}
    pub fn impossible(b: Box<Void>) -> *const Void { &*b }
    pub fn impossible_ref(b: Box<&'static Void>) -> *const &'static Void { &*b }
    pub fn slice(b: Box<[u32]>) -> *const [u32] { &*b }
    pub trait Trait {}
    pub fn dynamic(b: Box<dyn Trait>) -> *const dyn Trait { &*b }
    pub fn allocate() -> Box<u32> { Box::new(7u32) }
    pub fn custom_new(value: u32) -> Box<u32> { Box::new(value) }
    pub fn custom_allocate() -> Box<u32> { custom_new(7) }
    pub unsafe fn wrap_raw(pointer: *mut u32) -> Box<u32> { unsafe { Box::from_raw(pointer) } }
    pub unsafe fn transmute_pointer(pointer:*mut u32)->Box<u32> { unsafe {core::mem::transmute(pointer)} }
    pub fn release(value: Box<u32>) -> *mut u32 { Box::into_raw(value) }
    pub unsafe fn custom_from_raw(pointer: *mut u32) -> Box<u32> { unsafe { Box::from_raw(pointer) } }
    pub unsafe fn custom_wrap(pointer: *mut u32) -> Box<u32> { unsafe { custom_from_raw(pointer) } }
    pub struct WithDrop;
    impl Drop for WithDrop { fn drop(&mut self) { panic!("user destructor"); } }
    pub fn custom_drop(value: Box<WithDrop>) { drop(value); }
    pub fn native_drop(value: Box<u32>) { core::mem::drop(value); }
    pub unsafe fn zst_roundtrip(pointer: *mut Aligned) -> *mut Aligned { Box::into_raw(unsafe {Box::from_raw(pointer)}) }
    pub unsafe fn global_construct(pointer:*mut u32)->Box<u32> { unsafe {Box::from_raw_in(pointer,std::alloc::Global)} }
    pub unsafe fn system_construct(pointer:*mut u32)->Box<u32,std::alloc::System> { unsafe {Box::from_raw_in(pointer,std::alloc::System)} }
    pub fn system_owner(value:Box<u32,std::alloc::System>) { drop(value); }
    pub fn address_api(pointer:*const u32)->usize { pointer.addr() }
    pub fn null_api(pointer:*const u32)->bool { pointer.is_null() }
    pub unsafe fn compare_api(left:*const u32,right:*const u32)->u8 { core::intrinsics::ptr_guaranteed_cmp(left,right) }
    pub unsafe fn write_pointer(slot: *mut *mut u32, value: *mut u32) { unsafe { *slot=value; } }
    #[repr(transparent)]
    pub struct BoxRaw<T> { pub pointer: core::ptr::NonNull<T>, pub marker: core::marker::PhantomData<T> }
    pub fn custom_carrier(value: BoxRaw<u32>, pointer: *const u32) -> *const u32 { let _ = value; pointer }
"#;

fn actual_cast(body: &Body) -> (Operand, Ty) {
    body.blocks
        .iter()
        .flat_map(|block| &block.statements)
        .find_map(|statement| {
            let StatementKind::Assign(
                _,
                Rvalue::Cast(CastKind::BoxDerefTransmute, operand, target),
            ) = &statement.kind
            else {
                return None;
            };
            Some((operand.clone(), *target))
        })
        .expect("genuine native compiler BoxDerefTransmute")
}

#[test]
fn bmc_box_transfers_and_drop_require_resolved_native_identity_and_empty_pointee_glue() {
    use crate::codegen_ay::shared::native_box_raw::{
        native_bmc_box_drop_is_modeled, native_bmc_box_drop_value, native_bmc_box_from_raw,
        native_bmc_box_into_raw,
    };
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        for (name, from_raw, into_raw) in [
            ("wrap_raw", true, false),
            ("release", false, true),
            ("custom_wrap", false, false),
            ("native_drop", false, false),
            ("custom_drop", false, false),
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            let func = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, .. } => Some(func),
                    _ => None,
                })
                .unwrap();
            let TyKind::RigidTy(RigidTy::FnDef(def, generics)) =
                func.ty(body.locals()).unwrap().kind()
            else {
                panic!("call")
            };
            let callee = Instance::resolve(def, &generics).unwrap();
            assert_eq!(native_bmc_box_from_raw(ctx.tcx, &callee).is_some(), from_raw, "{name}");
            assert_eq!(native_bmc_box_into_raw(ctx.tcx, &callee).is_some(), into_raw, "{name}");
            assert_eq!(
                native_bmc_box_drop_value(ctx.tcx, &callee).is_some(),
                name == "native_drop",
                "{name}"
            );
            let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(HashMap::from(
                [(def, def)],
            ));
            assert!(native_bmc_box_from_raw(ctx.tcx, &callee).is_none());
            assert!(native_bmc_box_into_raw(ctx.tcx, &callee).is_none());
            assert!(native_bmc_box_drop_value(ctx.tcx, &callee).is_none());
        }
        for (name, modeled) in [
            ("scalar", true),
            ("aligned", true),
            ("custom_drop", false),
            ("slice", false),
            ("dynamic", false),
        ] {
            let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
            assert_eq!(
                native_bmc_box_drop_is_modeled(ctx.tcx, body.locals()[1].ty),
                modeled,
                "{name}"
            );
        }
    });
}

#[test]
fn bmc_native_box_unknown_free_withdraws_later_authority() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        bind_box(&mut codegen, &operand, pointer);
        let before = codegen.checked_bmc_box_deref(&operand, target).unwrap().1;
        codegen.ctx.native_box_deallocation_event(&Expr::bitvec_const(0x1234u64, 64), None);
        check_formula(before, true);
        assert!(codegen.ctx.unsupported_constructs.contains_key("BoxDeallocationOrigin"));
        assert!(codegen.checked_bmc_box_deref(&operand, target).is_none());
    });
}

#[test]
fn bmc_native_and_ordinary_heap_liveness_obey_the_same_conditional_free_guard() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        bind_box(&mut codegen, &operand, pointer.clone());
        let guard = codegen.ctx.declare_var("conditional_free", ay_bindings::Sort::bool());
        codegen.ctx.heap_dealloc_on_path(
            pointer.clone(),
            Expr::bitvec_const(4u64, 64),
            Expr::bitvec_const(4u64, 64),
            Some(guard.clone()),
        );
        let native = codegen
            .checked_bmc_box_deref(&operand, target)
            .unwrap()
            .1
            .into_iter()
            .reduce(Expr::and)
            .unwrap();
        let ordinary = codegen.ctx.heap_is_allocated(pointer, Some(Expr::bitvec_const(4u64, 64)));
        let program = codegen.ctx.program.to_string();
        for value in [native, ordinary] {
            let smt = format!(
                "{program}\n(assert (not (= {value} (not conditional_free))))\n(check-sat)\n"
            );
            let commands = ay_frontend::parse(&smt).unwrap();
            let mut executor = ay_dpll::Executor::new();
            executor.set_timeout(Some(std::time::Duration::from_secs(5)));
            let output = executor.execute_all(&commands).unwrap();
            assert!(output.iter().any(|line| line.trim() == "unsat"), "{smt}\n{output:?}");
        }
        assert!(!codegen.ctx.unsupported_constructs.contains_key("BoxConditionalDeallocation"));
    });
}

#[test]
fn bmc_native_box_pointer_call_destination_storage_is_refused() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_pointer");
        let body = instance.body().unwrap();
        ctx.set_current_fn(instance);
        let destination = body
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .find_map(|statement| match &statement.kind {
                StatementKind::Assign(place, _)
                    if place
                        .projection
                        .iter()
                        .any(|p| matches!(p, rustc_public::mir::ProjectionElem::Deref)) =>
                {
                    Some(place)
                }
                _ => None,
            })
            .unwrap();
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        codegen.assign_value_to_place(destination, pointer);
        assert!(codegen.ctx.unsupported_constructs.contains_key("BoxPointerStore"));
    });
}

#[test]
fn bmc_box_formula_limits_bound_deep_and_shared_input_before_recursive_evaluation() {
    let mut deep = Expr::var("deep", ay_bindings::Sort::bitvec(64));
    assert!(bounded_box_formula(&deep));
    for _ in 0..65 {
        deep = deep.bvadd(Expr::bitvec_const(1u64, 64));
    }
    assert!(!bounded_box_formula(&deep));
    let mut shared = Expr::var("shared", ay_bindings::Sort::bitvec(64));
    for _ in 0..12 {
        shared = shared.clone().bvadd(shared);
    }
    assert!(bounded_box_formula(&shared));
}

#[test]
fn bmc_native_box_free_does_not_infer_provenance_from_arithmetic_address_bits() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let mut roots = Vec::new();
        for _ in 0..2 {
            let pointer =
                codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
            codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
            roots.push(pointer);
        }
        bind_box(&mut codegen, &operand, roots[1].clone());
        check_formula(codegen.checked_bmc_box_deref(&operand, target).unwrap().1, true);
        let arithmetic = roots[0].clone().bvadd(roots[1].clone().bvsub(roots[0].clone()));
        codegen.ctx.native_box_deallocation_event(&arithmetic, None);
        assert!(codegen.ctx.unsupported_constructs.contains_key("BoxDeallocationOrigin"));
        assert!(codegen.checked_bmc_box_deref(&operand, target).is_none());
    });
}

#[test]
fn bmc_native_box_path_selection_keeps_original_provenance_and_refuses_uncomposed_join() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        let guard = codegen.ctx.declare_var("box_join_guard", ay_bindings::Sort::bool());
        let unknown = codegen.ctx.declare_var("box_join_unknown", ay_bindings::Sort::bitvec(64));
        bind_box(&mut codegen, &operand, Expr::ite(guard.clone(), pointer, unknown));
        assert!(codegen.checked_bmc_box_deref(&operand, target).is_none());
        codegen.current_path_condition = Some(guard.clone());
        check_formula(codegen.checked_bmc_box_deref(&operand, target).unwrap().1, true);
        codegen.current_path_condition = Some(guard.not());
        assert!(codegen.checked_bmc_box_deref(&operand, target).is_none());
    });
}

#[test]
fn bmc_native_by_value_drop_frees_the_allocation_and_returns_native_unit() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "native_drop");
        let body = instance.body().unwrap();
        let (func, args, destination) = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, destination, .. } => {
                    Some((func, args, destination))
                }
                _ => None,
            })
            .unwrap();
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        bind_box(&mut codegen, &args[0], pointer);
        assert!(codegen.try_native_box_transfer_call(func, args, destination));
        check_formula(
            vec![codegen.ctx.native_box_allocation(0).unwrap().alive.clone().unwrap()],
            false,
        );
        let value = codegen.codegen_place(destination).unwrap();
        assert_eq!(
            value.sort(),
            &StatementCodegen::infer_sort_from_ty(destination.ty(body.locals()).unwrap()).unwrap()
        );
        assert!(!codegen.ctx.unsupported_constructs.contains_key("BoxDropValidity"));
    });
}

#[test]
fn bmc_native_box_does_not_mint_allocator_authority_for_a_user_global_allocator() {
    const ALLOCATOR: &str = r#"
    use std::alloc::{GlobalAlloc,Layout,System};
    struct UserAllocator;
    unsafe impl GlobalAlloc for UserAllocator {
        unsafe fn alloc(&self,layout:Layout)->*mut u8 { unsafe {System.alloc(layout)} }
        unsafe fn dealloc(&self,ptr:*mut u8,layout:Layout) { unsafe {System.dealloc(ptr,layout)} }
    }
    #[global_allocator] static GLOBAL:UserAllocator=UserAllocator;
    pub fn allocate()->Box<u32> { Box::new(7) }
    "#;
    with_test_ay_ctx_for_source(ALLOCATOR, |mut ctx| {
        assert!(crate::codegen_ay::shared::native_box_raw::native_bmc_has_custom_global_allocator(
            ctx.tcx
        ));
        let instance = find_instance_by_suffix(ctx.tcx, "allocate");
        let body = instance.body().unwrap();
        let (func, args) = body
            .blocks
            .iter()
            .find_map(|block| match &block.terminator.kind {
                TerminatorKind::Call { func, args, .. } => Some((func, args)),
                _ => None,
            })
            .unwrap();
        ctx.set_current_fn(instance);
        let codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        assert!(codegen.native_box_new_layout(func, args).is_none());
    });
}

#[test]
fn bmc_native_box_transfer_entry_keeps_exact_pointer_and_demotes_unknown_origin() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        for name in ["wrap_raw", "release"] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            let (func, args, destination) = body
                .blocks
                .iter()
                .find_map(|block| match &block.terminator.kind {
                    TerminatorKind::Call { func, args, destination, .. } => {
                        Some((func, args, destination))
                    }
                    _ => None,
                })
                .unwrap();
            ctx.set_current_fn(instance);
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let pointer =
                codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
            codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
            if name == "wrap_raw" {
                codegen.ctx.release_native_box(&pointer, None);
            }
            bind_box(&mut codegen, &args[0], pointer.clone());
            assert!(codegen.try_native_box_transfer_call(func, args, destination), "{name}");
            let output = codegen.codegen_place(destination).unwrap();
            assert_eq!(node(&codegen.box_pointer_value(&output).unwrap()), node(&pointer));
            if name == "wrap_raw" {
                assert!(codegen.try_native_box_transfer_call(func, args, destination));
                assert!(
                    codegen.ctx.unsupported_constructs.contains_key("BoxConstructionValidity"),
                    "repeated ownership claims are refused without new release custody"
                );
            }
            let unknown =
                codegen.ctx.declare_var("untracked_box_origin", ay_bindings::Sort::bitvec(64));
            bind_box(&mut codegen, &args[0], unknown);
            assert!(codegen.try_native_box_transfer_call(func, args, destination));
            assert!(codegen.ctx.unsupported_constructs.contains_key("BoxConstructionValidity"));
        }
    });
}

fn bind_box(codegen: &mut StatementCodegen<'_, '_, '_>, operand: &Operand, pointer: Expr) {
    let (Operand::Copy(place) | Operand::Move(place)) = operand else {
        panic!("native carrier place")
    };
    codegen.assign_value_to_place(&Place { local: place.local, projection: vec![] }, pointer);
}

fn check_formula(checks: Vec<Expr>, expected: bool) {
    let condition = checks.into_iter().reduce(Expr::and).unwrap();
    for (formula, want) in [
        (condition.clone(), if expected { "sat" } else { "unsat" }),
        (condition.not(), if expected { "unsat" } else { "sat" }),
    ] {
        let smt = format!("(set-logic QF_BV)\n(assert {formula})\n(check-sat)\n");
        let commands = ay_frontend::parse(&smt).unwrap();
        let mut executor = ay_dpll::Executor::new();
        executor.set_timeout(Some(std::time::Duration::from_secs(5)));
        let output = executor.execute_all(&commands).unwrap();
        assert!(output.iter().any(|line| line.trim() == want), "{want}: {smt}\n{output:?}");
    }
}

#[test]
fn bmc_native_box_checks_non_null_alignment_full_extent_and_wrap() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        for (size, offset, safe) in [
            (8, 0u64, true),
            (8, 4, true),
            (8, 1, false),
            (8, 8, false),
            (8, u64::MAX, false),
            (0, 0, false),
        ] {
            let pointer =
                codegen.ctx.heap_alloc(Expr::bitvec_const(size, 64), Expr::bitvec_const(4u64, 64));
            codegen.ctx.record_native_box_allocation(pointer.clone(), size, 4, None);
            let value =
                if offset == 0 { pointer } else { pointer.bvadd(Expr::bitvec_const(offset, 64)) };
            bind_box(&mut codegen, &operand, value);
            let (_, checks) =
                codegen.checked_bmc_box_deref(&operand, target).expect("known native allocation");
            check_formula(checks, safe);
        }
        bind_box(&mut codegen, &operand, Expr::bitvec_const(0u64, 64));
        check_formula(codegen.checked_bmc_box_deref(&operand, target).unwrap().1, false);
    });
}

#[test]
fn bmc_native_box_liveness_is_frozen_before_later_free_and_rechecked_after_free() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 4, None);
        bind_box(&mut codegen, &operand, pointer.clone());
        let before = codegen.checked_bmc_box_deref(&operand, target).unwrap().1;
        codegen.ctx.heap_dealloc(
            pointer,
            Expr::bitvec_const(4u64, 64),
            Expr::bitvec_const(4u64, 64),
        );
        check_formula(before, true);
        check_formula(codegen.checked_bmc_box_deref(&operand, target).unwrap().1, false);
    });
}

#[test]
fn bmc_native_box_zst_and_operationally_impossible_pointees() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        for (name, address, expected) in [
            ("unit", 1u64, true),
            ("aligned", 32, true),
            ("aligned", 1, false),
            ("aligned", 0, false),
            ("impossible", 1, false),
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            let (operand, target) = actual_cast(&body);
            ctx.set_current_fn(instance);
            let mut codegen =
                StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            let pointer = Expr::bitvec_const(address, 64);
            codegen.ctx.record_box_numeric_address(pointer.clone());
            bind_box(&mut codegen, &operand, pointer);
            check_formula(codegen.checked_bmc_box_deref(&operand, target).unwrap().1, expected);
        }
        let instance = find_instance_by_suffix(ctx.tcx, "impossible_ref");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(8u64, 64), Expr::bitvec_const(8u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 8, 8, None);
        bind_box(&mut codegen, &operand, pointer);
        check_formula(codegen.checked_bmc_box_deref(&operand, target).unwrap().1, false);
    });
}

#[test]
fn bmc_zst_derived_heap_address_cannot_use_stride_bits_as_physical_null_facts() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "aligned");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(32u64, 64), Expr::bitvec_const(32u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 32, 32, None);
        bind_box(&mut codegen, &operand, pointer.clone());
        check_formula(codegen.checked_bmc_box_deref(&operand, target).unwrap().1, true);
        bind_box(
            &mut codegen,
            &operand,
            pointer.bvadd(Expr::bitvec_const(0xffff_ffff_fff0_0000u64, 64)),
        );
        assert!(codegen.checked_bmc_box_deref(&operand, target).is_none());
    });
}

#[test]
fn bmc_native_box_refuses_counterfeit_bits_weak_alignment_fat_metadata_and_stubs() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "scalar");
        let body = instance.body().unwrap();
        let (operand, target) = actual_cast(&body);
        ctx.set_current_fn(instance);
        let mut codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
        let pointer =
            codegen.ctx.heap_alloc(Expr::bitvec_const(4u64, 64), Expr::bitvec_const(4u64, 64));
        codegen.ctx.record_native_box_allocation(pointer.clone(), 4, 1, None);
        bind_box(&mut codegen, &operand, pointer.clone());
        assert!(
            codegen.checked_bmc_box_deref(&operand, target).is_none(),
            "stride alignment is not native allocator alignment"
        );
        let fake = Expr::bitvec_const(0x100000u64, 64);
        codegen.ctx.record_box_numeric_address(fake.clone());
        assert_eq!(fake, pointer, "same bits, independently produced");
        bind_box(&mut codegen, &operand, fake);
        assert!(codegen.checked_bmc_box_deref(&operand, target).is_none());
        for name in ["slice", "dynamic"] {
            let instance = find_instance_by_suffix(codegen.ctx.tcx, name);
            let body = instance.body().unwrap();
            let (operand, target) = actual_cast(&body);
            let mut nested =
                StatementCodegen::new(codegen.ctx, &body, TupleUsageAnalysis::run(&body));
            bind_box(&mut nested, &operand, pointer.clone());
            assert!(
                nested.checked_bmc_box_deref(&operand, target).is_none(),
                "{name}: metadata was erased"
            );
        }
    });
}

#[test]
fn bmc_native_box_allocation_facts_require_the_actual_native_constructor() {
    with_test_ay_ctx_for_source(SOURCE, |mut ctx| {
        for (name, expected) in [("allocate", Some((4, 4))), ("custom_allocate", None)] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().unwrap();
            let (func, args) = body
                .blocks
                .iter()
                .find_map(|block| {
                    let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else {
                        return None;
                    };
                    Some((func, args))
                })
                .unwrap();
            ctx.set_current_fn(instance);
            let codegen = StatementCodegen::new(&mut ctx, &body, TupleUsageAnalysis::run(&body));
            assert_eq!(codegen.native_box_new_layout(func, args), expected, "{name}");
            if name == "allocate" {
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) =
                    func.ty(body.locals()).unwrap().kind()
                else {
                    panic!("native constructor")
                };
                let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
                    HashMap::from([(def, def)]),
                );
                assert!(codegen.native_box_new_layout(func, args).is_none());
            }
        }
    });
}
