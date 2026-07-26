// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused tests for precise CHC `kani::mem` overapprox dispatch helpers.

// Test code: unwrap/panic are acceptable for assertions.
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use ay_bindings::{Expr, Sort};

fn mir_to_chc_mem(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    fn_name: &str,
) -> trust_mc_core::chc::ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig {
            track_level: crate::args::ChcTrackLevel::Mem,
            ..crate::codegen_ay::chc::ChcConfig::default()
        },
    )
}

const KANI_MEM_SAME_ALLOCATION_SOURCE: &str = r#"
    #![allow(dead_code)]

    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn same_allocation<T: ?Sized, U: ?Sized>(_p: *const T, _q: *const U) -> bool {
                true
            }
        }
    }

    pub fn probe_same_allocation_distinct_stack_is_false() {
        let left = 1u8;
        let right = 2u8;
        let left_ptr = &left as *const u8;
        let right_ptr = &right as *const u8;
        assert!(!kani::mem::same_allocation(left_ptr, right_ptr));
    }

    pub fn probe_same_allocation_distinct_slices_are_false() {
        let left = [1u8, 2u8];
        let right = [3u8, 4u8];
        let left_slice: &[u8] = &left;
        let right_slice: &[u8] = &right;
        let left_ptr = left_slice as *const [u8];
        let right_ptr = right_slice as *const [u8];
        assert!(!kani::mem::same_allocation(left_ptr, right_ptr));
    }

    pub fn probe_same_allocation_dead_stack_shape() {
        let ptr: *const u8;
        {
            let scoped = 9u8;
            ptr = &scoped as *const u8;
        }
        let _ = kani::mem::same_allocation(ptr, ptr);
    }

    pub fn probe_same_allocation_null_constants_are_false() {
        let null = core::ptr::null::<u8>();
        let one = 1usize as *const u8;
        assert!(!kani::mem::same_allocation(null, null));
        assert!(!kani::mem::same_allocation(null, one));
    }

    pub unsafe fn probe_same_allocation_freed_heap_is_false() {
        let layout = unsafe { std::alloc::Layout::from_size_align_unchecked(1, 1) };
        let ptr = unsafe { std::alloc::alloc(layout) };
        unsafe { std::alloc::dealloc(ptr, layout); }
        assert!(!kani::mem::same_allocation(ptr as *const u8, ptr as *const u8));
    }
"#;

#[test]
fn test_same_allocation_obj_id_simplifies_symbolic_offset_concat() {
    let obj_id = 0x4242_u32;
    let ptr = Expr::bitvec_const(obj_id as u64, 32)
        .concat(Expr::var("same_alloc_offset", Sort::bitvec(32)));
    let extracted_obj_id = ptr.extract(63, 32);

    let simplified = ChcCtx::simplify_same_allocation_obj_id_expr(extracted_obj_id);

    assert_eq!(ChcCtx::const_obj_id_u32(&simplified), Some(obj_id));
}

#[test]
fn test_same_allocation_obj_id_simplifies_nested_split_pointer_step() {
    let obj_id = 0x5151_u32;
    let base_ptr = Expr::bitvec_const(obj_id as u64, 32).concat(Expr::bitvec_const(0u64, 32));
    let stepped_ptr = base_ptr.extract(63, 32).concat(Expr::var("new_offset", Sort::bitvec(32)));
    let extracted_obj_id = stepped_ptr.extract(63, 32);

    let simplified = ChcCtx::simplify_same_allocation_obj_id_expr(extracted_obj_id);

    assert_eq!(ChcCtx::const_obj_id_u32(&simplified), Some(obj_id));
}

#[test]
fn test_same_allocation_distinct_stack_locals_are_precise() {
    with_test_ay_ctx_for_source(KANI_MEM_SAME_ALLOCATION_SOURCE, |ctx| {
        let fn_name = "probe_same_allocation_distinct_stack_is_false";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_mem(ctx.tcx, &body, fn_name);
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(overapprox, 0, "same_allocation should not fall back to true");

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "VC should serialize to non-empty SMT-LIB2");
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

#[test]
fn test_same_allocation_distinct_slice_fat_ptrs_are_precise() {
    with_test_ay_ctx_for_source(KANI_MEM_SAME_ALLOCATION_SOURCE, |ctx| {
        let fn_name = "probe_same_allocation_distinct_slices_are_false";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_mem(ctx.tcx, &body, fn_name);
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(overapprox, 0, "fat slice pointers should extract their data pointer");

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "VC should serialize to non-empty SMT-LIB2");
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

#[test]
fn test_same_allocation_dead_stack_local_is_not_live() {
    with_test_ay_ctx_for_source(KANI_MEM_SAME_ALLOCATION_SOURCE, |ctx| {
        let fn_name = "probe_same_allocation_dead_stack_shape";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let call_args = body
            .blocks
            .iter()
            .find_map(|block| {
                if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                    &block.terminator.kind
                    && matches!(chc_ctx.detect_stub(func), Some(StubKind::KaniMemSameAllocation))
                {
                    return Some(args.clone());
                }
                None
            })
            .expect("same_allocation call args");
        let ptr_local = match &call_args[0] {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            other => panic!("expected simple pointer local operand, got {other:?}"),
        };
        let owner_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(idx, local)| {
                (idx != ptr_local
                    && matches!(local.ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8))))
                .then_some(idx)
            })
            .expect("u8 stack owner local");

        let obj_id = 0xA11CE_u32;
        chc_ctx.heap_state.insert_local_address(owner_local, obj_id, "__dead_stack".to_string());
        chc_ctx.known_alloc_ids.insert(ptr_local, obj_id);
        chc_ctx.liveness.dead_locals.insert(owner_local);

        let (result, overapprox) = chc_ctx.compute_same_allocation(&call_args, &HashSet::new());

        assert!(!overapprox, "known dead stack liveness should not require fallback");
        assert!(
            matches!(result.value(), ExprValue::BoolConst(false)),
            "same_allocation for a dead stack object must be false, got {result:?}"
        );
    });
}

#[test]
fn test_same_allocation_symbolic_obj_id_excludes_dead_stack_ids_from_metadata() {
    with_test_ay_ctx_for_source(KANI_MEM_SAME_ALLOCATION_SOURCE, |ctx| {
        let fn_name = "probe_same_allocation_dead_stack_shape";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let owner_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(idx, local)| {
                matches!(local.ty.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U8))).then_some(idx)
            })
            .expect("u8 stack owner local");
        let dead_obj_id = 0xD15C_A11D_u32;
        chc_ctx.heap_state.insert_local_address(
            owner_local,
            dead_obj_id,
            "__symbolic_dead_stack".to_string(),
        );
        chc_ctx.liveness.dead_locals.insert(owner_local);

        let sym_obj_id = Expr::var("sym_obj_id", Sort::bitvec(32));
        let (result, overapprox) = chc_ctx.same_allocation_live_obj_predicate(sym_obj_id.clone());

        assert!(!overapprox, "symbolic dead-stack exclusion should remain precise");
        let predicate = result.to_string();
        assert!(
            predicate.contains("obj_valid"),
            "symbolic heap ids should still consult metadata: {predicate}"
        );

        let smt = format!(
            "(set-logic ALL)\n\
             (declare-const sym_obj_id (_ BitVec 32))\n\
             (declare-const obj_valid (Array (_ BitVec 32) Bool))\n\
             (assert (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true)))\n\
             (assert (= sym_obj_id (_ bv{dead_obj_id} 32)))\n\
             (assert {predicate})\n\
             (check-sat)\n"
        );
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

#[test]
fn test_same_allocation_null_and_distinct_constants_are_false() {
    with_test_ay_ctx_for_source(KANI_MEM_SAME_ALLOCATION_SOURCE, |ctx| {
        let fn_name = "probe_same_allocation_null_constants_are_false";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_mem(ctx.tcx, &body, fn_name);
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(overapprox, 0, "constant null provenance should be resolved precisely");

        let smt = emit_chc(&vc).to_string();
        assert!(!smt.is_empty(), "VC should serialize to non-empty SMT-LIB2");
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}

#[test]
fn test_same_allocation_freed_heap_object_requires_obj_valid_false() {
    with_test_ay_ctx_for_source(KANI_MEM_SAME_ALLOCATION_SOURCE, |ctx| {
        let fn_name = "probe_same_allocation_freed_heap_is_false";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let _ = crate::codegen_ay::take_kani_mem_overapprox_count();
        let vc = mir_to_chc_mem(ctx.tcx, &body, fn_name);
        assert_vc_structure(&vc, fn_name, body.blocks.len());
        let overapprox = crate::codegen_ay::take_kani_mem_overapprox_count();
        assert_eq!(overapprox, 0, "heap liveness should use obj_valid precisely");

        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("obj_valid"),
            "freed heap same_allocation should depend on obj_valid metadata"
        );
        assert_z3_result_with_timeout(&smt, "unsat", 10);
    });
}
