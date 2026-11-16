// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Focused tests for precise CHC `kani::mem` overapprox dispatch helpers.

// Test code: unwrap/panic are acceptable for assertions.
#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use ay_bindings::{Expr, ExprValue, Sort};

const KANI_MEM_STORAGE_SOURCE: &str = r#"
    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool { true }
        }
    }
    pub fn nonzero_storage() {
        let value = [1u8, 2];
        let ptr = &value as *const [u8; 2];
        let _ = kani::mem::can_dereference(ptr);
    }
    pub fn zero_storage() {
        let value = [0u8; 0];
        let ptr = &value as *const [u8; 0];
        let _ = kani::mem::can_dereference(ptr);
    }
"#;

#[test]
fn test_kani_mem_storage_lifetime_live_dead_and_unknown() {
    with_test_ay_ctx_for_source(KANI_MEM_STORAGE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "nonzero_storage");
        let body = instance.body().expect("nonzero storage body");
        for (mode, expected, expected_overapprox) in
            [("live", true, false), ("dead", false, false), ("unknown", true, true)]
        {
            let mut chc = ChcCtx::new(
                ctx.tcx,
                &body,
                "nonzero_storage",
                ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
            );
            let (bb, _func, args) = body
                .blocks
                .iter()
                .enumerate()
                .find_map(|(bb, block)| {
                    let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                        &block.terminator.kind
                    else {
                        return None;
                    };
                    matches!(chc.detect_stub(func), Some(StubKind::KaniMemCanDereference))
                        .then(|| (bb, func.clone(), args.clone()))
                })
                .expect("can_dereference call");
            let Operand::Copy(ptr) = &args[0] else {
                panic!("pointer local");
            };
            let owner = body
                .locals()
                .iter()
                .position(|local| matches!(local.ty.kind(), TyKind::RigidTy(RigidTy::Array(..))))
                .expect("array storage");
            let obj_id = 17;
            chc.heap_state.insert_local_address(owner, obj_id, "__storage".to_string());
            chc.known_alloc_ids.insert(ptr.local, obj_id);
            chc.current_encode_bb = bb;
            chc.liveness.dead_locals.remove(&owner);
            if mode == "dead" {
                chc.liveness.dead_locals.insert(owner);
            }
            if mode == "unknown" {
                chc.current_encode_bb = usize::MAX;
            }
            // Exercise the access predicate directly: this fixture supplies a
            // concrete address, not an uninitialized operand-translation state.
            let address =
                Expr::bitvec_const(obj_id as u64, 32).concat(Expr::bitvec_const(0u64, 32));
            let (result, overapprox) =
                chc.compute_kani_mem_access_predicate(address, body.locals()[owner].ty, true);
            assert_eq!(overapprox, expected_overapprox, "{mode}: {result:?}");
            let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&result)
                .expect("fixture access predicate must be a constant");
            assert!(
                matches!(folded.value(), ExprValue::BoolConst(value) if *value == expected),
                "{mode}: {result:?}"
            );
        }
    });
}

#[test]
fn test_kani_mem_storage_lifetime_zero_sized_pointee_stays_valid() {
    with_test_ay_ctx_for_source(KANI_MEM_STORAGE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "zero_storage");
        let body = instance.body().expect("zero storage body");
        let mut chc = ChcCtx::new(
            ctx.tcx,
            &body,
            "zero_storage",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        let (bb, _func, args) = body
            .blocks
            .iter()
            .enumerate()
            .find_map(|(bb, block)| {
                let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                    &block.terminator.kind
                else {
                    return None;
                };
                matches!(chc.detect_stub(func), Some(StubKind::KaniMemCanDereference))
                    .then(|| (bb, func.clone(), args.clone()))
            })
            .expect("can_dereference call");
        let Operand::Copy(ptr) = &args[0] else {
            panic!("pointer local");
        };
        let owner = body
            .locals()
            .iter()
            .position(|local| matches!(local.ty.kind(), TyKind::RigidTy(RigidTy::Array(..))))
            .expect("zero-sized array storage");
        let obj_id = 17;
        chc.heap_state.insert_local_address(owner, obj_id, "__zst_storage".to_string());
        chc.known_alloc_ids.insert(ptr.local, obj_id);
        chc.current_encode_bb = bb;
        chc.liveness.dead_locals.insert(owner);
        let address = Expr::bitvec_const(obj_id as u64, 32).concat(Expr::bitvec_const(0u64, 32));
        let (result, overapprox) =
            chc.compute_kani_mem_access_predicate(address, body.locals()[owner].ty, true);
        assert!(!overapprox, "{result:?}");
        let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&result)
            .expect("zero-sized fixture access must be constant");
        assert!(matches!(folded.value(), ExprValue::BoolConst(true)), "{result:?}");
    });
}

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

// This is a direct real-MIR translation test. Its local declarations supply
// the existing stub dispatch seam; no preprocessing/inlining is performed.
const KANI_MEM_BOOL_REPRESENTATION_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]
    mod kani {
        #[kanitool::fn_marker = "AssumeHook"]
        #[inline(never)]
        pub fn assume(_condition: bool) {}
        pub mod mem {
            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool { true }
        }
    }
    pub fn bool_array_invalid_bytes_safe(value: [u8; 2]) {
        kani::assume(value[0] > 1 || value[1] > 1);
        assert!(!kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
    }
    pub fn bool_array_invalid_bytes_bug(value: [u8; 2]) {
        kani::assume(value[0] > 1 || value[1] > 1);
        assert!(kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
    }
    pub fn bool_array_valid_bytes_safe(value: [u8; 2]) {
        kani::assume(value[0] <= 1 && value[1] <= 1);
        assert!(kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
    }
    pub fn bool_array_valid_bytes_bug(value: [u8; 2]) {
        kani::assume(value[0] <= 1 && value[1] <= 1);
        assert!(!kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
    }
    pub fn bool_array_typed_storage_safe(value: [bool; 2]) {
        assert!(kani::mem::can_dereference(&value));
    }
    pub fn bool_array_typed_storage_bug(value: [bool; 2]) {
        assert!(!kani::mem::can_dereference(&value));
    }
    pub fn bool_scalar_wide_storage_safe() {
        let value = 256u16;
        assert!(kani::mem::can_dereference(&value as *const _ as *const bool));
    }
    pub fn bool_scalar_wide_storage_bug() {
        let value = if cfg!(target_endian = "little") { 258u16 } else { 513u16 };
        assert!(kani::mem::can_dereference(&value as *const _ as *const bool));
    }
    pub fn bool_array_wide_storage_safe() {
        let value = [0x0200u16];
        assert!(!kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
    }
    pub fn bool_array_wide_storage_bug() {
        let value = [0x0001u16];
        assert!(!kani::mem::can_dereference(&value as *const _ as *const [bool; 2]));
    }
    pub fn bool_compact_enum_safe() {
        let value = Some(2u8);
        assert!(kani::mem::can_dereference(&value as *const _ as *const bool));
    }
    pub fn bool_compact_enum_bug() {
        let value = Some(2u8);
        assert!(!kani::mem::can_dereference(&value as *const _ as *const bool));
    }
    pub fn bool_compact_region_refusal() {
        let value = Box::new(None::<bool>);
        let pointer = &*value as *const Option<bool> as *const bool;
        kani::assume(true); // The read cannot use the allocation block's forward.
        assert!(!kani::mem::can_dereference(pointer));
    }
    pub fn bool_symbolic_pointer_refusal(pointer: *const bool) {
        assert!(kani::mem::can_dereference(pointer));
    }
    pub fn bool_partial_store_refusal() {
        let mut value = [0x0200u16];
        let byte = &raw mut value as *mut u8;
        unsafe { *byte = 0; }
        assert!(!kani::mem::can_dereference(&raw const value as *const [bool; 2]));
    }
"#;

#[test]
fn test_kani_mem_bool_representation_safe_and_bug() {
    super::test_trust_box_new::with_native_box_ctx(KANI_MEM_BOOL_REPRESENTATION_SOURCE, |ctx| {
        for name in [
            "bool_array_invalid_bytes_safe",
            "bool_array_invalid_bytes_bug",
            "bool_array_valid_bytes_safe",
            "bool_array_valid_bytes_bug",
            "bool_array_typed_storage_safe",
            "bool_array_typed_storage_bug",
            "bool_scalar_wide_storage_safe",
            "bool_scalar_wide_storage_bug",
            "bool_array_wide_storage_safe",
            "bool_array_wide_storage_bug",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("real MIR body");
            let chc = ChcCtx::new(ctx.tcx, &body, name, super::test_trust_box_new::mem_config());
            if name.contains("_bytes_") {
                assert!(
                    body.blocks.iter().any(|block| {
                        matches!(&block.terminator.kind,
                        rustc_public::mir::TerminatorKind::Call { func, .. }
                        if matches!(chc.detect_kani_hook(func),
                            Some(crate::kani_middle::kani_functions::KaniHook::Assume)))
                    }),
                    "the source assumption must reach the authentic Kani hook: {name}"
                );
            }
            let (vc, _, diagnostics) = chc.translate_with_diagnostics();
            let smt = emit_chc(&vc).to_string();
            if let Some(dir) = std::env::var_os("MC_BOOL_REPRESENTATION_ARTIFACT_DIR") {
                std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), &smt)
                    .unwrap();
                std::fs::write(
                    std::path::Path::new(&dir).join(format!("{name}.mir")),
                    format!("{body:#?}"),
                )
                .unwrap();
            }
            let verdict = run_z3_on_smt2_with_timeout(&smt, 30);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
                .remove(name)
                .unwrap_or_default();
            eprintln!("BOOL_REPRESENTATION {name}: {verdict:?}; reasons={reasons:?}");
            assert_eq!(
                verdict.as_deref(),
                Ok(if name.ends_with("safe") { "unsat" } else { "sat" }),
                "{name}"
            );
            assert_eq!(diagnostics.place_translation_drop.get(), 0, "{name}: {reasons:?}");
            assert_eq!(diagnostics.kani_mem_overapprox.get(), 0, "{name}: exact byte view");
            assert!(reasons.is_empty(), "{name}: {reasons:?}");
        }
    });
}

#[test]
fn test_kani_mem_bool_unproven_byte_representation_is_refused() {
    super::test_trust_box_new::with_native_box_ctx(KANI_MEM_BOOL_REPRESENTATION_SOURCE, |ctx| {
        for name in [
            "bool_compact_enum_safe",
            "bool_compact_enum_bug",
            "bool_symbolic_pointer_refusal",
            "bool_partial_store_refusal",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("real MIR body");
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, super::test_trust_box_new::mem_config())
                    .translate_with_diagnostics();
            assert!(
                diagnostics.kani_mem_overapprox.get() > 0,
                "unproven physical bytes must not answer exact Bool validity: {name}"
            );
            assert!(
                !vc.approximation_identity_complete,
                "neither Safe nor Genuine may be certified from the refused byte view: {name}"
            );
        }
    });
}

#[test]
fn test_kani_mem_bool_compact_region_is_not_a_physical_byte() {
    super::test_trust_box_new::with_native_box_ctx(KANI_MEM_BOOL_REPRESENTATION_SOURCE, |ctx| {
        let name = "bool_compact_region_refusal";
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = instance.body().expect("real native Box MIR");
        let (vc, _, diagnostics) =
            ChcCtx::new(ctx.tcx, &body, name, super::test_trust_box_new::mem_config())
                .translate_with_diagnostics();
        let smt = emit_chc(&vc).to_string();
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
            .remove(name)
            .unwrap_or_default();
        if let Some(dir) = std::env::var_os("MC_BOOL_REPRESENTATION_ARTIFACT_DIR") {
            std::fs::write(std::path::Path::new(&dir).join(format!("{name}.smt2")), &smt).unwrap();
            std::fs::write(
                std::path::Path::new(&dir).join(format!("{name}.mir")),
                format!("{body:#?}"),
            )
            .unwrap();
        }
        eprintln!("BOOL_REGION_REFUSAL reasons={reasons:?}, properties={:?}", vc.properties);
        assert!(
            diagnostics.sound_havoc_drop.get() > 0,
            "missing physical byte view must be recorded: {reasons:?}"
        );
        assert!(
            ["memory_cell_unwritten_under_key", "heap_view_read_unwritten"]
                .iter()
                .any(|reason| reasons.get(*reason).is_some_and(|count| *count > 0)),
            "the refusal must name the missing byte view, not unrelated Box debt: {reasons:?}"
        );
        // The only explicit panic in this source is the user's assertion;
        // its lowering retains a generic "panic reached" diagnostic.
        let assertions: Vec<_> = vc
            .properties
            .iter()
            .filter(|property| property.kind == trust_mc_core::violation::PropertyKind::Panic)
            .collect();
        assert_eq!(assertions.len(), 1, "the user panic must stay unique");
        let assertion = assertions[0];
        assert_eq!(
            assertion.approximation_dependent,
            Some(true),
            "a compact region must not certify an independent physical-byte result"
        );
    });
}

#[test]
fn test_kani_mem_bool_byte_representation_endianness_and_refusals() {
    for (endian, expected) in [(rustc_abi::Endian::Little, false), (rustc_abi::Endian::Big, true)] {
        let predicate =
            ChcCtx::bool_byte_validity_predicate(Expr::bitvec_const(0x0102u16, 16), endian)
                .unwrap();
        let result = trust_mc_core::chc_const_prop::eval::try_eval_to_const(&predicate).unwrap();
        assert!(matches!(result.value(), ExprValue::BoolConst(value) if *value == expected));
    }
    for value in [Expr::bitvec_const(1u8, 1), Expr::bitvec_const(1u16, 12), Expr::int_const(1)] {
        assert!(ChcCtx::bool_byte_validity_predicate(value, rustc_abi::Endian::Little).is_none());
    }
}

#[test]
fn test_kani_mem_bool_bytes_refuse_active_unit_stubs() {
    super::test_trust_box_new::with_native_box_ctx(KANI_MEM_BOOL_REPRESENTATION_SOURCE, |ctx| {
        let name = "bool_array_valid_bytes_safe";
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = instance.body().expect("real MIR body");
        let TyKind::RigidTy(RigidTy::FnDef(marker, _)) = instance.ty().kind() else {
            panic!("fixture definition");
        };
        let _stubs = crate::kani_middle::transform::UnitStubsTestScope::install(
            std::collections::HashMap::from([(marker, marker)]),
        );
        let (vc, _, diagnostics) =
            ChcCtx::new(ctx.tcx, &body, name, super::test_trust_box_new::mem_config())
                .translate_with_diagnostics();
        assert!(diagnostics.kani_mem_overapprox.get() > 0);
        assert!(!vc.approximation_identity_complete);
    });
}

#[test]
fn test_kani_mem_bool_bytes_refuse_untracked_copy_intrinsics() {
    const SOURCE: &str = r#"
        #![feature(core_intrinsics)]
        #![allow(dead_code, internal_features)]
        mod kani { pub mod mem {
            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool { true }
        }}
        pub fn bool_copy_intrinsic_refusal() {
            let mut value = [0u8; 2];
            let invalid = [2u8; 2];
            unsafe {
                core::intrinsics::copy_nonoverlapping(
                    &raw const invalid as *const u8,
                    &raw mut value as *mut u8,
                    2,
                );
            }
            assert!(!kani::mem::can_dereference(&raw const value as *const [bool; 2]));
        }
    "#;
    super::test_trust_box_new::with_native_box_ctx(SOURCE, |ctx| {
        let name = "bool_copy_intrinsic_refusal";
        let instance = find_instance_by_suffix(ctx.tcx, name);
        let body = instance.body().expect("real MIR body");
        assert!(
            body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
                matches!(
                    statement.kind,
                    rustc_public::mir::StatementKind::Intrinsic(
                        rustc_public::mir::NonDivergingIntrinsic::CopyNonOverlapping(_)
                    )
                )
            }),
            "control must reach the intrinsic statement, not a call fallback"
        );
        let chc = ChcCtx::new(ctx.tcx, &body, name, super::test_trust_box_new::mem_config());
        assert!(
            !chc.body_stores_through_deref(),
            "the direct-Deref fence must not mask the control"
        );
        let (vc, _, diagnostics) = chc.translate_with_diagnostics();
        assert!(
            diagnostics.kani_mem_overapprox.get() > 0,
            "a write not reflected in the forwarding map must invalidate exact bytes"
        );
        assert!(
            !vc.approximation_identity_complete,
            "the untracked byte write must retain unaccounted provenance debt"
        );
    });
}

#[test]
fn test_kani_mem_bool_bytes_refuse_named_wrapper_keys() {
    use rustc_public::CrateDef;
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        mod kani { pub mod mem {
            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool { true }
        }}
        #[repr(C)]
        struct Mutex<T> { tag: u8, value: T }
        pub fn bool_wrapper_invalid_safe() {
            let values = [Mutex { tag: 2u8, value: 0u8 }];
            assert!(!kani::mem::can_dereference(&values as *const _ as *const bool));
        }
        pub fn bool_wrapper_invalid_bug() {
            let values = [Mutex { tag: 2u8, value: 0u8 }];
            assert!(kani::mem::can_dereference(&values as *const _ as *const bool));
        }
        pub fn bool_wrapper_valid_safe() {
            let values = [Mutex { tag: 0u8, value: 2u8 }];
            assert!(kani::mem::can_dereference(&values as *const _ as *const bool));
        }
        pub fn bool_wrapper_valid_bug() {
            let values = [Mutex { tag: 0u8, value: 2u8 }];
            assert!(!kani::mem::can_dereference(&values as *const _ as *const bool));
        }
        pub fn native_wrapper_true_refusal() {
            let values = [std::sync::Mutex::new(2u8)];
            assert!(kani::mem::can_dereference(&values as *const _ as *const bool));
        }
        pub fn native_wrapper_false_refusal() {
            let values = [std::sync::Mutex::new(2u8)];
            assert!(!kani::mem::can_dereference(&values as *const _ as *const bool));
        }
    "#;
    super::test_trust_box_new::with_native_box_ctx(SOURCE, |ctx| {
        for name in [
            "bool_wrapper_invalid_safe",
            "bool_wrapper_invalid_bug",
            "bool_wrapper_valid_safe",
            "bool_wrapper_valid_bug",
            "native_wrapper_true_refusal",
            "native_wrapper_false_refusal",
        ] {
            let instance = find_instance_by_suffix(ctx.tcx, name);
            let body = instance.body().expect("real MIR body");
            let element_ty = body
                .locals()
                .iter()
                .find_map(|local| {
                    let TyKind::RigidTy(RigidTy::Array(element, _)) = local.ty.kind() else {
                        return None;
                    };
                    let TyKind::RigidTy(RigidTy::Adt(def, _)) = element.kind() else {
                        return None;
                    };
                    (def.trimmed_name() == "Mutex").then_some(element)
                })
                .expect("declared wrapper array");
            let size = element_ty.layout().expect("actual wrapper layout").shape().size.bytes();
            let TyKind::RigidTy(RigidTy::Adt(def, _)) = element_ty.kind() else {
                panic!("declared wrapper ADT")
            };
            use crate::kani_middle::std_abstraction::{NativeWrapperKind, native_wrapper_kind};
            if name.starts_with("native_wrapper_") {
                assert_eq!(native_wrapper_kind(ctx.tcx, def), Some(NativeWrapperKind::Mutex));
                assert!(size > 1, "the real Mutex has state in addition to its payload");
                assert_eq!(
                    ChcCtx::type_key_for_ty(element_ty).as_ref(),
                    "u8",
                    "real library identity retains the existing logical payload key"
                );
            } else {
                assert_eq!(native_wrapper_kind(ctx.tcx, def), None);
                assert_eq!(size, 2, "the user wrapper retains its tag and payload");
                assert_ne!(
                    ChcCtx::type_key_for_ty(element_ty).as_ref(),
                    "u8",
                    "the user wrapper keeps its ordinary ADT key"
                );
            }
            let (vc, _, diagnostics) =
                ChcCtx::new(ctx.tcx, &body, name, super::test_trust_box_new::mem_config())
                    .translate_with_diagnostics();
            assert!(
                diagnostics.kani_mem_overapprox.get() > 0,
                "a logical payload is not the wrapper's physical first byte: {name}"
            );
            assert!(
                !vc.approximation_identity_complete,
                "unsupported wrapper bytes must retain unaccounted provenance: {name}"
            );
        }
    });
}
