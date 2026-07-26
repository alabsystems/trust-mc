// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Mem-level deref type array collection (Part of #2231)
// ═══════════════════════════════════════════════════════════════════════

/// Source with raw pointer dereference — triggers collect_deref_type_arrays
/// at Mem track level. `*ptr` → Deref projection on a raw pointer.
const DEREF_PROBE_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]

    pub unsafe fn read_ptr(ptr: *const u32) -> u32 {
        *ptr
    }

    pub unsafe fn write_ptr(ptr: *mut u32, val: u32) {
        *ptr = val;
    }

    pub fn ref_deref(r: &u32) -> u32 {
        *r
    }
"#;

/// Source with a nested deref through a pointer-valued field.
///
/// This exercises `load_ptr_from_memory` on a deref carrier type (`*const u32`)
/// that can be introduced by projection traversal (not only by local declarations).
const NESTED_DEREF_CARRIER_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]

    pub struct Node {
        pub next: *const u32,
    }

    pub unsafe fn nested_field_deref(pp: *const Node) -> u32 {
        *(*pp).next
    }
"#;

/// At Mem level, a raw pointer deref should produce a type-indexed array
/// as a state variable (e.g., `_read_ptr_mem_u32`).
#[test]
fn test_collect_deref_type_arrays_raw_ptr_read() {
    with_test_ay_ctx_for_source(DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_ptr");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "read_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        // At Mem level, deref of *const u32 should declare a type-indexed array.
        let has_mem_array = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(name, sort)| name.contains("_mem_") && sort.is_array());
        assert!(
            has_mem_array,
            "Mem-level declaration with ptr deref should produce type-indexed array state vars. \
             state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    });
}

/// At Mem level, a raw pointer write should also declare type-indexed arrays.
#[test]
fn test_collect_deref_type_arrays_raw_ptr_write() {
    with_test_ay_ctx_for_source(DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "write_ptr");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "write_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let has_mem_array = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(name, sort)| name.contains("_mem_") && sort.is_array());
        assert!(
            has_mem_array,
            "Mem-level with *mut deref should produce type-indexed arrays. \
             state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    });
}

/// At Reg level, the same deref source should NOT produce type-indexed arrays.
#[test]
fn test_collect_deref_type_arrays_not_at_reg_level() {
    with_test_ay_ctx_for_source(DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_ptr");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "read_ptr", ChcConfig::default());

        chc_ctx.declare_block_relations();

        let has_mem_array =
            chc_ctx.state_var_mgr.state_vars.iter().any(|(name, _)| name.contains("_mem_"));
        assert!(
            !has_mem_array,
            "Reg-level should NOT produce type-indexed memory arrays. \
             state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    });
}

/// A reference deref (&u32 → *r) at Mem level should also produce type arrays.
#[test]
fn test_collect_deref_type_arrays_ref_deref() {
    with_test_ay_ctx_for_source(DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ref_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ref_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let has_mem_array = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .any(|(name, sort)| name.contains("_mem_") && sort.is_array());
        assert!(
            has_mem_array,
            "Mem-level &u32 deref should produce type-indexed array. \
             state_vars: {:?}",
            chc_ctx.state_var_mgr.state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
        );
    });
}

/// At Mem level, the type-indexed arrays should have matching output vars.
#[test]
fn test_deref_type_arrays_have_output_counterparts() {
    with_test_ay_ctx_for_source(DEREF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "read_ptr");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "read_ptr",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        chc_ctx.declare_block_relations();

        let mem_state_vars: Vec<&str> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .filter(|(name, _)| name.contains("_mem_"))
            .map(|(name, _)| &**name)
            .collect();

        for sv_name in &mem_state_vars {
            let expected_out = format!("{sv_name}__out");
            let has_output = chc_ctx
                .state_var_mgr
                .output_state_vars
                .iter()
                .any(|(name, _)| &**name == expected_out.as_str());
            assert!(
                has_output,
                "type-indexed array {sv_name} should have output counterpart {expected_out}. \
                 output_vars: {:?}",
                chc_ctx.state_var_mgr.output_state_vars.iter().map(|(n, _)| n).collect::<Vec<_>>()
            );
        }
    });
}

/// Deref carrier pointer types discovered during projection traversal should be
/// pre-declared as type arrays, preventing late `get_or_create_type_array` calls.
#[test]
fn test_collect_deref_type_arrays_declares_nested_deref_carrier_type() {
    with_test_ay_ctx_for_source(NESTED_DEREF_CARRIER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "nested_field_deref");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "nested_field_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut deref_types = std::collections::BTreeMap::new();
        for bb_data in &body.blocks {
            for stmt in &bb_data.statements {
                if let StatementKind::Assign(lhs, rhs) = &stmt.kind {
                    chc_ctx.collect_deref_types_from_place(lhs, &mut deref_types);
                    chc_ctx.collect_deref_types_from_rvalue(rhs, &mut deref_types);
                }
            }
            if let TerminatorKind::Call { args, .. } = &bb_data.terminator.kind {
                for arg in args {
                    if let Operand::Copy(place) | Operand::Move(place) = arg {
                        chc_ctx.collect_deref_types_from_place(place, &mut deref_types);
                    }
                }
            }
        }

        let ptr_u32_ty = *deref_types
            .values()
            .find(|ty| {
                matches!(
                    ty.kind(),
                    TyKind::RigidTy(RigidTy::RawPtr(inner, _))
                        if matches!(inner.kind(), TyKind::RigidTy(RigidTy::Uint(UintTy::U32)))
                )
            })
            .expect("expected deref traversal to discover *const u32 carrier type");
        let ptr_u32_key = ChcCtx::type_key_for_ty(ptr_u32_ty);

        chc_ctx.declare_block_relations();

        assert!(
            chc_ctx.heap_state.type_arrays.contains_key(&*ptr_u32_key),
            "missing type-array pre-declaration for deref carrier {ptr_u32_key}; keys: {:?}",
            chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
        );
        let expected_name = format!("_{}_mem_{}", "nested_field_deref", ptr_u32_key);
        let expected_sort = Sort::array(Sort::bitvec(POINTER_WIDTH), Sort::bitvec(POINTER_WIDTH));
        assert!(
            chc_ctx
                .state_var_mgr
                .state_vars
                .iter()
                .any(|(name, sort)| &**name == expected_name.as_str() && *sort == expected_sort),
            "missing state var for deref carrier array {expected_name} with sort {expected_sort:?}"
        );
        assert!(
            chc_ctx
                .state_var_mgr
                .output_state_vars
                .iter()
                .any(|(name, sort)| **name == format!("{expected_name}__out")
                    && *sort == expected_sort),
            "missing output state var for deref carrier array {expected_name}__out"
        );
    });
}
