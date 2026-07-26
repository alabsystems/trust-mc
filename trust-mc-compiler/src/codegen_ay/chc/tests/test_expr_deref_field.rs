// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_expr_deref_field.rs` — deref resolution helpers
//! for ref-target, argument-ref, and static-ref paths.
//!
//! Part of #2921 (untested production file coverage).
//! Part of #2302 (cross-repo quality patterns).
//!
//! Covers:
//! - `try_resolve_deref_via_ref_targets`: ref_target-based deref chain
//! - `resolve_arg_ref_deref`: argument reference pointee resolution (#2844)
//! - `resolve_static_ref_deref`: static-mut pointer resolution (#428)
//! - `emit_ptr_obj_valid_check`: raw pointer validity check (#2310)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use std::collections::HashSet;

use rustc_public::mir::{Place, ProjectionElem, Rvalue, StatementKind};

use super::common::*;

// =============================================================================
// Deref through reference (&T) — exercises try_resolve_deref_via_ref_targets
// =============================================================================

const REF_DEREF_FIELD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Pair { pub x: u32, pub y: u32 }

    pub fn probe_ref_deref_field(r: &Pair) -> u32 {
        (*r).x + (*r).y
    }
"#;

/// Deref through &Pair to access fields produces a valid VC with bv32 state vars.
#[test]
fn test_ref_deref_field_produces_vc() {
    with_test_ay_ctx_for_source(REF_DEREF_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_deref_field");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_deref_field", ChcConfig::default());

        assert_vc_structure(&vc, "probe_ref_deref_field", body.blocks.len());

        // u32 fields should produce bv32 sorts in relations
        assert_relation_has_arg_sort(
            &vc,
            "probe_ref_deref_field",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );
    });
}

/// Deref through reference should produce non-trivial transition constraints
/// (field selects or bvadd for the addition).
#[test]
fn test_ref_deref_field_has_nontrivial_semantics() {
    with_test_ay_ctx_for_source(REF_DEREF_FIELD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ref_deref_field");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_ref_deref_field", ChcConfig::default());

        assert_has_nontrivial_transition_constraints(&vc, "probe_ref_deref_field");
    });
}

// =============================================================================
// Argument reference deref — exercises resolve_arg_ref_deref (#2844)
// =============================================================================

const ARG_REF_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_arg_ref_deref(val: &u32) -> u32 {
        *val
    }
"#;

/// Deref of argument reference &u32 should produce a valid VC.
#[test]
fn test_arg_ref_deref_produces_vc() {
    with_test_ay_ctx_for_source(ARG_REF_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arg_ref_deref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_arg_ref_deref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_arg_ref_deref", body.blocks.len());
    });
}

// =============================================================================
// Argument mutable reference deref — exercises resolve_arg_ref_deref path
// =============================================================================

const ARG_MUT_REF_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_arg_mut_ref(val: &mut u32) -> u32 {
        let old = *val;
        *val = old + 1;
        old
    }
"#;

/// Deref + store through &mut u32 argument should produce VC with transitions.
#[test]
fn test_arg_mut_ref_deref_produces_vc() {
    with_test_ay_ctx_for_source(ARG_MUT_REF_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arg_mut_ref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_arg_mut_ref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_arg_mut_ref", body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, "probe_arg_mut_ref");
    });
}

const TEMP_REF_ENUM_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_temp_ref_option_payload(flag: bool) -> i32 {
        let value = if flag { Some(7_i32) } else { None };
        let tmp = &value;
        match *tmp {
            Some(v) => v,
            None => 0,
        }
    }
"#;

const STATIC_MUT_OPTION_PAYLOAD_SOURCE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }
    }

    static mut SLOT: Option<u32> = None;

    pub fn probe_static_mut_option_payload() -> u32 {
        unsafe {
            let _baseline = match &SLOT {
                Some(v) => *v,
                None => 0,
            };
            SLOT = kani::any();
            match &SLOT {
                Some(v) => *v,
                None => 0,
            }
        }
    }
"#;

fn place_is_deref_downcast_field(place: &Place) -> bool {
    matches!(place.projection.first(), Some(ProjectionElem::Deref))
        && place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Downcast(_)))
        && place.projection.iter().any(|proj| matches!(proj, ProjectionElem::Field(_, _)))
        && place.projection.iter().all(|proj| {
            matches!(
                proj,
                ProjectionElem::Deref | ProjectionElem::Downcast(_) | ProjectionElem::Field(_, _)
            )
        })
}

fn find_deref_downcast_field_place(
    body: &rustc_public::mir::Body,
) -> Option<rustc_public::mir::Place> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(dest, rvalue) = &stmt.kind else {
                continue;
            };

            if place_is_deref_downcast_field(dest) {
                return Some(dest.clone());
            }

            let source_places: Vec<&Place> = match rvalue {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::Ref(_, _, place)
                | Rvalue::AddressOf(_, place)
                | Rvalue::CopyForDeref(place)
                | Rvalue::Discriminant(place)
                | Rvalue::Len(place) => vec![place],
                _ => vec![],
            };

            for place in source_places {
                if place_is_deref_downcast_field(place) {
                    return Some(place.clone());
                }
            }
        }
    }

    None
}

fn find_last_deref_downcast_field_place(
    body: &rustc_public::mir::Body,
) -> Option<rustc_public::mir::Place> {
    let mut found = None;

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(dest, rvalue) = &stmt.kind else {
                continue;
            };

            if place_is_deref_downcast_field(dest) {
                found = Some(dest.clone());
            }

            let source_places: Vec<&Place> = match rvalue {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                | Rvalue::Ref(_, _, place)
                | Rvalue::AddressOf(_, place)
                | Rvalue::CopyForDeref(place)
                | Rvalue::Discriminant(place)
                | Rvalue::Len(place) => vec![place],
                _ => vec![],
            };

            for place in source_places {
                if place_is_deref_downcast_field(place) {
                    found = Some(place.clone());
                }
            }
        }
    }

    found
}

#[test]
fn test_translate_place_with_modified_redirects_temp_ref_enum_payload() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();

    with_test_ay_ctx_for_source(TEMP_REF_ENUM_PAYLOAD_SOURCE, |ctx| {
        let fn_name = "probe_temp_ref_option_payload";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let place = find_deref_downcast_field_place(&body)
            .expect("probe_temp_ref_option_payload should contain a Deref+Downcast+Field read");
        let expr = chc_ctx
            .translate_place_with_modified(&place, &HashSet::new())
            .expect("temp-ref Deref+Downcast+Field read should translate");

        assert_eq!(
            expr.sort().bitvec_width(),
            Some(32),
            "Option<i32> payload read through temp ref should translate to a bv32 payload"
        );
    });

    assert_eq!(
        crate::codegen_ay::take_place_translation_drop_count(),
        0,
        "temp-ref enum payload read should not increment place_translation_drop"
    );
    assert_eq!(
        crate::codegen_ay::take_unsupported_field_projection_count(),
        0,
        "temp-ref enum payload read should not increment unsupported_field_projection"
    );
}

#[test]
fn test_translate_place_with_modified_redirects_static_mut_option_payload() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();

    with_test_ay_ctx_for_source(STATIC_MUT_OPTION_PAYLOAD_SOURCE, |ctx| {
        let fn_name = "probe_static_mut_option_payload";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, fn_name, ChcConfig::default());
        chc_ctx.declare_block_relations();

        let place = find_last_deref_downcast_field_place(&body)
            .expect("probe_static_mut_option_payload should contain a Deref+Downcast+Field read");
        let defining_statements: Vec<String> = body
            .blocks
            .iter()
            .enumerate()
            .flat_map(|(bb_idx, block)| {
                block.statements.iter().filter_map(move |stmt| {
                    let StatementKind::Assign(dest, rhs) = &stmt.kind else {
                        return None;
                    };
                    (dest.local == place.local)
                        .then(|| format!("bb{bb_idx}: _{} = {:?}", dest.local, rhs))
                })
            })
            .collect();
        let expr = chc_ctx.translate_place_with_modified(&place, &HashSet::new());
        assert!(
            expr.is_some(),
            "static-mut Deref+Downcast+Field read should translate; place={place:?}, \
             local={}, defining_statements={defining_statements:?}, static_ref_to_state_idx={:?}",
            place.local,
            chc_ctx.ref_resolution.static_ref_to_state_idx
        );
        let expr = expr.expect("static-mut Deref+Downcast+Field read should translate");

        assert_eq!(
            expr.sort().bitvec_width(),
            Some(32),
            "static-mut Option<u32> payload read should translate to a bv32 payload"
        );
    });

    assert_eq!(
        crate::codegen_ay::take_place_translation_drop_count(),
        0,
        "static-mut enum payload read should not increment place_translation_drop"
    );
    assert_eq!(
        crate::codegen_ay::take_unsupported_field_projection_count(),
        0,
        "static-mut enum payload read should not increment unsupported_field_projection"
    );
}

/// Full-pipeline diagnostic: `mir_to_chc` on the static-mut Option probe should
/// not record translation drops or inferable predicates for the probe function.
/// This is the D2 localizer from the #1836 design — if D1 passes but D2 fails,
/// the bug is on the symbolic-write/coercion path rather than the read path.
#[test]
fn test_static_mut_option_full_pipeline_no_translation_drops() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();

    with_test_ay_ctx_for_source(STATIC_MUT_OPTION_PAYLOAD_SOURCE, |ctx| {
        let fn_name = "probe_static_mut_option_payload";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("body");

        // Clear per-fn counters before the pipeline run
        let _ = crate::codegen_ay::take_translation_drop_by_fn();
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());

        let translation_drops = crate::codegen_ay::take_translation_drop_by_fn();
        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let drop_count = translation_drops.get(fn_name).copied().unwrap_or(0);

        assert_eq!(
            drop_count, 0,
            "{fn_name} should not record translation drops after reborrow fix; \
             drops={translation_drops:?}, sites={translation_sites:?}"
        );
        assert!(
            !translation_sites.contains_key(fn_name),
            "{fn_name} should not record translation-drop site reasons; sites={translation_sites:?}"
        );
    });
}

// =============================================================================
// Raw pointer deref at Ptr level — exercises emit_ptr_obj_valid_check (#2310)
// =============================================================================

const RAW_PTR_DEREF_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]

    pub unsafe fn probe_raw_ptr_deref(ptr: *const u32) -> u32 {
        *ptr
    }
"#;

/// Raw pointer deref at Ptr level should produce valid VC.
#[test]
fn test_raw_ptr_deref_ptr_level_produces_vc() {
    with_test_ay_ctx_for_source(RAW_PTR_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_deref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_raw_ptr_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_raw_ptr_deref", body.blocks.len());
    });
}

/// Raw pointer deref at Mem level should also produce a valid VC.
#[test]
fn test_raw_ptr_deref_mem_level_produces_vc() {
    with_test_ay_ctx_for_source(RAW_PTR_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_raw_ptr_deref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_raw_ptr_deref",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_raw_ptr_deref", body.blocks.len());
    });
}

const VOLATILE_LOAD_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]
    #![feature(core_intrinsics)]

    pub unsafe fn probe_volatile_load(ptr: *const u32) -> u32 {
        std::intrinsics::volatile_load(ptr)
    }
"#;

const VOLATILE_LOAD_ALLOC_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]
    #![feature(core_intrinsics)]

    use std::alloc::{alloc, Layout};

    pub unsafe fn probe_volatile_load_from_alloc() -> u8 {
        let layout = unsafe { Layout::from_size_align_unchecked(1, 1) };
        let ptr = unsafe { alloc(layout) };
        unsafe { std::intrinsics::volatile_load(ptr) }
    }
"#;

/// `volatile_load` is a call terminator, so it must flush the pointer-validity
/// check into an error rule instead of leaving it in pending_checks. (#3636)
#[test]
fn test_volatile_load_emits_obj_valid_error_rule() {
    with_test_ay_ctx_for_source(VOLATILE_LOAD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_volatile_load");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_volatile_load",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mut saw_volatile_load = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(path) = chc_ctx.resolve_callee_path(func)
                && path.ends_with("volatile_load")
            {
                saw_volatile_load = true;
                break;
            }
        }
        assert_mir_pattern_found(saw_volatile_load, "volatile_load call");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_volatile_load",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, "probe_volatile_load", body.blocks.len());

        let error_rules: Vec<_> =
            vc.rules.iter().filter(|rule| rule.head.name == "error").collect();
        assert!(
            !error_rules.is_empty(),
            "volatile_load probe should emit at least one error rule for pointer validity"
        );

        let has_obj_valid_check = error_rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|constraint| {
                let text = constraint.to_string();
                text.contains("obj_valid") && text.contains("select")
            })
        });
        assert!(
            has_obj_valid_check,
            "volatile_load error rules must reference obj_valid select constraints"
        );
    });
}

#[test]
fn test_volatile_load_from_alloc_uses_concrete_heap_address() {
    with_test_ay_ctx_for_source(VOLATILE_LOAD_ALLOC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_volatile_load_from_alloc");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_volatile_load_from_alloc",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let mem_selects: Vec<String> = vc
            .rules
            .iter()
            .flat_map(|rule| rule.body.constraints.iter())
            .filter_map(|constraint| {
                let text = constraint.to_string();
                (text.contains("mem_u8") || text.contains("region_")).then_some(text)
            })
            .take(4)
            .collect();
        // Two acceptable encodings for a concrete heap address:
        //   1. Legacy array-backed mem: Select on a BV64→BV8 array with a
        //      concrete (BitVecConst) index and no free variables.
        //   2. Per-region scalar sidecar: a Var whose name embeds a concrete
        //      address, e.g. `_probe_..._region_N_bv8_at_0x500000000_bv64`.
        //      This is a stronger form of concrete tracking (no symbolic
        //      memory array involved at all).
        let has_concrete_mem_select =
            vc.rules.iter().filter(|rule| rule.head.name != "error").any(|rule| {
                rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| match expr.value() {
                        ExprValue::Select { array, index } => {
                            array.sort().array_sort().is_some_and(|arr| {
                                arr.index_sort.bitvec_width() == Some(64)
                                    && arr.element_sort.bitvec_width() == Some(8)
                            }) && constraint_tree_contains(index, &|inner| {
                                matches!(inner.value(), ExprValue::BitVecConst { .. })
                            }) && !constraint_tree_contains(index, &|inner| {
                                matches!(inner.value(), ExprValue::Var { .. })
                            })
                        }
                        _ => false,
                    })
                })
            });
        let has_concrete_region_sidecar =
            vc.rules.iter().filter(|rule| rule.head.name != "error").any(|rule| {
                rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| match expr.value() {
                        ExprValue::Var { name, .. } => {
                            name.contains("region_") && name.contains("_at_0x")
                        }
                        _ => false,
                    })
                })
            });
        assert!(
            has_concrete_mem_select || has_concrete_region_sidecar,
            "volatile_load from an alloc-backed local should use a concrete heap address \
             (either a concrete-index mem_u8 Select or a region_N_bv8_at_0xADDR sidecar); \
             saw mem_u8 constraints: {mem_selects:?}"
        );
    });
}

// =============================================================================
// Vec-backed volatile_load — exercises try_extract_vec_element_for_load and
// try_volatile_load_via_ptr_add (#4074)
//
// The failing compiletest harness Intrinsics/Volatile/load.rs does:
//   let vec = vec![1, 2];
//   volatile_load(vec.as_ptr())       -> should read fld_data[0]
//   volatile_load(vec.as_ptr().add(1)) -> should read fld_data[1]
//
// These localizers reproduce that exact MIR shape through the full CHC pipeline.
// =============================================================================

const VOLATILE_LOAD_VEC_SOURCE: &str = r#"
    #![allow(dead_code, unsafe_op_in_unsafe_fn)]
    #![feature(core_intrinsics)]

    pub unsafe fn probe_volatile_load_vec() -> (i32, i32) {
        let vec = vec![1_i32, 2_i32];
        let vec_ptr = vec.as_ptr();
        let fst = std::intrinsics::volatile_load(vec_ptr);
        let snd = std::intrinsics::volatile_load(vec_ptr.add(1));
        (fst, snd)
    }
"#;

/// Vec-backed volatile_load should produce a VC that contains fld_data select
/// constraints — proving the Vec element extraction path is wired. Part of #4074.
#[test]
fn test_volatile_load_vec_produces_fld_data_select() {
    with_test_ay_ctx_for_source(VOLATILE_LOAD_VEC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_volatile_load_vec");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_volatile_load_vec", ChcConfig::default());

        assert_vc_structure(&vc, "probe_volatile_load_vec", body.blocks.len());

        // The volatile_load helpers should produce Select expressions on the Vec
        // data array. Two encoding paths exist:
        //   (a) Projected: Select(Var("..._fld3"), idx) — projected state variable
        //   (b) Datatype:  Select(DatatypeSelector("fld_data", ...), idx)
        // Check for either path in non-error rule constraints. Part of #4074.
        let has_data_select =
            vc.rules.iter().filter(|rule| rule.head.name != "error").any(|rule| {
                rule.body.constraints.iter().any(|constraint| {
                    constraint_tree_contains(constraint, &|expr| {
                        if let ExprValue::Select { array, .. } = expr.value() {
                            // Path (a): projected state variable (name contains "fld")
                            if let ExprValue::Var { name, .. } = array.value() {
                                if name.contains("fld") {
                                    return true;
                                }
                            }
                            // Path (b): DatatypeSelector("fld_data")
                            constraint_tree_contains(array, &|inner| {
                                matches!(inner.value(),
                                    ExprValue::DatatypeSelector { selector_name, .. }
                                    if selector_name == "fld_data"
                                )
                            })
                        } else {
                            false
                        }
                    })
                })
            });
        assert!(
            has_data_select,
            "Vec-backed volatile_load should produce data array select constraints (Part of #4074)"
        );
    });
}

/// The VC from Vec volatile_load must NOT leave the destination unconstrained.
/// If both volatile_load calls produce fld_data selects, at least 2 non-error
/// rules should have nontrivial transition constraints. Part of #4074.
#[test]
fn test_volatile_load_vec_has_nontrivial_transitions() {
    with_test_ay_ctx_for_source(VOLATILE_LOAD_VEC_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_volatile_load_vec");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_volatile_load_vec", ChcConfig::default());

        assert_has_nontrivial_transition_constraints(&vc, "probe_volatile_load_vec");
    });
}

// =============================================================================
// Nested deref with field — multi-level ref_target resolution
// =============================================================================

const NESTED_DEREF_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Inner { pub val: u32 }
    pub struct Outer { pub inner: Inner }

    pub fn probe_nested_deref(r: &Outer) -> u32 {
        (*r).inner.val
    }
"#;

/// Nested field access through reference should produce valid VC.
#[test]
fn test_nested_deref_field_produces_vc() {
    with_test_ay_ctx_for_source(NESTED_DEREF_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_nested_deref");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_nested_deref", ChcConfig::default());

        assert_vc_structure(&vc, "probe_nested_deref", body.blocks.len());

        // Inner.val is u32, so bv32 should be in relations
        assert_relation_has_arg_sort(
            &vc,
            "probe_nested_deref",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );
    });
}

// =============================================================================
// Conditional array index — exercises resolve_dead_index_projections (#3117)
//
// When different branches assign different constant indices to the same local,
// the uniqueness validation should skip resolution rather than pick the wrong
// constant. This test verifies that codegen does not crash on such patterns.
// =============================================================================

const CONDITIONAL_ARRAY_INDEX_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_conditional_array_index(arr: [u32; 3], flag: bool) -> u32 {
        let idx = if flag { 0 } else { 2 };
        arr[idx]
    }
"#;

/// Conditional array index with different constants in different branches
/// should produce a valid VC without crashing. The dead-index resolver
/// should either resolve (if only one constant) or safely skip (#3117).
#[test]
fn test_conditional_array_index_produces_vc() {
    with_test_ay_ctx_for_source(CONDITIONAL_ARRAY_INDEX_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_conditional_array_index");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_conditional_array_index", ChcConfig::default());

        assert_vc_structure(&vc, "probe_conditional_array_index", body.blocks.len());
    });
}

// =============================================================================
// Arg-ref array deref with struct elements — exercises resolve_arg_ref_deref (#3116)
//
// Tests that arg-ref path emits bounds checks and handles BV→Datatype
// unflattening when the array element type is a struct.
// =============================================================================

const ARG_REF_ARRAY_STRUCT_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Point { pub x: u32, pub y: u32 }

    pub fn probe_arg_ref_array_struct(arr: &[Point; 2], idx: usize) -> u32 {
        arr[idx].x + arr[idx].y
    }
"#;

/// Arg-ref deref through array of structs should produce valid VC with
/// bounds checks and correct struct field access (#3116).
#[test]
fn test_arg_ref_array_struct_produces_vc() {
    with_test_ay_ctx_for_source(ARG_REF_ARRAY_STRUCT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_arg_ref_array_struct");
        let body = instance.body().expect("body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_arg_ref_array_struct", ChcConfig::default());

        assert_vc_structure(&vc, "probe_arg_ref_array_struct", body.blocks.len());
    });
}
