// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::*;
use rustc_public::ty::GenericArgKind;

// ═══════════════════════════════════════════════════════════════════════
// Option<T> flattening tests (Part of #2214)
// ═══════════════════════════════════════════════════════════════════════

const OPTION_PROBE_SOURCE: &str = r#"
pub fn option_local(x: u32) -> u32 {
    let opt: Option<u32> = Some(x);
    match opt {
        Some(v) => v,
        None => 0,
    }
}

pub fn option_none_local() -> u32 {
    let opt: Option<u32> = None;
    match opt {
        Some(v) => v,
        None => 42,
    }
}
"#;

const OPTION_REF_PROBE_SOURCE: &str = r#"
pub fn option_ref_unit_is_some(opt: Option<&()>) -> bool {
    opt.is_some()
}

pub fn option_ref_u8_is_some(opt: Option<&u8>) -> bool {
    opt.is_some()
}
"#;

const OPTION_REF_COMPOSITE_PROBE_SOURCE: &str = r#"
struct Point {
    x: u8,
    y: bool,
}

pub fn option_ref_tuple_is_some(opt: Option<&(u8, bool)>) -> bool {
    opt.is_some()
}

pub fn option_ref_struct_is_some(opt: Option<&Point>) -> bool {
    opt.is_some()
}
"#;

/// Verify that Option<u32> locals are flattened to 2 scalar state vars (no Datatype).
#[test]
fn test_option_local_flattened_no_datatype_sort() {
    with_test_ay_ctx_for_source(OPTION_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "option_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // No relation argument should have a Datatype sort (Option should be flattened)
        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "Option<u32> should be flattened, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// Verify that flattened Option locals appear in flattened_tuple_locals set.
#[test]
fn test_option_local_in_flattened_set() {
    with_test_ay_ctx_for_source(OPTION_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "option_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // At least one local should be flattened (the Option<u32> local)
        assert!(
            !chc_ctx.flatten.flattened_tuple_locals.is_empty(),
            "option_local should have at least one flattened local (Option<u32>)"
        );
    });
}

/// Verify that flattened Option<u32> produces Bool + bv32 state vars (is_some, value).
#[test]
fn test_option_flattened_produces_bool_and_bv32_state_vars() {
    with_test_ay_ctx_for_source(OPTION_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_local");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "option_local", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Find state vars with _fld0 and _fld1 suffixes (flattened Option fields)
        let fld0_vars: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .filter(|(name, _)| name.contains("_fld0"))
            .collect();
        let fld1_vars: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .filter(|(name, _)| name.contains("_fld1"))
            .collect();

        assert!(!fld0_vars.is_empty(), "should have fld0 state vars from Option flattening");
        assert!(!fld1_vars.is_empty(), "should have fld1 state vars from Option flattening");

        // Check that at least one fld0 is Bool (is_some) and one fld1 is bv32 (value)
        // for the Option<u32> local specifically.
        let has_bool_fld0 = fld0_vars.iter().any(|(_, sort)| sort.is_bool());
        let has_bv32_fld1 = fld1_vars.iter().any(|(_, sort)| sort.bitvec_width() == Some(32));

        assert!(has_bool_fld0, "Option<u32> fld0 (is_some) should be Bool, found: {:?}", fld0_vars);
        assert!(has_bv32_fld1, "Option<u32> fld1 (value) should be bv32, found: {:?}", fld1_vars);
    });
}

#[test]
fn test_option_ref_unit_flattened_to_bool_payload() {
    with_test_ay_ctx_for_source(OPTION_REF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_ref_unit_is_some");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "option_ref_unit_is_some", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(local_idx, decl)| match decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Option" => {
                    args.0.first().and_then(|arg| match arg {
                        GenericArgKind::Type(inner_ty) => match inner_ty.kind() {
                            TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _))
                                if matches!(
                                    pointee_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Tuple(tys)) if tys.is_empty()
                                ) =>
                            {
                                Some(local_idx)
                            }
                            _ => None,
                        },
                        _ => None,
                    })
                }
                _ => None,
            })
            .expect("expected Option<&()> local");

        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&option_local),
            "Option<&()> local should be flattened"
        );

        let vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&option_local)
            .expect("flattened Option<&()> local should have a state-var mapping");
        let fld0_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx].1;
        let fld1_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx + 1].1;

        assert!(fld0_sort.is_bool(), "Option<&()> fld0 should be Bool, got {fld0_sort:?}");
        assert!(fld1_sort.is_bool(), "Option<&()> fld1 should be Bool, got {fld1_sort:?}");
    });
}

#[test]
fn test_option_ref_u8_flattened_to_value_payload_width() {
    with_test_ay_ctx_for_source(OPTION_REF_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_ref_u8_is_some");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "option_ref_u8_is_some", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(local_idx, decl)| match decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Option" => {
                    args.0.first().and_then(|arg| match arg {
                        GenericArgKind::Type(inner_ty) => match inner_ty.kind() {
                            TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _))
                                if matches!(
                                    pointee_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Uint(UintTy::U8))
                                ) =>
                            {
                                Some(local_idx)
                            }
                            _ => None,
                        },
                        _ => None,
                    })
                }
                _ => None,
            })
            .expect("expected Option<&u8> local");

        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&option_local),
            "Option<&u8> local should be flattened"
        );

        let vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&option_local)
            .expect("flattened Option<&u8> local should have a state-var mapping");
        let fld0_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx].1;
        let fld1_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx + 1].1;

        assert!(fld0_sort.is_bool(), "Option<&u8> fld0 should be Bool, got {fld0_sort:?}");
        assert_eq!(
            fld1_sort.bitvec_width(),
            Some(8),
            "Option<&u8> fld1 should be bv8, got {fld1_sort:?}"
        );
    });
}

#[test]
fn test_option_ref_tuple_flattened_to_bool_u8_bool() {
    with_test_ay_ctx_for_source(OPTION_REF_COMPOSITE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_ref_tuple_is_some");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "option_ref_tuple_is_some", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(local_idx, decl)| match decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Option" => {
                    args.0.first().and_then(|arg| match arg {
                        GenericArgKind::Type(inner_ty) => match inner_ty.kind() {
                            TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _))
                                if matches!(
                                    pointee_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Tuple(tys))
                                        if tys.len() == 2
                                            && matches!(
                                                tys[0].kind(),
                                                TyKind::RigidTy(RigidTy::Uint(UintTy::U8))
                                            )
                                            && matches!(
                                                tys[1].kind(),
                                                TyKind::RigidTy(RigidTy::Bool)
                                            )
                                ) =>
                            {
                                Some(local_idx)
                            }
                            _ => None,
                        },
                        _ => None,
                    })
                }
                _ => None,
            })
            .expect("expected Option<&(u8, bool)> local");

        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&option_local),
            "Option<&(u8, bool)> local should be flattened"
        );

        let vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&option_local)
            .expect("flattened Option<&(u8, bool)> local should have a state-var mapping");
        let fld0_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx].1;
        let fld1_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx + 1].1;
        let fld2_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx + 2].1;

        assert!(fld0_sort.is_bool(), "Option<&(u8, bool)> fld0 should be Bool, got {fld0_sort:?}");
        assert_eq!(
            fld1_sort.bitvec_width(),
            Some(8),
            "Option<&(u8, bool)> fld1 should be bv8, got {fld1_sort:?}"
        );
        assert!(fld2_sort.is_bool(), "Option<&(u8, bool)> fld2 should be Bool, got {fld2_sort:?}");
    });
}

#[test]
fn test_option_ref_struct_flattened_to_bool_u8_bool() {
    with_test_ay_ctx_for_source(OPTION_REF_COMPOSITE_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_ref_struct_is_some");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "option_ref_struct_is_some", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let option_local = body
            .locals()
            .iter()
            .enumerate()
            .find_map(|(local_idx, decl)| match decl.ty.kind() {
                TyKind::RigidTy(RigidTy::Adt(def, args)) if def.trimmed_name() == "Option" => {
                    args.0.first().and_then(|arg| match arg {
                        GenericArgKind::Type(inner_ty) => match inner_ty.kind() {
                            TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, _))
                                if matches!(
                                    pointee_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Adt(def, _))
                                        if def.trimmed_name() == "Point"
                                ) =>
                            {
                                Some(local_idx)
                            }
                            _ => None,
                        },
                        _ => None,
                    })
                }
                _ => None,
            })
            .expect("expected Option<&Point> local");

        assert!(
            chc_ctx.flatten.flattened_tuple_locals.contains(&option_local),
            "Option<&Point> local should be flattened"
        );

        let vec_idx = *chc_ctx
            .state_var_mgr
            .local_to_state_idx
            .get(&option_local)
            .expect("flattened Option<&Point> local should have a state-var mapping");
        let fld0_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx].1;
        let fld1_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx + 1].1;
        let fld2_sort = &chc_ctx.state_var_mgr.state_vars[vec_idx + 2].1;

        assert!(fld0_sort.is_bool(), "Option<&Point> fld0 should be Bool, got {fld0_sort:?}");
        assert_eq!(
            fld1_sort.bitvec_width(),
            Some(8),
            "Option<&Point> fld1 should be bv8, got {fld1_sort:?}"
        );
        assert!(fld2_sort.is_bool(), "Option<&Point> fld2 should be Bool, got {fld2_sort:?}");
    });
}

/// Verify that mir_to_chc on Option-using function produces valid VC structure.
#[test]
fn test_option_mir_to_chc_valid_vc() {
    with_test_ay_ctx_for_source(OPTION_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "option_local");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "option_local", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "option_local", bb_count);

        // Verify no Datatype sorts in any relation signature
        for rel in &vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "option_local VC should have no Datatype sorts after flattening, found {:?} in {}",
                    sort,
                    rel.name
                );
            }
        }
    });
}

// ═══════════════════════════════════════════════════════════════════════
// General scalar tuple flattening tests (Part of #2214)
// ═══════════════════════════════════════════════════════════════════════

const TUPLE_SCALAR_PROBE_SOURCE: &str = r#"
pub fn tuple_bv_bv(x: u32, y: u64) -> u64 {
    let pair: (u32, u64) = (x, y);
    pair.1
}

pub fn tuple_bv_int(x: usize, y: u32) -> u32 {
    let pair: (usize, u32) = (x, y);
    pair.1
}

pub fn tuple_bv_bv_bool(x: u32, y: u64, z: bool) -> u64 {
    let triple: (u32, u64, bool) = (x, y, z);
    if triple.2 { triple.1 } else { 0 }
}
"#;

/// Verify that (u32, u64) tuples are flattened (no Datatype sort in relations).
#[test]
fn test_general_tuple_flattened_no_datatype_sort() {
    with_test_ay_ctx_for_source(TUPLE_SCALAR_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_bv_bv");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "tuple_bv_bv", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "(u32, u64) should be flattened, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// Verify that general tuple locals appear in flattened_tuple_locals set.
#[test]
fn test_general_tuple_in_flattened_set() {
    with_test_ay_ctx_for_source(TUPLE_SCALAR_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_bv_bv");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "tuple_bv_bv", ChcConfig::default());
        chc_ctx.declare_block_relations();

        assert!(
            !chc_ctx.flatten.flattened_tuple_locals.is_empty(),
            "tuple_bv_bv should have at least one flattened local"
        );
    });
}

/// Verify that flattened (u32, u64) produces bv32 + bv64 state vars.
#[test]
fn test_general_tuple_produces_correct_sort_widths() {
    with_test_ay_ctx_for_source(TUPLE_SCALAR_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_bv_bv");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "tuple_bv_bv", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for &local_idx in &chc_ctx.flatten.flattened_tuple_locals {
            if let Some(&vec_idx) = chc_ctx.state_var_mgr.local_to_state_idx.get(&local_idx) {
                let fld0 = &chc_ctx.state_var_mgr.state_vars[vec_idx];
                let fld1 = &chc_ctx.state_var_mgr.state_vars[vec_idx + 1];
                // Both fields should be scalar (not Datatype)
                assert!(
                    fld0.1.is_bitvec() || fld0.1.is_bool() || fld0.1.is_int(),
                    "fld0 should be scalar, got {:?}",
                    fld0.1
                );
                assert!(
                    fld1.1.is_bitvec() || fld1.1.is_bool() || fld1.1.is_int(),
                    "fld1 should be scalar, got {:?}",
                    fld1.1
                );
            }
        }
    });
}

/// Verify general tuple local is NOT in flattened_enum_discr (not an enum).
#[test]
fn test_general_tuple_not_in_enum_discr() {
    with_test_ay_ctx_for_source(TUPLE_SCALAR_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_bv_bv");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "tuple_bv_bv", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for &local_idx in &chc_ctx.flatten.flattened_tuple_locals {
            assert!(
                !chc_ctx.flatten.flattened_enum_discr.contains_key(&local_idx),
                "general tuple local {} should NOT be in flattened_enum_discr",
                local_idx
            );
        }
    });
}

/// Verify that (u32, u64, bool) tuples are flattened (no Datatype sort in relations).
#[test]
fn test_general_triple_tuple_flattened_no_datatype_sort() {
    with_test_ay_ctx_for_source(TUPLE_SCALAR_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_bv_bv_bool");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "tuple_bv_bv_bool", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "(u32, u64, bool) should be flattened, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// Verify that 3-field tuples register field_count=3 and expected scalar sorts.
#[test]
fn test_general_triple_tuple_tracks_three_flattened_fields() {
    with_test_ay_ctx_for_source(TUPLE_SCALAR_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_bv_bv_bool");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "tuple_bv_bv_bool", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let has_expected_triple = chc_ctx.flatten.flattened_tuple_locals.iter().any(|&local_idx| {
            if chc_ctx.flatten.flattened_local_field_count.get(&local_idx).copied() != Some(3) {
                return false;
            }
            let Some(&vec_idx) = chc_ctx.state_var_mgr.local_to_state_idx.get(&local_idx) else {
                return false;
            };
            let Some((_, fld0_sort)) = chc_ctx.state_var_mgr.state_vars.get(vec_idx) else {
                return false;
            };
            let Some((_, fld1_sort)) = chc_ctx.state_var_mgr.state_vars.get(vec_idx + 1) else {
                return false;
            };
            let Some((_, fld2_sort)) = chc_ctx.state_var_mgr.state_vars.get(vec_idx + 2) else {
                return false;
            };
            fld0_sort.bitvec_width() == Some(32)
                && fld1_sort.bitvec_width() == Some(64)
                && fld2_sort.is_bool()
        });

        assert!(
            has_expected_triple,
            "should find flattened (u32, u64, bool) local with 3 scalar fields"
        );
    });
}
