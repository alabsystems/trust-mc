// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::super::super::codegen_ctx::CollectionProjectionKind;
use super::*;

// ═══════════════════════════════════════════════════════════════════════
// Static pointer Copy/Move propagation regression (Part of #2824)
// ═══════════════════════════════════════════════════════════════════════

/// Probe where a `static mut` pointer is copied through locals before deref.
/// This requires collect_static_state_vars to propagate local mappings via
/// Copy/Move/Cast, or deref/store codegen will lose static-state linkage.
const STATIC_PTR_COPY_CHAIN_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    static mut GLOBAL: u32 = 100;

    pub fn probe_copy_chain_requires_propagation() -> u32 {
        unsafe {
            let p0: *mut u32 = core::ptr::addr_of_mut!(GLOBAL);
            let p1 = p0;
            let p2 = p1;
            *p2 = (*p2).wrapping_add(1);
            GLOBAL
        }
    }
"#;

#[test]
fn test_static_copy_chain_requires_pointer_propagation() {
    with_test_ay_ctx_for_source(STATIC_PTR_COPY_CHAIN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_copy_chain_requires_propagation");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_copy_chain_requires_propagation",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();

        let static_idx = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .position(|(name, _)| {
                name.contains("_static_probe_copy_chain_requires_propagation_GLOBAL")
            })
            .expect("expected static state var for GLOBAL");

        let mapped_locals = chc_ctx
            .ref_resolution
            .static_ref_to_state_idx
            .values()
            .filter(|&&idx| idx == static_idx)
            .count();
        assert!(
            mapped_locals >= 2,
            "expected static ref mapping to propagate through Copy/Move chain; got {mapped_locals}"
        );

        let has_propagated_ref =
            body.blocks.iter().flat_map(|bb| bb.statements.iter()).any(|stmt| {
                let rustc_public::mir::StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    return false;
                };
                let src_local = match rhs {
                    rustc_public::mir::Rvalue::Use(
                        rustc_public::mir::Operand::Copy(place)
                        | rustc_public::mir::Operand::Move(place),
                    ) if place.projection.is_empty() => Some(place.local),
                    rustc_public::mir::Rvalue::Cast(
                        _,
                        rustc_public::mir::Operand::Copy(place)
                        | rustc_public::mir::Operand::Move(place),
                        _,
                    ) if place.projection.is_empty() => Some(place.local),
                    _ => None,
                };
                let Some(src_local) = src_local else {
                    return false;
                };

                lhs.projection.is_empty()
                    && chc_ctx.ref_resolution.static_ref_to_state_idx.get(&src_local).is_some_and(
                        |src_idx| {
                            chc_ctx.ref_resolution.static_ref_to_state_idx.get(&lhs.local)
                                == Some(src_idx)
                        },
                    )
            });
        assert_mir_pattern_found(
            has_propagated_ref,
            "static pointer Copy/Move or Cast propagation",
        );
    });
}

// ═══════════════════════════════════════════════════════════════════════
// Collection/iterator projection flattening tests (Part of #2874)
//
// These tests verify that Vec, VecIntoIter, and HashMap iterator types
// are flattened into scalar/array state vars in CHC relation signatures.
// Without flattening, their Datatype sorts block PDR invariant synthesis.
// ═══════════════════════════════════════════════════════════════════════

const VEC_ITER_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn vec_into_iter_probe() -> Option<u32> {
        let v: Vec<u32> = Vec::new();
        let mut it = v.into_iter();
        it.next()
    }
"#;

/// VecIntoIter locals should be deep-flattened: Vec inner fields + pos.
/// No Datatype sort should remain in any relation signature.
#[test]
fn test_vec_into_iter_projected_no_datatype_sort() {
    with_test_ay_ctx_for_source(VEC_ITER_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_into_iter_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "vec_into_iter_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "VecIntoIter should be projected, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// VecIntoIter deep-flattening should register the local in collection_projection_locals.
#[test]
fn test_vec_into_iter_registered_as_projection() {
    with_test_ay_ctx_for_source(VEC_ITER_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_into_iter_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "vec_into_iter_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // The source calls `v.into_iter()`, so at minimum a VecIntoIter local
        // must exist. A Vec local may also be projected (from the `v` binding).
        let has_vec_into_iter = chc_ctx
            .collections
            .projection_locals
            .values()
            .any(|kind| *kind == CollectionProjectionKind::VecIntoIter);

        assert!(
            has_vec_into_iter,
            "vec_into_iter_probe should register a VecIntoIter projection, got: {:?}",
            chc_ctx.collections.projection_locals
        );
    });
}

/// Deep-flattened VecIntoIter should produce >= 5 state var fields (ptr, len, cap, data, pos).
#[test]
fn test_vec_into_iter_deep_flattening_field_count() {
    with_test_ay_ctx_for_source(VEC_ITER_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_into_iter_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "vec_into_iter_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let iter_local = chc_ctx.collections.projection_locals.iter().find_map(|(local, kind)| {
            if *kind == CollectionProjectionKind::VecIntoIter { Some(*local) } else { None }
        });

        let local = iter_local.expect(
            "vec_into_iter_probe should produce a VecIntoIter projected local; \
             if MIR opts eliminate it, the test source needs updating",
        );
        let field_count = chc_ctx.flattened_field_count(local);
        assert!(
            field_count >= 5,
            "VecIntoIter deep-flattening should produce >= 5 fields (ptr, len, cap, data, pos), got {field_count}"
        );
    });
}

/// mir_to_chc on Vec iteration should produce valid VC with no Datatype sorts.
#[test]
fn test_vec_into_iter_mir_to_chc_no_datatype() {
    with_test_ay_ctx_for_source(VEC_ITER_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_into_iter_probe");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "vec_into_iter_probe", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "vec_into_iter_probe", bb_count);

        for rel in &vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "vec_into_iter_probe VC should have no Datatype sorts, found {:?} in {}",
                    sort,
                    rel.name
                );
            }
        }
    });
}

const VEC_PLAIN_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn vec_plain_probe(v: Vec<u32>) -> usize {
        v.len()
    }
"#;

/// Plain Vec<u32> locals (not iterators) should be all-scalar projected too.
#[test]
fn test_vec_plain_projected_no_datatype_sort() {
    with_test_ay_ctx_for_source(VEC_PLAIN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_plain_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "vec_plain_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                assert!(
                    !sort.is_datatype(),
                    "Vec<u32> should be projected, but relation {} has Datatype sort: {:?}",
                    rel.name,
                    sort
                );
            }
        }
    });
}

/// Plain Vec local should be registered as CollectionProjectionKind::Vec.
#[test]
fn test_vec_plain_registered_as_projection() {
    with_test_ay_ctx_for_source(VEC_PLAIN_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "vec_plain_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "vec_plain_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let has_vec = chc_ctx
            .collections
            .projection_locals
            .values()
            .any(|kind| *kind == CollectionProjectionKind::Vec);

        assert!(
            has_vec,
            "vec_plain_probe should register Vec projection, got: {:?}",
            chc_ctx.collections.projection_locals
        );
    });
}

const HASHMAP_ITER_PROBE_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn hashmap_into_iter_probe() -> Option<(u32, u64)> {
        let m: HashMap<u32, u64> = HashMap::new();
        let mut it = m.into_iter();
        it.next()
    }
"#;

/// HashMapIntoIter locals should be projected — no HashMapIntoIter/IntoIter
/// Datatype sorts remain in relation signatures. Other Datatypes (Option, Tuple)
/// may still appear from the `.next()` return type, which is expected.
#[test]
fn test_hashmap_into_iter_projected_no_iter_datatype_sort() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "hashmap_into_iter_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "hashmap_into_iter_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // Check specifically that no iterator/collection Datatype sorts remain.
        // Option/Tuple Datatypes from `.next()` return type are expected.
        for rel in &chc_ctx.vc.relations {
            for sort in &rel.arg_sorts {
                if let Some(dt_name) = sort.datatype_name() {
                    assert!(
                        !dt_name.contains("IntoIter")
                            && !dt_name.starts_with("HashMap_")
                            && !dt_name.starts_with("Vec_"),
                        "Iterator/collection Datatype should be projected, but relation {} has {:?}",
                        rel.name,
                        dt_name
                    );
                }
            }
        }
    });
}

/// HashMapIntoIter should be registered in collection_projection_locals.
#[test]
fn test_hashmap_into_iter_registered_as_projection() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "hashmap_into_iter_probe");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "hashmap_into_iter_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();

        // HashMap iterator may be classified as HashMapIntoIter or as
        // VecIntoIter (via generic IntoIter pattern match). Either is an
        // iterator-class projection; only Vec (non-iterator) would be wrong.
        let has_iter_projection = chc_ctx.collections.projection_locals.values().any(|kind| {
            matches!(
                kind,
                CollectionProjectionKind::HashMapIntoIter
                    | CollectionProjectionKind::HashSetIntoIter
                    | CollectionProjectionKind::VecIntoIter
            )
        });

        assert!(
            has_iter_projection,
            "hashmap_into_iter_probe should register an iterator-class projection, got: {:?}",
            chc_ctx.collections.projection_locals
        );
    });
}

/// mir_to_chc on HashMap iteration produces valid VC; no iterator Datatypes in signatures.
#[test]
fn test_hashmap_into_iter_mir_to_chc_no_iter_datatype() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_PROBE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "hashmap_into_iter_probe");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "hashmap_into_iter_probe", ChcConfig::default());

        let bb_count = body.blocks.len();
        assert_vc_structure(&vc, "hashmap_into_iter_probe", bb_count);

        // No iterator/collection Datatype should remain in relation signatures.
        // Option/Tuple Datatypes from `.next()` return type are expected.
        for rel in &vc.relations {
            for sort in &rel.arg_sorts {
                if let Some(dt_name) = sort.datatype_name() {
                    assert!(
                        !dt_name.contains("IntoIter")
                            && !dt_name.starts_with("HashMap_")
                            && !dt_name.starts_with("Vec_"),
                        "VC should not have iterator Datatype sorts, found {:?} in {}",
                        dt_name,
                        rel.name
                    );
                }
            }
        }
    });
}
