// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Nested field stores through a reference into a flattened owner
//! (`let r = &mut o; r.inner.b = 42;`), mirrored by `mirror_scalar_ref_store`
//! (`stmt/codegen_stmt_store/deref_mem_mirror.rs`), and the slot resolver
//! behind it (`expr/codegen_expr_flat_struct_path.rs`).
//!
//! Tracker: `tools/soundness-duals/nested_field_ref_write_dual.rs`. The mirror
//! used to end in a warn-only arm for a path of two or more fields, which lost
//! the write, so `assert!(o.inner.a == 0)` after `r.inner.a = 7` was proved.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::stmt_accumulator::StmtAccumulator;
use super::common::*;
use crate::rustc_compat::prelude::*;
use rustc_public::mir::{Body, Mutability, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::Ty;
use std::collections::HashMap;

/// `P { inner: Q { a, b }, c }` flattens to three u32 slots `[inner.a,
/// inner.b, c]`; `R { p: P, d }` to four.
const NESTED_MIRROR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub struct Q { pub a: u32, pub b: u32 }
    pub struct P { pub inner: Q, pub c: u32 }
    pub struct R { pub p: P, pub d: u32 }
    pub struct P3 { pub inner: (Q,), pub c: u32 }
    pub struct PC { pub inner: core::cell::Cell<Q>, pub c: u32 }
    pub struct PM { pub m: core::mem::ManuallyDrop<P>, pub c: u32 }
    pub struct L4 { pub x: u8, pub y: u8 }
    pub struct L3 { pub l4: L4 }
    pub struct L2 { pub l3: L3 }
    pub struct L1 { pub l2: L2 }
    pub struct L0 { pub l1: L1, pub z: u8 }

    pub fn nested_mirror_probe() -> u32 {
        let mut o = P { inner: Q { a: 0, b: 0 }, c: 0 };
        let r = &mut o;
        r.inner.b = 42;
        o.c
    }

    pub fn three_level_probe() -> u32 {
        let mut o = R { p: P { inner: Q { a: 0, b: 0 }, c: 0 }, d: 0 };
        let r = &mut o;
        r.p.inner.b = 42;
        o.d
    }

    pub fn tuple_root_probe() -> u32 {
        let mut t = (P { inner: Q { a: 0, b: 0 }, c: 0 },);
        let r = &mut t;
        r.0.c = 42;
        t.0.inner.a
    }

    pub fn tuple_interior_probe() -> u32 {
        let mut o = P3 { inner: (Q { a: 0, b: 0 },), c: 0 };
        let r = &mut o;
        r.inner.0.b = 42;
        o.c
    }

    pub fn cell_probe() -> u32 {
        let o = PC { inner: core::cell::Cell::new(Q { a: 0, b: 0 }), c: 0 };
        o.c
    }

    pub fn md_probe() -> u32 {
        let o = PM { m: core::mem::ManuallyDrop::new(P { inner: Q { a: 0, b: 0 }, c: 0 }), c: 0 };
        o.c
    }

    pub fn deep_probe() -> u8 {
        let mut o = L0 { l1: L1 { l2: L2 { l3: L3 { l4: L4 { x: 0, y: 0 } } } }, z: 0 };
        let r = &mut o;
        r.z = 7;
        o.l1.l2.l3.l4.x
    }

    pub fn direct_interior_probe() -> u32 {
        let mut o = P3 { inner: (Q { a: 0, b: 0 },), c: 0 };
        o.inner.0.b = 42;
        o.c
    }

    pub fn direct_deep_probe() -> u8 {
        let mut o = L0 { l1: L1 { l2: L2 { l3: L3 { l4: L4 { x: 0, y: 0 } } } }, z: 0 };
        o.l1.l2.l3.l4.y = 7;
        o.z
    }

    pub fn direct_root_tuple_probe() -> u32 {
        let mut t = (P { inner: Q { a: 0, b: 0 }, c: 0 },);
        t.0.c = 42;
        t.0.inner.b
    }

    pub fn box_as_mut_probe() -> u32 {
        let mut b = Box::new(Q { a: 0, b: 0 });
        b.as_mut().a = 42;
        b.b
    }

    pub fn tuple_zst_probe() -> u32 {
        let t = (5u32, ());
        let u = (5u32, 6u8);
        t.0 + u.0 as u32
    }
"#;

/// The `(*r).<fields> = ..` store with `depth` fields after the Deref, the
/// reference local, and the owner that `r = &mut o` borrows.
fn find_deref_field_store(body: &Body, depth: usize) -> (Place, usize, usize) {
    let mut store = None;
    let mut borrows: HashMap<usize, usize> = HashMap::new();
    for bb in &body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
            if let Rvalue::Ref(_, _, place) = rhs
                && place.projection.is_empty()
            {
                borrows.insert(lhs.local, place.local);
            }
            if lhs.projection.len() == depth + 1
                && matches!(lhs.projection[0], ProjectionElem::Deref)
                && lhs.projection[1..].iter().all(|p| matches!(p, ProjectionElem::Field(..)))
            {
                store = Some(lhs.clone());
            }
        }
    }
    let store = store.expect("the probe keeps a (*r).<fields> store in its MIR");
    let owner = *borrows.get(&store.local).expect("the reference borrows the owner");
    let ref_local = store.local;
    (store, ref_local, owner)
}

/// MIR type of field `idx` of a struct or tuple type.
fn field_ty(ty: Ty, idx: usize) -> Ty {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            def.variants()[0].fields()[idx].ty_with_args(&args)
        }
        TyKind::RigidTy(RigidTy::Tuple(elems)) => elems[idx],
        other => panic!("not a struct or tuple: {other:?}"),
    }
}

/// Field projections for `indices`, walked from `root`'s MIR type.
fn field_path(root: Ty, indices: &[usize]) -> Vec<FieldProjection> {
    let mut ty = root;
    let mut path = Vec::with_capacity(indices.len());
    for &idx in indices {
        ty = field_ty(ty, idx);
        path.push(FieldProjection { field_idx: idx, cons_idx: None, field_ty: Some(ty) });
    }
    path
}

fn field_place(owner: usize, root: Ty, indices: &[usize]) -> Place {
    let mut ty = root;
    let mut projection = Vec::with_capacity(indices.len());
    for &idx in indices {
        ty = field_ty(ty, idx);
        projection.push(ProjectionElem::Field(idx, ty));
    }
    Place { local: owner.into(), projection }
}

fn mem_ctx<'tcx, 'body>(tcx: TyCtxt<'tcx>, body: &'body Body, name: &str) -> ChcCtx<'tcx, 'body> {
    let mut chc_ctx = ChcCtx::new(
        tcx,
        body,
        name,
        ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
    );
    chc_ctx.declare_block_relations();
    chc_ctx
}

/// One mirror call on fresh accumulators; returns (constraints, key -> index,
/// modified).
fn run_mirror(
    chc_ctx: &mut ChcCtx<'_, '_>,
    ref_target: RefTarget,
    lhs: &Place,
    rhs: &Expr,
    ref_local: usize,
    modified_before: HashSet<usize>,
) -> (Vec<Expr>, HashMap<usize, usize>, HashSet<usize>) {
    let mut modified = modified_before;
    let mut constraints = Vec::new();
    let mut last_constraint_for_local: HashMap<usize, usize> = HashMap::new();
    {
        let mut acc =
            StmtAccumulator::new(&mut modified, &mut constraints, &mut last_constraint_for_local);
        chc_ctx.mirror_scalar_ref_store(
            &ref_target,
            lhs,
            rhs,
            ref_local,
            rustc_public::ty::Ty::unsigned_ty(UintTy::U32),
            &mut acc,
        );
    }
    (constraints, last_constraint_for_local, modified)
}

fn slot_constraint(
    chc_ctx: &ChcCtx<'_, '_>,
    constraints: &[Expr],
    keys: &HashMap<usize, usize>,
    owner: usize,
    slot: usize,
) -> String {
    let key = chc_ctx.flattened_field_constraint_key(owner, slot);
    let idx = keys.get(&key).unwrap_or_else(|| panic!("slot {slot} key must be registered"));
    constraints[*idx].to_string()
}

/// Assert the fail-closed shape: one FailClose drop with `reason`, every slot
/// key registered as `true`, the owner modified, no cached value left.
fn assert_failed_closed(
    chc_ctx: &ChcCtx<'_, '_>,
    fn_name: &str,
    reason: &str,
    drops_before: usize,
    run: &(Vec<Expr>, HashMap<usize, usize>, HashSet<usize>),
    owner: usize,
) {
    let (constraints, keys, modified) = run;
    assert_eq!(
        chc_ctx.diagnostics.place_translation_drop.get(),
        drops_before + 1,
        "the refused mirror must record one FailClose drop"
    );
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    assert_eq!(
        reasons.get(fn_name).and_then(|m| m.get(reason)),
        Some(&1),
        "expected the {reason} reason, got {reasons:?}"
    );
    for slot in 0..chc_ctx.flattened_field_count(owner) {
        assert_eq!(
            slot_constraint(chc_ctx, constraints, keys, owner, slot),
            Expr::bool_const(true).to_string(),
            "slot {slot} must take its free output variable"
        );
    }
    assert!(modified.contains(&owner), "the owner must be marked modified");
    assert!(
        !chc_ctx.encode.flattened_field_env.keys().any(|(local, _)| *local == owner),
        "no cached value of the owner may survive the failed mirror"
    );
}

fn with_counter_guard(test: impl FnOnce()) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    test();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
}

/// The resolver names the same slots the read side does, at any depth, for
/// leaves and for whole sub-structs.
#[test]
fn test_resolve_flat_struct_path_nested_levels() {
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "nested_mirror_probe");
        let body = instance.body().expect("body");
        let (lhs, _, owner) = find_deref_field_store(&body, 2);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "resolve_nested_levels");
        let p_ty = body.locals()[owner].ty;

        let store_path =
            collect_field_projections(&lhs.projection[1..], UnknownProjectionPolicy::Break);
        let span = chc_ctx.resolve_flat_struct_path(owner, &store_path).expect("inner.b");
        assert_eq!((span.offset, span.count), (1, 1), "inner.b is the second leaf");
        assert_eq!(span.declared.len(), 3);
        let inner = chc_ctx.resolve_flat_struct_path(owner, &field_path(p_ty, &[0])).unwrap();
        assert_eq!((inner.offset, inner.count), (0, 2), "inner spans two leaves");
        let c = chc_ctx.resolve_flat_struct_path(owner, &field_path(p_ty, &[1])).unwrap();
        assert_eq!((c.offset, c.count), (2, 1), "c follows both leaves of inner");
    });
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "three_level_probe");
        let body = instance.body().expect("body");
        let (lhs, _, owner) = find_deref_field_store(&body, 3);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "resolve_three_levels");
        let r_ty = body.locals()[owner].ty;

        let store_path =
            collect_field_projections(&lhs.projection[1..], UnknownProjectionPolicy::Break);
        let span = chc_ctx.resolve_flat_struct_path(owner, &store_path).expect("p.inner.b");
        assert_eq!((span.offset, span.count), (1, 1));
        let d = chc_ctx.resolve_flat_struct_path(owner, &field_path(r_ty, &[1])).unwrap();
        assert_eq!((d.offset, d.count), (3, 1), "d follows the three leaves of p");
        let p = chc_ctx.resolve_flat_struct_path(owner, &field_path(r_ty, &[0])).unwrap();
        assert_eq!((p.offset, p.count), (0, 3));
    });
}

/// `translate_ty((T,))` is T's sort, so a single-element tuple step consumes
/// no sort level, at the root or inside the path (C5b): the read side drops
/// it the same way (`flat_field_path`), so a write and a read of `o.inner.0.b`
/// name one slot. It used to be refused inside, because the readers walked
/// the MIR indices over the sort tree raw and landed on another leaf there
/// (`r.a.0.x.r1 = v; assert!(o.a.0.y == v)` was proved).
#[test]
fn test_resolve_flat_struct_path_drops_sort_identity_steps() {
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_root_probe");
        let body = instance.body().expect("body");
        let (lhs, _, owner) = find_deref_field_store(&body, 2);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "resolve_tuple_root");
        let path = collect_field_projections(&lhs.projection[1..], UnknownProjectionPolicy::Break);
        let span = chc_ctx.resolve_flat_struct_path(owner, &path).expect("t.0.c");
        assert_eq!((span.offset, span.count), (2, 1), "t.0.c is P's third leaf, not Q's b");
    });
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_interior_probe");
        let body = instance.body().expect("body");
        let (lhs, _, owner) = find_deref_field_store(&body, 3);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "resolve_tuple_interior");
        let path = collect_field_projections(&lhs.projection[1..], UnknownProjectionPolicy::Break);
        let span = chc_ctx.resolve_flat_struct_path(owner, &path).expect("o.inner.0.b");
        assert_eq!(
            (span.offset, span.count),
            (1, 1),
            "o.inner.0.b is Q's second leaf (slot 1), not c (slot 2)"
        );
        // The interior tuple as a whole is still a plain field: `o.inner`.
        let p3_ty = body.locals()[owner].ty;
        let inner = chc_ctx.resolve_flat_struct_path(owner, &field_path(p3_ty, &[0])).unwrap();
        assert_eq!((inner.offset, inner.count), (0, 2));
    });
}

/// The path read case C, the direct nested write and the stack Deref+Field
/// read place (`faithful_flat_field_path`, C5b): a sort-identity step is
/// dropped wherever it is, an ordinary step is kept, and a walk past the
/// depth cap has no faithful slot.
#[test]
fn test_faithful_flat_field_path() {
    let indices =
        |path: Vec<FieldProjection>| -> Vec<usize> { path.iter().map(|fp| fp.field_idx).collect() };
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_interior_probe");
        let body = instance.body().expect("body");
        let (_, _, owner) = find_deref_field_store(&body, 3);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "refusal_interior");
        let p3_ty = body.locals()[owner].ty;
        let inner_b = chc_ctx.faithful_flat_field_path(owner, &field_path(p3_ty, &[0, 0, 1]));
        assert_eq!(inner_b.map(indices), Ok(vec![0, 1]), "o.inner.0.b drops the (Q,) step");
        assert_eq!(chc_ctx.flat_slot_for(owner, &field_path(p3_ty, &[0, 0, 1])), Ok(1));
        assert_eq!(
            chc_ctx.faithful_flat_field_path(owner, &field_path(p3_ty, &[1])).map(indices),
            Ok(vec![1])
        );
    });
    // ManuallyDrop<P> is `{ value: MaybeDangling<P> }` and MaybeDangling<P> is
    // `(P)`, both with P's sort: neither step has a level, and `m.value.0.c`
    // is P's third leaf. (The old refusal test walked `[0, 0, 1]`, as if
    // `value` were P, and panicked on MaybeDangling's one field.)
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "md_probe");
        let body = instance.body().expect("body");
        let chc_ctx = mem_ctx(ctx.tcx, &body, "refusal_wrapper");
        let owner = body
            .locals()
            .iter()
            .position(|decl| {
                matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "PM")
            })
            .expect("the PM local");
        assert!(chc_ctx.flatten.flattened_tuple_locals.contains(&owner));
        let pm_ty = body.locals()[owner].ty;
        assert_eq!(
            chc_ctx.faithful_flat_field_path(owner, &field_path(pm_ty, &[0, 0, 0, 1])).map(indices),
            Ok(vec![0, 1]),
            "m.value.0.c: the ManuallyDrop and MaybeDangling steps are the identity"
        );
        assert_eq!(chc_ctx.flat_slot_for(owner, &field_path(pm_ty, &[0, 0, 0, 1])), Ok(2));
        assert_eq!(chc_ctx.flat_slot_for(owner, &field_path(pm_ty, &[1])), Ok(3));
    });
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deep_probe");
        let body = instance.body().expect("body");
        let (_, _, owner) = find_deref_field_store(&body, 1);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "refusal_deep");
        let l0_ty = body.locals()[owner].ty;
        assert_eq!(
            chc_ctx.faithful_flat_field_path(owner, &field_path(l0_ty, &[0, 0, 0, 0, 1])).err(),
            Some("flat_layout_depth_capped")
        );
    });
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "nested_mirror_probe");
        let body = instance.body().expect("body");
        let (_, _, owner) = find_deref_field_store(&body, 2);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "refusal_plain");
        let p_ty = body.locals()[owner].ty;
        assert_eq!(
            chc_ctx.faithful_flat_field_path(owner, &field_path(p_ty, &[0, 1])).map(indices),
            Ok(vec![0, 1])
        );
    });
}

/// Read case C refuses a nested path with no faithful slot instead of reading
/// another leaf: `o.l1.l2.l3.l4.x` on the five-level L0 read past the capped
/// L4 slot. (`o.inner.0.b` on `P3 { inner: (Q,), c }` used to be refused here
/// too; it is now placed exactly, `test_flattened_nested_read_drops_sort_identity_steps`.)
#[test]
fn test_flattened_nested_read_refuses_unfaithful_path() {
    for (probe, depth, indices, fn_name) in
        [("deep_probe", 1, vec![0usize, 0, 0, 0, 0], "read_deep")]
    {
        with_counter_guard(|| {
            with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
                let instance = find_instance_by_suffix(ctx.tcx, probe);
                let body = instance.body().expect("body");
                let (_, _, owner) = find_deref_field_store(&body, depth);
                let chc_ctx = mem_ctx(ctx.tcx, &body, fn_name);
                let owner_ty = body.locals()[owner].ty;
                let read = field_place(owner, owner_ty, &indices);
                let drops_before = chc_ctx.diagnostics.place_translation_drop.get();
                assert_eq!(
                    chc_ctx.translate_place_with_modified(&read, &HashSet::new()),
                    None,
                    "{probe}: the read has no faithful slot"
                );
                assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), drops_before + 1);
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
                assert_eq!(
                    reasons.get(fn_name).and_then(|m| m.get("flattened_nested_path_unfaithful")),
                    Some(&1),
                    "got {reasons:?}"
                );
            });
        });
    }
}

/// Read case C drops a sort-identity step wherever it is (C5b): `o.inner.0.b`
/// on `P3 { inner: (Q,), c }` reads Q's second leaf, slot 1, exactly.
#[test]
fn test_flattened_nested_read_drops_sort_identity_steps() {
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_interior_probe");
        let body = instance.body().expect("body");
        let (_, _, owner) = find_deref_field_store(&body, 3);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "read_interior");
        let owner_ty = body.locals()[owner].ty;
        let read = field_place(owner, owner_ty, &[0, 0, 1]);
        let drops_before = chc_ctx.diagnostics.place_translation_drop.get();
        let value = chc_ctx
            .translate_place_with_modified(&read, &HashSet::new())
            .expect("o.inner.0.b has a faithful slot");
        assert!(
            value.to_string().contains(&format!("_{owner}_fld1")),
            "o.inner.0.b reads slot 1 (Q's b), got {value}"
        );
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), drops_before);
    });
}

/// The direct nested write (`o.a.b = v`, no reference) places its slot the way
/// read case C reads it, or fails closed on every slot.
#[test]
fn test_direct_nested_store_places_or_fails_closed() {
    // Unfaithful paths: every slot takes its free output variable.
    for (probe, fn_name) in [("direct_deep_probe", "direct_deep")] {
        with_counter_guard(|| {
            with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
                let instance = find_instance_by_suffix(ctx.tcx, probe);
                let body = instance.body().expect("body");
                let mut chc_ctx = mem_ctx(ctx.tcx, &body, fn_name);
                let (bb, owner) = find_direct_nested_store(&body);
                let (constraints, _, modified, _) = chc_ctx.encode_block_statements(bb);
                let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
                assert_eq!(
                    reasons.get(fn_name).and_then(|m| m.get("flat_nested_store_unfaithful")),
                    Some(&1),
                    "{probe}: expected the fail-closed reason, got {reasons:?}"
                );
                assert!(modified.contains(&owner));
                let stored = constraints.iter().any(|c| {
                    let c = c.to_string();
                    c.contains("__out") && (c.contains("#x0000002a") || c.contains("#x07"))
                });
                assert!(!stored, "{probe}: no slot may take the stored value: {constraints:?}");
            });
        });
    }
    // A root single-element tuple is peeled as the read peels it: `t.0.c` is
    // P's third leaf (slot 2), not `inner.b` (slot 1).
    with_counter_guard(|| {
        with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "direct_root_tuple_probe");
            let body = instance.body().expect("body");
            let mut chc_ctx = mem_ctx(ctx.tcx, &body, "direct_root_tuple");
            let (bb, owner) = find_direct_nested_store(&body);
            let (constraints, _, _, _) = chc_ctx.encode_block_statements(bb);
            let writes = |slot: usize| {
                let var = format!("_{owner}_fld{slot}__out");
                constraints.iter().any(|c| {
                    let c = c.to_string();
                    c.contains(&var) && c.contains("#x0000002a")
                })
            };
            assert!(writes(2), "t.0.c must be stored in slot 2: {constraints:?}");
            assert!(!writes(1), "t.0.c must not land on inner.b: {constraints:?}");
        });
    });
    // An interior single-element tuple is dropped the same way (C5b):
    // `o.inner.0.b` is Q's second leaf (slot 1), not c (slot 2).
    with_counter_guard(|| {
        with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "direct_interior_probe");
            let body = instance.body().expect("body");
            let mut chc_ctx = mem_ctx(ctx.tcx, &body, "direct_interior");
            let (bb, owner) = find_direct_nested_store(&body);
            let (constraints, _, _, _) = chc_ctx.encode_block_statements(bb);
            let writes = |slot: usize| {
                let var = format!("_{owner}_fld{slot}__out");
                constraints.iter().any(|c| {
                    let c = c.to_string();
                    c.contains(&var) && c.contains("#x0000002a")
                })
            };
            assert!(writes(1), "o.inner.0.b must be stored in slot 1: {constraints:?}");
            assert!(!writes(2), "o.inner.0.b must not land on c: {constraints:?}");
        });
    });
}

/// The block and owner of the one direct `_o.<fields> = ..` store with two or
/// more Field projections and no Deref.
fn find_direct_nested_store(body: &Body) -> (usize, usize) {
    for (bb_idx, bb) in body.blocks.iter().enumerate() {
        for stmt in &bb.statements {
            let StatementKind::Assign(lhs, _) = &stmt.kind else { continue };
            if lhs.projection.len() >= 2
                && lhs.projection.iter().all(|p| matches!(p, ProjectionElem::Field(..)))
            {
                return (bb_idx, lhs.local);
            }
        }
    }
    panic!("the probe keeps a direct nested field store in its MIR");
}

/// A reference that points THROUGH a pointer-typed ref_target place --
/// `Box::as_mut` registers `_r -> b.[Field(Unique), Field(NonNull)]` -- has
/// its referent behind that pointer, written by the Mem-level store. The
/// owner's register holds only the pointer, so the mirror leaves it alone and
/// records nothing. Failing it closed havocked the Box's pointer, and the next
/// `*b` tripped the alignment check on an arbitrary address.
#[test]
fn test_deref_mem_mirror_skips_ref_target_through_pointer() {
    with_counter_guard(|| {
        with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "box_as_mut_probe");
            let body = instance.body().expect("body");
            let fn_name = "mirror_through_pointer";
            let mut chc_ctx = mem_ctx(ctx.tcx, &body, fn_name);
            let is_box = |ty: Ty| matches!(ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "Box");
            let owner = body.locals().iter().position(|d| is_box(d.ty)).expect("the Box local");
            let box_ty = body.locals()[owner].ty;
            let ref_local = body
                .locals()
                .iter()
                .position(|d| {
                    matches!(d.ty.kind(), TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut)))
                })
                .expect("the &mut Q from as_mut");
            let q_ty = match body.locals()[ref_local].ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                _ => unreachable!(),
            };
            // b.0: Unique<Q>, b.0.0: NonNull<Q>.
            let through = field_place(owner, box_ty, &[0, 0]).projection;
            let mut lhs = field_place(ref_local, q_ty, &[0]);
            lhs.projection.insert(0, ProjectionElem::Deref);
            let drops_before = chc_ctx.diagnostics.place_translation_drop.get();

            let (constraints, keys, modified) = run_mirror(
                &mut chc_ctx,
                RefTarget::with_projections(owner, through),
                &lhs,
                &Expr::bitvec_const(42u64, 32),
                ref_local,
                HashSet::new(),
            );
            assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), drops_before);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            assert!(reasons.get(fn_name).is_none(), "no fallback expected, got {reasons:?}");
            assert!(constraints.is_empty() && keys.is_empty(), "nothing is mirrored");
            assert!(!modified.contains(&owner), "the Box's pointer is unchanged");
        });
    });
}

/// A Cell step is a sort-identity step (C5b: `translate_adt_ty` collapses
/// `Cell<Q>` and its `UnsafeCell<Q>` to Q's sort), so `inner.value` is all of
/// Q and `inner.value.value.b` is Q's second leaf. Refusals: an enum
/// Downcast, a depth-capped datatype slot, an empty path, and a local that is
/// not flattened.
#[test]
fn test_resolve_flat_struct_path_refuses_unfaithful_paths() {
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "cell_probe");
        let body = instance.body().expect("body");
        let chc_ctx = mem_ctx(ctx.tcx, &body, "resolve_cell");
        let owner = body
            .locals()
            .iter()
            .position(|decl| {
                matches!(decl.ty.kind(), TyKind::RigidTy(RigidTy::Adt(def, _)) if def.trimmed_name() == "PC")
            })
            .expect("the PC local");
        assert!(chc_ctx.flatten.flattened_tuple_locals.contains(&owner));
        let pc_ty = body.locals()[owner].ty;
        // `inner` itself resolves: its sort is Q's, and Q's leaves are there.
        let inner = chc_ctx.resolve_flat_struct_path(owner, &field_path(pc_ty, &[0])).unwrap();
        assert_eq!((inner.offset, inner.count), (0, 2));
        // `inner.value` is the same slots: the Cell step has no sort level.
        let value = chc_ctx.resolve_flat_struct_path(owner, &field_path(pc_ty, &[0, 0])).unwrap();
        assert_eq!((value.offset, value.count), (0, 2));
        let b = chc_ctx.resolve_flat_struct_path(owner, &field_path(pc_ty, &[0, 0, 0, 1])).unwrap();
        assert_eq!((b.offset, b.count), (1, 1), "inner.value.value.b is Q's second leaf");
        let mut downcast = field_path(pc_ty, &[1]);
        downcast[0].cons_idx = Some(0);
        assert_eq!(
            chc_ctx.resolve_flat_struct_path(owner, &downcast),
            Err("enum_downcast_in_path")
        );
        assert_eq!(chc_ctx.resolve_flat_struct_path(owner, &[]), Err("empty_path"));
    });
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "deep_probe");
        let body = instance.body().expect("body");
        let (lhs, ref_local, owner) = find_deref_field_store(&body, 1);
        let chc_ctx = mem_ctx(ctx.tcx, &body, "resolve_deep");
        assert!(chc_ctx.flatten.flattened_tuple_locals.contains(&owner));
        let path = collect_field_projections(&lhs.projection[1..], UnknownProjectionPolicy::Break);
        assert_eq!(
            chc_ctx.resolve_flat_struct_path(owner, &path),
            Err("declared_slot_not_scalar"),
            "flattening stopped at depth 4 and left L4 as one datatype slot"
        );
        assert_eq!(chc_ctx.resolve_flat_struct_path(ref_local, &path), Err("target_not_flattened"));
    });
}

/// The precise mirror writes the stored leaf into its own slot and keeps the
/// siblings at their current (input) values, with no fallback recorded.
#[test]
fn test_deref_mem_mirror_nested_field_path_is_exact() {
    with_counter_guard(|| {
        with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "nested_mirror_probe");
            let body = instance.body().expect("body");
            let (lhs, ref_local, owner) = find_deref_field_store(&body, 2);
            let fn_name = "nested_mirror_exact";
            let mut chc_ctx = mem_ctx(ctx.tcx, &body, fn_name);
            let drops_before = chc_ctx.diagnostics.place_translation_drop.get();

            let run = run_mirror(
                &mut chc_ctx,
                RefTarget::with_projections(owner, Vec::new()),
                &lhs,
                &Expr::bitvec_const(42u64, 32),
                ref_local,
                HashSet::new(),
            );
            let (constraints, keys, modified) = &run;

            assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), drops_before);
            let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
            assert!(reasons.get(fn_name).is_none(), "no fallback expected, got {reasons:?}");
            let stored = slot_constraint(&chc_ctx, constraints, keys, owner, 1);
            assert!(
                stored.contains("fld1__out") && stored.contains("#x0000002a"),
                "inner.b must be stored in fld1, got {stored}"
            );
            for slot in [0, 2] {
                let kept = slot_constraint(&chc_ctx, constraints, keys, owner, slot);
                let input = format!("_{owner}_fld{slot}");
                assert!(
                    kept.contains(&format!("{input}__out")) && kept.contains(&format!("{input})")),
                    "slot {slot} must carry its input value, got {kept}"
                );
            }
            assert!(modified.contains(&owner));
            assert_eq!(
                chc_ctx.encode.flattened_field_env.get(&(owner, 1)),
                Some(&Expr::bitvec_const(42u64, 32))
            );
        });
    });
}

/// `r.inner = q` writes both of inner's leaves from the stored value.
#[test]
fn test_deref_mem_mirror_sub_struct_store_writes_the_span() {
    with_counter_guard(|| {
        with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "nested_mirror_probe");
            let body = instance.body().expect("body");
            let (_, ref_local, owner) = find_deref_field_store(&body, 2);
            let mut chc_ctx = mem_ctx(ctx.tcx, &body, "nested_mirror_span");
            let p_ty = body.locals()[owner].ty;
            let q_ty = field_ty(p_ty, 0);
            let q_sort = ChcCtx::translate_ty(q_ty).expect("Q sort");
            let mut lhs = field_place(ref_local, p_ty, &[0]);
            lhs.projection.insert(0, ProjectionElem::Deref);
            let drops_before = chc_ctx.diagnostics.place_translation_drop.get();

            let run = run_mirror(
                &mut chc_ctx,
                RefTarget::with_projections(owner, Vec::new()),
                &lhs,
                &Expr::var("q_val", q_sort),
                ref_local,
                HashSet::new(),
            );
            let (constraints, keys, _) = &run;
            assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), drops_before);
            for slot in [0, 1] {
                let stored = slot_constraint(&chc_ctx, constraints, keys, owner, slot);
                assert!(stored.contains("q_val"), "slot {slot} must come from q, got {stored}");
            }
            let kept = slot_constraint(&chc_ctx, constraints, keys, owner, 2);
            assert!(!kept.contains("q_val"), "c must keep its value, got {kept}");
        });
    });
}

/// A path the resolver refuses fails closed. L0's flattening stopped at depth
/// 4, so even the one-level `r.z = 7` cannot be placed exactly: the old
/// raw-index write was right here only by luck.
#[test]
fn test_deref_mem_mirror_unresolved_flat_path_fails_closed() {
    with_counter_guard(|| {
        with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "deep_probe");
            let body = instance.body().expect("body");
            let (lhs, ref_local, owner) = find_deref_field_store(&body, 1);
            let fn_name = "deep_mirror_fail_closed";
            let mut chc_ctx = mem_ctx(ctx.tcx, &body, fn_name);
            // A cached pre-store value that a lost write would leave readable.
            chc_ctx.encode.flattened_field_env.insert((owner, 1), Expr::bitvec_const(0u64, 8));
            let drops_before = chc_ctx.diagnostics.place_translation_drop.get();

            let run = run_mirror(
                &mut chc_ctx,
                RefTarget::with_projections(owner, Vec::new()),
                &lhs,
                &Expr::bitvec_const(7u64, 8),
                ref_local,
                HashSet::new(),
            );
            assert_failed_closed(
                &chc_ctx,
                fn_name,
                "deref_mirror_flat_path_unresolved",
                drops_before,
                &run,
                owner,
            );
        });
    });
}

/// R4: a ref_target the Skip collector would silently shorten (a Deref), or
/// one whose place type is not the reference's pointee, is not a path into
/// the owner. Both fail closed before any arm writes.
#[test]
fn test_deref_mem_mirror_ref_target_join_mismatch_fails_closed() {
    for (case, fn_name) in [(0, "join_deref"), (1, "join_type")] {
        with_counter_guard(|| {
            with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
                let instance = find_instance_by_suffix(ctx.tcx, "nested_mirror_probe");
                let body = instance.body().expect("body");
                let (lhs, ref_local, owner) = find_deref_field_store(&body, 2);
                let mut chc_ctx = mem_ctx(ctx.tcx, &body, fn_name);
                let p_ty = body.locals()[owner].ty;
                let projections = if case == 0 {
                    vec![ProjectionElem::Deref]
                } else {
                    // Points at `o.c` (u32) while `r: &mut P`.
                    field_place(owner, p_ty, &[1]).projection
                };
                let drops_before = chc_ctx.diagnostics.place_translation_drop.get();
                let run = run_mirror(
                    &mut chc_ctx,
                    RefTarget::with_projections(owner, projections),
                    &lhs,
                    &Expr::bitvec_const(42u64, 32),
                    ref_local,
                    HashSet::new(),
                );
                assert_failed_closed(
                    &chc_ctx,
                    fn_name,
                    "deref_mirror_ref_target_join_mismatch",
                    drops_before,
                    &run,
                    owner,
                );
            });
        });
    }
}

/// R3 and R7: a stored value of another sort is never coerced into the slot,
/// and a sibling that would read back as its own `__out` variable (owner
/// already modified in the block, no cached value) is never written as
/// `out == out`. Both fail closed.
#[test]
fn test_deref_mem_mirror_inexact_values_fail_closed() {
    for (case, fn_name) in [(0, "value_sort"), (1, "value_sibling")] {
        with_counter_guard(|| {
            with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
                let instance = find_instance_by_suffix(ctx.tcx, "nested_mirror_probe");
                let body = instance.body().expect("body");
                let (lhs, ref_local, owner) = find_deref_field_store(&body, 2);
                let mut chc_ctx = mem_ctx(ctx.tcx, &body, fn_name);
                let (rhs, modified) = if case == 0 {
                    (Expr::bitvec_const(42u64, 8), HashSet::new())
                } else {
                    (Expr::bitvec_const(42u64, 32), HashSet::from([owner]))
                };
                let drops_before = chc_ctx.diagnostics.place_translation_drop.get();
                let run = run_mirror(
                    &mut chc_ctx,
                    RefTarget::with_projections(owner, Vec::new()),
                    &lhs,
                    &rhs,
                    ref_local,
                    modified,
                );
                assert_failed_closed(
                    &chc_ctx,
                    fn_name,
                    "deref_mirror_flat_value_unresolved",
                    drops_before,
                    &run,
                    owner,
                );
            });
        });
    }
}

/// R1: read case C (a nested field of a flattened local) returns the value
/// this block last wrote, as case B does, not the block's final `__out`.
#[test]
fn test_flattened_nested_read_consults_field_env() {
    with_counter_guard(|| {
        with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
            let instance = find_instance_by_suffix(ctx.tcx, "nested_mirror_probe");
            let body = instance.body().expect("body");
            let (lhs, ref_local, owner) = find_deref_field_store(&body, 2);
            let mut chc_ctx = mem_ctx(ctx.tcx, &body, "nested_read_env");
            let p_ty = body.locals()[owner].ty;
            let read = field_place(owner, p_ty, &[0, 1]);
            let modified = HashSet::from([owner]);

            let before = chc_ctx.translate_place_with_modified(&read, &modified).unwrap();
            assert!(before.to_string().contains("fld1__out"), "no write yet: the output var");

            // Mirror `r.inner.b = 42`, then read `o.inner.b` in the same block.
            let (_, _, modified) = run_mirror(
                &mut chc_ctx,
                RefTarget::with_projections(owner, Vec::new()),
                &lhs,
                &Expr::bitvec_const(42u64, 32),
                ref_local,
                HashSet::new(),
            );
            assert_eq!(
                chc_ctx.translate_place_with_modified(&read, &modified),
                Some(Expr::bitvec_const(42u64, 32)),
                "the read after the store must see the stored value"
            );
        });
    });
}

/// Follow-up (c): a single-variable target takes a field store as a whole
/// write only when the field is the whole value.
#[test]
fn test_non_flattened_field_whole_value() {
    with_test_ay_ctx_for_source(NESTED_MIRROR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "tuple_zst_probe");
        let body = instance.body().expect("body");
        let chc_ctx = mem_ctx(ctx.tcx, &body, "whole_value");
        let find = |second: &str| {
            body.locals()
                .iter()
                .position(|decl| match decl.ty.kind() {
                    TyKind::RigidTy(RigidTy::Tuple(elems)) if elems.len() == 2 => {
                        format!("{:?}", elems[1].kind()).contains(second)
                    }
                    _ => false,
                })
                .unwrap_or_else(|| panic!("a (u32, {second}) local"))
        };
        let t = find("Tuple");
        let u = find("Uint(U8)");
        let bv32 = Sort::bitvec(32);
        let rhs = Expr::bitvec_const(9u64, 32);
        let t_ty = body.locals()[t].ty;
        let u_ty = body.locals()[u].ty;
        assert!(chc_ctx.non_flattened_field_is_whole_value(
            t,
            &field_path(t_ty, &[0])[0],
            &bv32,
            &rhs
        ));
        assert!(!chc_ctx.non_flattened_field_is_whole_value(
            u,
            &field_path(u_ty, &[0])[0],
            &bv32,
            &rhs
        ));
        assert!(!chc_ctx.non_flattened_field_is_whole_value(
            t,
            &field_path(t_ty, &[1])[0],
            &bv32,
            &rhs
        ));
        assert!(!chc_ctx.non_flattened_field_is_whole_value(
            t,
            &field_path(t_ty, &[0])[0],
            &bv32,
            &Expr::bitvec_const(9u64, 8)
        ));
    });
}
