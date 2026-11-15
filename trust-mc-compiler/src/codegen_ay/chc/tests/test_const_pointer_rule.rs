// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The constant-pointer rule (`shared::const_pointer`) on the CHC lane:
//! a constant pointer is its relocation's target T plus the offset k its bytes
//! carry, its pointee is the window `T[k .. k + extent]`, and relocated bytes
//! are never data. Each test names the state main got wrong.
//!
//! Sources are the shapes of `tools/soundness-duals/const_pointer_*_dual.rs`.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::chc::decl::global_objects::object_base_for;
use crate::codegen_ay::shared::const_pointer::{self, ConstRead, TargetKey};
use rustc_public::mir::{Rvalue, StatementKind};

/// Every `(local, constant operand)` a body assigns straight from a constant.
fn const_operands(body: &rustc_public::mir::Body) -> Vec<(usize, rustc_public::mir::ConstOperand)> {
    let mut out = Vec::new();
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(place, Rvalue::Use(Operand::Constant(c), ..)) = &stmt.kind
                && place.projection.is_empty()
            {
                out.push((place.local, c.clone()));
            }
        }
    }
    out
}

/// Every `(local, constant)` a body assigns straight from a constant operand.
fn const_assigns(body: &rustc_public::mir::Body) -> Vec<(usize, rustc_public::ty::MirConst)> {
    const_operands(body).into_iter().map(|(local, c)| (local, c.const_)).collect()
}

/// The local a body assigns from its (only) pointer-typed constant.
fn const_pointer_local(body: &rustc_public::mir::Body) -> usize {
    let found: Vec<usize> = const_assigns(body)
        .into_iter()
        .filter(|(_, c)| {
            matches!(c.ty().kind(), TyKind::RigidTy(RigidTy::Ref(..) | RigidTy::RawPtr(..)))
        })
        .map(|(local, _)| local)
        .collect();
    assert_eq!(found.len(), 1, "expected one pointer constant, found locals {found:?}");
    found[0]
}

fn ctx_for<'tcx, 'body>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &'body rustc_public::mir::Body,
    name: &str,
) -> ChcCtx<'tcx, 'body> {
    let cfg = ChcConfig { track_level: crate::args::ChcTrackLevel::Ptr, ..ChcConfig::default() };
    let mut chc_ctx = ChcCtx::new(tcx, body, name.to_string(), cfg);
    chc_ctx.declare_block_relations();
    chc_ctx
}

fn bv(value: u128, width: u32) -> String {
    Expr::bitvec_const(value, width).to_string()
}

const WINDOW_SOURCE: &str = r#"
    #![allow(dead_code)]
    static PAIR: (u32, u32) = (1, 2);
    const E: &u32 = &[1u32, 2, 3][1];
    const SECOND: &u32 = &PAIR.1;
    const A3: &[u32; 3] = &[10, 20, 30];
    const E0: &u32 = &A3[0];
    const E1: &u32 = &A3[1];
    const SL: &[u32] = {
        let a: &[u32] = &[0, 1, 2, 3];
        a.split_at(1).1
    };
    const T: &str = "hello".split_at(2).1;
    const SS: &&str = &["ab", "cd"][1];
    const OE: &Option<u8> = &[None, Some(3u8)][1];
    #[derive(Clone, Copy)]
    enum Dir { A, B }
    const DR: &Dir = &[Dir::B, Dir::A][1];

    pub fn probe_e() -> u32 { *E }
    pub fn probe_second() -> u32 { *SECOND }
    pub fn probe_e0() -> u32 { *E0 }
    pub fn probe_e1() -> u32 { *E1 }
    pub fn probe_sl() -> usize { SL.len() }
    pub fn probe_t() -> usize { T.len() }
    pub fn probe_ss() -> usize { SS.len() }
    pub fn probe_oe() -> bool { OE.is_some() }
    pub fn probe_dr() -> bool { matches!(*DR, Dir::A) }
"#;

/// Unit test 1. On main `*E` decoded `[1, 2, 3]` from byte 0 and gave 1.
#[test]
fn const_ref_into_the_middle_decodes_its_window() {
    with_test_ay_ctx_for_source(WINDOW_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_e").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_e");
        let local = const_pointer_local(&body);
        let value = chc_ctx.ref_resolution.const_ref_values.get(&local).expect("E's value fact");
        assert_eq!(value.to_string(), bv(2, 32), "*E is the u32 at byte 4 of [1, 2, 3]");
    });
}

/// Unit test 2. `E` addresses byte 4 of its object; `E0` and `E1` are one
/// object (A3's) at offsets 0 and 4. On main every promoted constant got an
/// object of its own at offset 0.
#[test]
fn const_ref_into_the_middle_is_placed_at_its_offset() {
    with_test_ay_ctx_for_source(WINDOW_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_e").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_e");
        let local = const_pointer_local(&body);
        let object = *chc_ctx.ref_resolution.const_ref_objects.get(&local).expect("E's object");
        assert_eq!(object.offset, 4);
        assert_eq!(
            object.address().to_string(),
            object_base_for(object.obj_id)
                .bvadd(Expr::bitvec_const(4u128, crate::codegen_ay::types::POINTER_WIDTH))
                .to_string()
        );

        let objects: Vec<(u32, u64)> = ["probe_e0", "probe_e1"]
            .into_iter()
            .map(|name| {
                let body = find_instance_by_suffix(ctx.tcx, name).body().unwrap();
                let chc_ctx = ctx_for(ctx.tcx, &body, name);
                let local = const_pointer_local(&body);
                let object = chc_ctx.ref_resolution.const_ref_objects[&local];
                let bytes = const_pointer::const_bytes(
                    &const_assigns(&body).into_iter().find(|(l, _)| *l == local).unwrap().1,
                )
                .unwrap()
                .stored_pointer(0)
                .unwrap();
                // The object is the one the table keys by the target.
                assert_eq!(
                    chc_ctx.global_object(&bytes.key().unwrap()).map(|o| o.obj_id),
                    Some(object.obj_id)
                );
                (object.obj_id, object.offset)
            })
            .collect();
        assert_eq!(objects[0].1, 0);
        assert_eq!(objects[1].1, 4);
    });
}

/// Unit test 3. On main the length was the target's size / 4 (4), not the
/// fat pointer's metadata word (3).
#[test]
fn const_subslice_length_is_the_metadata_word() {
    with_test_ay_ctx_for_source(WINDOW_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_sl").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_sl");
        let local = const_pointer_local(&body);
        let len = chc_ctx.ref_resolution.subslice_len.get(&local).expect("SL's length");
        assert_eq!(len.to_string(), bv(3, crate::codegen_ay::types::POINTER_WIDTH));
    });
}

/// Unit tests 4 and 11 (call-model shapes): `T` is "llo" and `SS` is "cd",
/// the windows at the pointers' offsets. On main both read their target from
/// byte 0 ("hel", "ab").
#[test]
fn nested_const_ref_follows_the_relocation_at_the_read_offset() {
    with_test_ay_ctx_for_source(WINDOW_SOURCE, |ctx| {
        for (probe, want, not_want, len) in
            [("probe_t", b"lo".as_slice(), b"he".as_slice(), 3u128), ("probe_ss", b"cd", b"ab", 2)]
        {
            let body = find_instance_by_suffix(ctx.tcx, probe).body().unwrap();
            let chc_ctx = ctx_for(ctx.tcx, &body, probe);
            let local = const_pointer_local(&body);
            let value = chc_ctx
                .ref_resolution
                .const_ref_values
                .get(&local)
                .expect("a window value")
                .to_string();
            for byte in want {
                assert!(
                    value.contains(&bv(u128::from(*byte), 8)),
                    "{probe}: {value} lacks {byte:#x}"
                );
            }
            for byte in not_want {
                assert!(
                    !value.contains(&bv(u128::from(*byte), 8)),
                    "{probe}: {value} holds {byte:#x}, a byte outside the window"
                );
            }
            let got_len = chc_ctx.ref_resolution.subslice_len.get(&local).expect("a length");
            assert_eq!(got_len.to_string(), bv(len, crate::codegen_ay::types::POINTER_WIDTH));
        }
    });
}

/// Unit test 5. `SECOND = &PAIR.1` into a FIXED static folds its window (2),
/// and is not the static's whole-state reference (it names byte 4).
#[test]
fn const_ref_into_fixed_static_folds_the_window() {
    with_test_ay_ctx_for_source(WINDOW_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_second").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_second");
        let local = const_pointer_local(&body);
        let value = chc_ctx.ref_resolution.const_ref_values.get(&local).expect("SECOND's value");
        assert_eq!(value.to_string(), bv(2, 32));
        assert!(
            !chc_ctx.ref_resolution.static_ref_to_state_idx.contains_key(&local),
            "a pointer to byte 4 of PAIR is not a reference to PAIR's whole state"
        );
    });
}

/// Unit test 10. The discriminant is the WINDOW's tag: `OE` is Some (1) and
/// `DR` is `Dir::A` (0). On main they were read at the target's byte 0:
/// None (0) and `Dir::B` (1).
#[test]
fn const_ref_discriminant_reads_the_window() {
    with_test_ay_ctx_for_source(WINDOW_SOURCE, |ctx| {
        for (probe, want) in [("probe_oe", 1u64), ("probe_dr", 0)] {
            let body = find_instance_by_suffix(ctx.tcx, probe).body().unwrap();
            let chc_ctx = ctx_for(ctx.tcx, &body, probe);
            let local = const_pointer_local(&body);
            assert_eq!(
                chc_ctx.ref_resolution.const_ref_discriminants.get(&local).copied(),
                Some(want),
                "{probe}"
            );
        }
    });
}

/// Unit test 14 (D2). A fixed object is seeded WHOLE at every offset the
/// harness reads it at: `E`'s object `[1, 2, 3]` has u32 seeds at 0, 4 and
/// 8, not only at the window's 4.
#[test]
fn fixed_object_is_seeded_whole() {
    with_test_ay_ctx_for_source(WINDOW_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_e").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_e");
        let local = const_pointer_local(&body);
        let obj_id = chc_ctx.ref_resolution.const_ref_objects[&local].obj_id;
        let mut seeds: Vec<(u64, String)> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .filter(|(_, sort, _, id, _)| *id == obj_id && sort.bitvec_width() == Some(32))
            .map(|(_, _, value, _, offset)| (*offset, value.to_string()))
            .collect();
        seeds.sort();
        seeds.dedup();
        assert_eq!(seeds, vec![(0, bv(1, 32)), (4, bv(2, 32)), (8, bv(3, 32))]);
    });
}

const VALUE_SLOTS_SOURCE: &str = r#"
    #![allow(dead_code)]
    static PAIR: (u32, u32) = (1, 2);
    const PTRS: [*const u32; 2] = [&raw const PAIR.0, &raw const PAIR.1];

    pub fn probe_ptrs() -> bool {
        let p = PTRS;
        p[0].is_null()
    }
"#;

/// Unit tests 12 and 16 (D8). A pointer INSIDE a constant value is its
/// relocation's address: `PTRS` is `[base(PAIR), base(PAIR) + 4]`. On main
/// the elements were the offsets their bytes carry (0 and 4), so
/// `PTRS[0].is_null()` PROVED. And the aggregate constant is not a static
/// reference: its local names no static's state.
#[test]
fn pointer_slot_in_const_value_resolves_its_target() {
    with_test_ay_ctx_for_source(VALUE_SLOTS_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_ptrs").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_ptrs");
        let (local, op) = const_operands(&body)
            .into_iter()
            .find(|(_, c)| matches!(c.const_.ty().kind(), TyKind::RigidTy(RigidTy::Array(..))))
            .expect("the PTRS constant");
        let pair = const_pointer::const_bytes(&op.const_)
            .unwrap()
            .stored_pointer(0)
            .unwrap()
            .key()
            .unwrap();
        let obj_id = chc_ctx.global_object(&pair).expect("PAIR's object").obj_id;
        let value = chc_ctx.translate_constant(&op).expect("PTRS decodes").to_string();
        let base = object_base_for(obj_id);
        let second =
            base.clone().bvadd(Expr::bitvec_const(4u128, crate::codegen_ay::types::POINTER_WIDTH));
        assert!(value.contains(&base.to_string()), "{value} lacks base(PAIR)");
        assert!(value.contains(&second.to_string()), "{value} lacks base(PAIR) + 4");
        assert!(
            !chc_ctx.ref_resolution.static_ref_to_state_idx.contains_key(&local),
            "an aggregate constant holding pointers is not a static reference"
        );
    });
}

const POINTER_STATIC_SOURCE: &str = r#"
    #![allow(dead_code)]
    static SS2: &str = "hello".split_at(2).1;
    pub fn probe_ss2() -> usize { SS2.len() }
"#;

/// Unit test 15 (D9). A pointer static's seed length is ITS OWN metadata
/// word (3, for "llo"), not the target's size (5).
#[test]
fn pointer_static_slice_len_is_the_metadata_word() {
    with_test_ay_ctx_for_source(POINTER_STATIC_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_ss2").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_ss2");
        let local = const_pointer_local(&body);
        let idx = *chc_ctx
            .ref_resolution
            .static_ref_to_state_idx
            .get(&local)
            .expect("SS2's reference maps to its state");
        let len = chc_ctx.ref_resolution.static_ref_len_seeds.get(&idx).expect("SS2's length seed");
        assert_eq!(len.to_string(), bv(3, crate::codegen_ay::types::POINTER_WIDTH));
    });
}

const TRANSITIVE_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::UnsafeCell;
    struct Racy(UnsafeCell<[u32; 2]>);
    unsafe impl Sync for Racy {}
    struct SyncPtr(*mut u32);
    unsafe impl Sync for SyncPtr {}
    static RC: Racy = Racy(UnsafeCell::new([1, 2]));
    static RP: SyncPtr = SyncPtr(unsafe { (RC.0.get() as *mut u32).add(1) });

    pub fn probe_rp() -> u32 { unsafe { *RP.0 } }
"#;

/// Unit test 17 (D1, N6), CHC half. `RC` is reached only through `RP`'s
/// initializer, and still gets its one object. On main it had none.
#[test]
fn reachable_targets_is_transitive_through_initializers() {
    with_test_ay_ctx_for_source(TRANSITIVE_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_rp").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_rp");
        let rp = const_assigns(&body)
            .into_iter()
            .find_map(|(_, c)| {
                let key = const_pointer::const_bytes(&c)?.stored_pointer(0)?.key()?;
                key.static_def().map(|_| key)
            })
            .expect("a reference to RP");
        let (rp_bytes, _) = const_pointer::target_bytes(ctx.tcx, &rp).expect("RP's initializer");
        let rc = rp_bytes.stored_pointer(0).expect("RP holds a pointer").key().expect("into RC");
        assert!(matches!(rc, TargetKey::Static(_)));
        assert!(chc_ctx.global_object(&rp).is_some(), "RP has its object");
        assert!(chc_ctx.global_object(&rc).is_some(), "RC, reached through RP, has its object");
        let walk = const_pointer::reachable_targets(ctx.tcx, &body, |_| true);
        assert!(walk.targets.iter().any(|reached| reached.key == rc));
    });
}

const STATIC_PATH_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub struct S3 { a: u8, b: u32, c: u16 }
    pub enum En { X(u32), Y(u16) }
    pub fn probe_types(a: [u32; 2], b: (u8, (u16, u32)), c: S3, e: En, x: u32, y: u16) {}
"#;

/// Unit test 7 (D6). The static place path is the layout's: a pointer at
/// byte k of a static, read at type P, is the field/element path whose offset
/// is k and whose type is P; an enum has no path (its payload moves with the
/// variant).
#[test]
fn static_path_from_offset() {
    use crate::codegen_ay::chc::decl::static_path::{StaticPathElem, static_path};
    use crate::kani_middle::abi::LayoutOf;
    with_test_ay_ctx_for_source(STATIC_PATH_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_types").body().unwrap();
        let ty = |local: usize| body.locals()[local].ty;
        let (arr, tup, s3, en, u32_ty, u16_ty) = (ty(1), ty(2), ty(3), ty(4), ty(5), ty(6));

        assert_eq!(static_path(arr, 4, u32_ty), Some(vec![StaticPathElem::Index(1)]));

        let TyKind::RigidTy(RigidTy::Tuple(elems)) = tup.kind() else { panic!("tuple") };
        let k = LayoutOf::new(tup).field_offset(1).unwrap()
            + LayoutOf::new(elems[1]).field_offset(1).unwrap();
        assert_eq!(
            static_path(tup, k as u64, u32_ty),
            Some(vec![StaticPathElem::Field(1), StaticPathElem::Field(1)])
        );

        // `repr(Rust)` reorders: the path names `c` by its LAYOUT offset.
        let c_off = LayoutOf::new(s3).field_offset(2).unwrap();
        assert_eq!(static_path(s3, c_off as u64, u16_ty), Some(vec![StaticPathElem::Field(2)]));

        assert_eq!(static_path(en, 4, u32_ty), None);
        // The whole static at offset 0, at its own type, is the empty path.
        assert_eq!(static_path(arr, 0, arr), Some(vec![]));
    });
}

const STATIC_PATH_COLLAPSED_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::UnsafeCell;
    use std::sync::atomic::AtomicU32;
    pub struct Counters { a: AtomicU32, b: AtomicU32 }
    pub fn probe_collapsed(a: AtomicU32, c: Counters, x: u32, cell: UnsafeCell<u32>) {}
    pub struct DirectStorageAtomic { v: UnsafeCell<u32> }
    pub fn probe_direct_storage(a: DirectStorageAtomic) {}

    mod user {
        pub struct UnsafeCell<T>(pub T, pub u8);
        pub fn probe_named_cell(cell: UnsafeCell<u32>) {}
    }
"#;

/// The static place path skips a layer the CHC encoding collapses into its
/// field: an atomic-shaped `{ v: UnsafeCell<u32> }` has ONE selection, with
/// no `UnsafeCell` level. The pinned compiler's generic Atomic may additionally
/// contain its real aligned storage struct, whose selection must remain. It was
/// `[Field(0), Field(0)]`; the second step failed on the bitvector, every store
/// through `AtomicU32::as_ptr` into a static havocked the static, and a store
/// made by `AtomicU32::store` could not be routed into it
/// (const_pointer_live_raw_read_dual.rs, `bug_atomic_as_ptr_after_store`
/// PROVED on main ed592ea3d).
#[test]
fn static_path_skips_a_layer_the_encoding_collapses() {
    use crate::codegen_ay::chc::decl::static_path::{StaticPathElem, static_path};
    use crate::codegen_ay::shared::mono_ty;
    use crate::kani_middle::abi::LayoutOf;
    with_test_ay_ctx_for_source(STATIC_PATH_COLLAPSED_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_collapsed").body().unwrap();
        let ty = |local: usize| body.locals()[local].ty;
        let (atomic, counters, u32_ty, cell) = (ty(1), ty(2), ty(3), ty(4));

        let direct_body = find_instance_by_suffix(ctx.tcx, "probe_direct_storage").body().unwrap();
        let direct_atomic = direct_body.locals()[1].ty;
        assert_eq!(static_path(direct_atomic, 0, u32_ty), Some(vec![StaticPathElem::Field(0)]));

        // Preserve the actual standard-library storage path rather than
        // flattening its private alignment wrapper to fit a historical count.
        let TyKind::RigidTy(RigidTy::Adt(atomic_def, atomic_args)) = atomic.kind() else {
            panic!("AtomicU32 is an ADT")
        };
        let atomic_cell = mono_ty::single_field_storage_ty(atomic_def, &atomic_args)
            .expect("Atomic has exactly one normalized field");
        let TyKind::RigidTy(RigidTy::Adt(cell_def, cell_args)) = atomic_cell.kind() else {
            panic!("Atomic's field is UnsafeCell")
        };
        assert!(rustc_internal::internal(ctx.tcx, cell_def).is_unsafe_cell());
        let storage = mono_ty::single_field_storage_ty(cell_def, &cell_args)
            .expect("UnsafeCell's real normalized storage");
        let mut expected_path = vec![StaticPathElem::Field(0)];
        if storage != u32_ty {
            let TyKind::RigidTy(RigidTy::Adt(storage_def, storage_args)) = storage.kind() else {
                panic!("the extra storage is a real single-field struct")
            };
            assert_eq!(storage_def.kind(), rustc_public::ty::AdtKind::Struct);
            assert_eq!(mono_ty::single_field_storage_ty(storage_def, &storage_args), Some(u32_ty));
            assert_eq!(LayoutOf::new(storage).field_offset(0), Some(0));
            let scalar_size = LayoutOf::new(u32_ty).size_of().expect("u32 has a concrete size");
            assert_eq!(LayoutOf::new(storage).size_of(), Some(scalar_size));
            assert_ne!(ChcCtx::translate_ty(storage), ChcCtx::translate_ty(u32_ty));
            expected_path.push(StaticPathElem::Field(0));
        }
        let path = static_path(atomic, 0, u32_ty).expect("the u32 inside an AtomicU32");
        assert_eq!(
            path,
            expected_path,
            "AtomicU32={atomic:?}, UnsafeCell={cell:?}, scalar={u32_ty:?}; sorts={:?}/{:?}/{:?}",
            ChcCtx::translate_ty(atomic),
            ChcCtx::translate_ty(cell),
            ChcCtx::translate_ty(u32_ty)
        );
        assert_eq!(static_path(cell, 0, u32_ty), Some(vec![]));
        assert_eq!(ChcCtx::translate_ty(cell), ChcCtx::translate_ty(u32_ty));
        let b_off = LayoutOf::new(counters).field_offset(1).unwrap();
        let mut counter_path = vec![StaticPathElem::Field(1)];
        counter_path.extend_from_slice(&path);
        assert_eq!(static_path(counters, b_off as u64, u32_ty), Some(counter_path));

        // The path applies to the CHC value: a store of the u32 updates the
        // atomic, and a read of it selects the bitvector.
        let sort = ChcCtx::translate_ty(atomic).expect("AtomicU32 has a sort");
        assert!(sort.is_datatype(), "AtomicU32 is a datatype: {sort:?}");
        let root = Expr::var("probe_atomic", sort.clone());
        let seven = Expr::bitvec_const(7i128, 32);
        let updated = ChcCtx::update_static_path(&root, &path, seven.clone())
            .expect("the u32 inside the atomic is updatable");
        assert_eq!(updated.sort(), &sort);
        let read = ChcCtx::select_static_path(root.clone(), &path).expect("selectable");
        assert_eq!(read.sort(), seven.sort());
        // A call model stores the atomic's SCALAR at the atomic's own type
        // (`AtomicU32::store(7)`): the update writes the innermost field.
        let whole = static_path(atomic, 0, atomic).expect("the whole atomic");
        assert!(whole.is_empty());
        assert!(ChcCtx::update_static_path(&root, &whole, seven.clone()).is_none());
        let scalar = ChcCtx::update_static_path_scalar(&root, &whole, seven)
            .expect("the scalar of a single-field chain");
        assert_eq!(scalar.sort(), &sort);

        // A same-named user ADT retains every real field; the spelling must
        // not collapse it to its first generic argument.
        let user_body = find_instance_by_suffix(ctx.tcx, "probe_named_cell").body().unwrap();
        let named_cell = user_body.locals()[1].ty;
        let named_sort = ChcCtx::translate_ty(named_cell).expect("user UnsafeCell has a sort");
        let named_dt = named_sort.datatype_sort().expect("user UnsafeCell stays a datatype");
        assert_eq!(named_dt.constructors.len(), 1);
        assert_eq!(named_dt.constructors[0].fields.len(), 2);
        assert_ne!(Some(named_sort), ChcCtx::translate_ty(u32_ty));
    });
}

/// A collapsed owner retains its whole value under the content's canonical
/// memory key, while field views select the content's actual constructor.
/// Check the registered values as well as the shared field decomposition.
#[test]
fn static_image_collapsed_struct_view_preserves_the_content_value() {
    use crate::codegen_ay::provenance::{Loc, Val};
    use crate::codegen_ay::shared::mono_ty;
    with_test_ay_ctx_for_source(STATIC_PATH_COLLAPSED_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_collapsed").body().unwrap();
        let atomic = body.locals()[1].ty;
        let scalar = body.locals()[3].ty;
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = atomic.kind() else { panic!("Atomic") };
        let cell = mono_ty::single_field_storage_ty(def, &args).expect("Atomic.v");
        let TyKind::RigidTy(RigidTy::Adt(def, args)) = cell.kind() else { panic!("UnsafeCell") };
        assert!(rustc_internal::internal(ctx.tcx, def).is_unsafe_cell());
        let storage = mono_ty::single_field_storage_ty(def, &args).expect("cell.value");
        let sort = ChcCtx::translate_ty(cell).expect("the canonical cell encoding");
        assert_eq!(ChcCtx::translate_ty(storage), Some(sort.clone()));
        let value = Expr::var("content_value", sort.clone());
        let mut chc = ChcCtx::new(ctx.tcx, &body, "probe_collapsed", ChcConfig::default());
        assert_eq!(chc.type_key_for_body_ty(cell), chc.type_key_for_body_ty(storage));
        assert_eq!(
            chc.static_image_field_views(cell, &sort),
            chc.static_image_field_views(storage, &sort)
        );
        let fields = chc.static_image_fields(storage, &value);
        assert_eq!(chc.static_image_fields(cell, &value), fields);
        assert!(chc.static_image_fields(cell, &Expr::bitvec_const(7u16, 16)).is_none());

        let scalar_value = if storage != scalar {
            let fields = fields.expect("real storage fields");
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, scalar);
            assert_eq!(fields[0].2, 0);
            assert_eq!(Some(fields[0].1.sort().clone()), ChcCtx::translate_ty(scalar));
            assert_ne!(fields[0].1, value, "a real storage constructor is selected, not erased");
            let datatype = sort.datatype_sort().expect("the storage's real constructor");
            let [constructor] = datatype.constructors.as_slice() else { panic!("one constructor") };
            let [field] = constructor.fields.as_slice() else { panic!("one scalar field") };
            let expected =
                value.clone().field_select(&datatype.name, &field.name, field.sort.clone());
            assert_eq!(fields[0].1, expected, "the value comes from the actual storage field");
            expected
        } else {
            value.clone()
        };
        let address = object_base_for(42);
        chc.register_static_memory_init_entries(
            cell,
            Val::of_value(value),
            Loc::of_address(address.clone()),
            false,
        );
        for ty in [cell, storage, scalar] {
            let key = chc.type_key_for_body_ty(ty);
            let entries: Vec<_> = chc
                .ref_resolution
                .static_memory_inits
                .iter()
                .filter(|(entry_key, ..)| entry_key.as_ref() == key.as_ref())
                .collect();
            assert!(!entries.is_empty(), "the image must seed {key}");
            for (_, entry_sort, entry_value, entry_address) in entries {
                assert_eq!(entry_sort, scalar_value.sort(), "{key}");
                assert_eq!(entry_value, &scalar_value, "{key}: the whole content is preserved");
                assert_eq!(entry_address, &address, "{key}: the alias keeps the same address");
            }
        }
    });
}

const COLLAPSED_LAYOUT_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::UnsafeCell;
    #[derive(Clone, Copy)]
    pub struct Pt { x: u16, y: u32 }
    #[repr(C)]
    pub struct CPt { x: u16, y: u32 }
    #[repr(C)]
    pub struct Image {
        prefix: u64,
        point: UnsafeCell<Pt>,
        cpoint: UnsafeCell<CPt>,
        array: UnsafeCell<[Pt; 2]>,
    }
    struct SyncImage(Image);
    unsafe impl Sync for SyncImage {}
    static IMAGE: SyncImage = SyncImage(Image {
        prefix: 0x1122_3344_5566_7788,
        point: UnsafeCell::new(Pt { x: 1, y: 0x0102_0304 }),
        cpoint: UnsafeCell::new(CPt { x: 5, y: 0x0506_0708 }),
        array: UnsafeCell::new([
            Pt { x: 9, y: 0x090a_0b0c },
            Pt { x: 13, y: 0x0d0e_0f10 },
        ]),
    });
    pub fn probe_layout_types(
        point: Pt, cpoint: CPt, point_cell: UnsafeCell<Pt>,
        cpoint_cell: UnsafeCell<CPt>, array_cell: UnsafeCell<[Pt; 2]>, image: Image,
    ) {}
    pub fn probe_layout_image() -> *const SyncImage { &IMAGE }
"#;

/// The collapsed value still comes from the content's actual ABI layout,
/// at the caller's original window. In particular Pt.y precedes Pt.x, while
/// repr(C) retains declaration order and an array uses Pt's padded stride.
#[test]
fn collapsed_static_content_decodes_reordered_fields_at_its_original_offset() {
    use crate::kani_middle::abi::LayoutOf;
    with_test_ay_ctx_for_source(COLLAPSED_LAYOUT_SOURCE, |ctx| {
        let types = find_instance_by_suffix(ctx.tcx, "probe_layout_types").body().unwrap();
        let ty = |local: usize| types.locals()[local].ty;
        let (point, cpoint, point_cell, cpoint_cell, array_cell, image) =
            (ty(1), ty(2), ty(3), ty(4), ty(5), ty(6));
        assert_eq!(LayoutOf::new(point).field_offset(1), Some(0), "real reordered Pt.y");
        assert_eq!(LayoutOf::new(point).field_offset(0), Some(4), "real reordered Pt.x");
        assert_eq!(LayoutOf::new(cpoint).field_offset(0), Some(0));
        assert_eq!(LayoutOf::new(cpoint).field_offset(1), Some(4));

        let body = find_instance_by_suffix(ctx.tcx, "probe_layout_image").body().unwrap();
        let local = const_pointer_local(&body);
        let constant = const_assigns(&body).into_iter().find(|(l, _)| *l == local).unwrap().1;
        let key = const_pointer::const_bytes(&constant)
            .unwrap()
            .stored_pointer(0)
            .unwrap()
            .key()
            .unwrap();
        let (bytes, _) = const_pointer::target_bytes(ctx.tcx, &key).expect("real IMAGE allocation");
        let mut chc = ChcCtx::new(ctx.tcx, &body, "probe_layout_image", ChcConfig::default());
        let value = |sort: &Sort, x: u128, y: u128| {
            let dt = sort.datatype_sort().expect("point datatype");
            let [ctor] = dt.constructors.as_slice() else { panic!("one point constructor") };
            assert_eq!(ctor.fields.len(), 2);
            assert_eq!(ctor.fields[0].sort, Sort::bitvec(16));
            assert_eq!(ctor.fields[1].sort, Sort::bitvec(32));
            Expr::datatype_constructor(
                &*dt.name,
                &*ctor.name,
                vec![Expr::bitvec_const(x, 16), Expr::bitvec_const(y, 32)],
                sort.clone(),
            )
        };
        for (index, cell, x, y) in
            [(1, point_cell, 1, 0x0102_0304), (2, cpoint_cell, 5, 0x0506_0708)]
        {
            let offset = LayoutOf::new(image).field_offset(index).expect("real field offset");
            assert_ne!(offset, 0, "prefix makes the retained window observable");
            let sort = ChcCtx::translate_ty(cell).expect("collapsed content sort");
            let decoded = chc.read_static_value_by_layout(&bytes, offset, cell, &sort, 0);
            assert_eq!(decoded, Some(value(&sort, x, y)));
        }

        let offset = LayoutOf::new(image).field_offset(3).expect("array field offset");
        let sort = ChcCtx::translate_ty(array_cell).expect("collapsed array sort");
        let arr = sort.array_sort().expect("real content array");
        let width = arr.element_sort.bitvec_width().expect("flattened Pt");
        let point_sort = ChcCtx::translate_ty(point).unwrap();
        let flatten = |x, y| {
            crate::codegen_ay::types::flatten_datatype_to_bitvec(&value(&point_sort, x, y), width)
                .expect("canonical point flattening")
        };
        let idx_width = arr.index_sort.bitvec_width().unwrap();
        let expected = Expr::const_array(arr.index_sort.clone(), Expr::bitvec_const(0u128, width))
            .store(Expr::bitvec_const(0u128, idx_width), flatten(9, 0x090a_0b0c))
            .store(Expr::bitvec_const(1u128, idx_width), flatten(13, 0x0d0e_0f10));
        assert_eq!(
            chc.read_static_value_by_layout(&bytes, offset, array_cell, &sort, 0),
            Some(expected),
        );
    });
}

const POINTER_STATIC_IDENTITY_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(static_mut_refs)]
    static mut X: u32 = 1;
    static mut PX: *mut u32 = unsafe { &raw mut X };
    static mut X2: u32 = 1;
    static mut PX2: *mut u32 = unsafe { &raw mut X2 };
    pub fn probe_px() -> u32 { unsafe { *PX = 7; X } }
    pub fn probe_px2() -> u32 { unsafe { *PX2 = 7; X2 } }
"#;

/// Unit test 6a (D1, R10a). One static, one object: the object `PX`'s
/// initializer points at is the object whose state variable is `X`'s. On main
/// `X` was minted twice (once by the pointer-static resolver, again by the
/// static collector), so `*PX = 7` wrote an object `X`'s state never read and
/// `X == 1` PROVED.
#[test]
fn pointer_static_mints_its_target_once() {
    with_test_ay_ctx_for_source(POINTER_STATIC_IDENTITY_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_px").body().unwrap();
        let mut chc_ctx = ctx_for(ctx.tcx, &body, "probe_px");
        let locals = referenced_static_locals(&body);
        let px_key = TargetKey::Static(
            const_assigns(&body)
                .into_iter()
                .find(|(local, _)| Some(local) == locals.get("PX"))
                .and_then(|(_, c)| const_pointer::const_bytes(&c)?.stored_pointer(0)?.key())
                .and_then(|key| key.static_def())
                .expect("a reference to PX"),
        );
        let (px_bytes, _) = const_pointer::target_bytes(ctx.tcx, &px_key).expect("PX's bytes");
        let x_key = px_bytes.stored_pointer(0).expect("PX holds &raw mut X").key().expect("X");
        let x_obj = chc_ctx.global_object(&x_key).expect("X's object").obj_id;
        let x_idx = locals
            .get("X")
            .and_then(|local| chc_ctx.ref_resolution.static_ref_to_state_idx.get(local))
            .copied()
            .expect("X's state variable");
        assert_eq!(
            chc_ctx.ref_resolution.static_state_idx_by_obj.get(&x_obj).copied(),
            Some(x_idx),
            "the object PX points at is the object of X's state variable"
        );
        assert_eq!(
            chc_ctx
                .ref_resolution
                .static_state_idx_by_obj
                .values()
                .filter(|&&i| i == x_idx)
                .count(),
            1,
            "X has exactly one object"
        );
        // THE mint is idempotent per key: a second call (the static
        // collector, a callee's walk) names the same object, never a new one
        // that would leave the first one's seeds and stores dangling.
        assert_eq!(chc_ctx.mint_object(x_key), Some(x_obj), "minting X again names X's object");
    });
}

/// Unit test 6b (D7(c)). A `static mut` pointer static may be repointed
/// before it is loaded, so the lane records neither its initializer's
/// pointee address nor that pointee's value for it. On main `PX2 = &raw mut
/// Y2; *PX2 = 7; Y2 == 2` PROVED on the initializer's pointee.
#[test]
fn mutable_pointer_static_load_names_no_pointee() {
    with_test_ay_ctx_for_source(POINTER_STATIC_IDENTITY_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_px2").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_px2");
        let locals = referenced_static_locals(&body);
        let idx = locals
            .get("PX2")
            .and_then(|local| chc_ctx.ref_resolution.static_ref_to_state_idx.get(local))
            .copied()
            .expect("PX2's state variable");
        assert!(!chc_ctx.ref_resolution.static_pointee_addrs.contains_key(&idx));
        assert!(!chc_ctx.ref_resolution.static_pointee_init_values.contains_key(&idx));
    });
}

const CALL_MODEL_SOURCE: &str = r#"
    #![allow(dead_code)]
    const BS: &[u8] = b"hello".split_at(2).1;
    const T: &str = "hello".split_at(2).1;
    const SS: &&str = &["ab", "cd"][1];
    pub fn probe_bs() -> usize { BS.len() }
    pub fn probe_t() -> usize { T.len() }
    pub fn probe_ss() -> usize { SS.len() }
"#;

/// Unit test 11 (R8, shared). The reader every call model now takes its
/// constant through: `BS` is `b"llo"` with length 3, `T` is `"llo"`, and the
/// `SS` hop reads the relocation AT its window (`"cd"`), not the allocation's
/// first one (`"ab"`). On main the string models decoded the target from
/// byte 0 (`"hello"`, length 5).
#[test]
fn fixed_pointee_on_call_model_shapes() {
    with_test_ay_ctx_for_source(CALL_MODEL_SOURCE, |ctx| {
        let pointer_const = |probe: &str| {
            let body = find_instance_by_suffix(ctx.tcx, probe).body().unwrap();
            let local = const_pointer_local(&body);
            const_assigns(&body).into_iter().find(|(l, _)| *l == local).unwrap().1
        };
        let pointee = |c: &rustc_public::ty::MirConst| match c.ty().kind() {
            TyKind::RigidTy(RigidTy::Ref(_, p, _)) => p,
            other => panic!("not a reference: {other:?}"),
        };
        for (probe, want) in [("probe_bs", &b"llo"[..]), ("probe_t", &b"llo"[..])] {
            let c = pointer_const(probe);
            let bytes = const_pointer::const_bytes(&c).unwrap();
            let (r, window) = const_pointer::fixed_pointee(ctx.tcx, &bytes, 0, pointee(&c))
                .expect("a fixed window");
            assert_eq!(r.metadata, Some(3), "{probe}: the length is the fat pointer's word");
            assert_eq!(window.read_data_bytes(0, window.len()).as_deref(), Some(want), "{probe}");
        }
        let c = pointer_const("probe_ss");
        let bytes = const_pointer::const_bytes(&c).unwrap();
        let (_, outer) =
            const_pointer::fixed_pointee(ctx.tcx, &bytes, 0, pointee(&c)).expect("SS's window");
        let str_ty = match pointee(&c).kind() {
            TyKind::RigidTy(RigidTy::Ref(_, p, _)) => p,
            other => panic!("SS points at a &str, got {other:?}"),
        };
        let (_, cd) = const_pointer::fixed_pointee(ctx.tcx, &outer, 0, str_ty).expect("the hop");
        assert_eq!(cd.read_data_bytes(0, cd.len()).as_deref(), Some(&b"cd"[..]));
    });
}

const READ_SET_SOURCE: &str = r#"
    #![allow(dead_code)]
    const E: &u32 = &[1u32, 2, 3][1];
    pub fn probe_bytes() -> u8 {
        let p = E as *const u32 as *const u8;
        unsafe { *p.add(1) }
    }
    pub fn probe_message(x: u32) {
        assert!(x != 7, "a message the model never reads, long enough to notice");
    }
    pub fn probe_message_local(x: u32) -> u32 {
        if x == 7 {
            let msg: &str = "a message a local holds on a failing path only";
            panic!("{}", msg);
        }
        x
    }
    pub fn probe_long_message_local(x: u32) -> u32 {
        if x == 7 {
            let msg: &str = "a long diagnostic message kept only on the failing branch with more than sixty four bytes";
            panic!("{}", msg);
        }
        x
    }
    pub fn probe_long_string_live(index: usize) -> u8 {
        let msg: &str = "a long diagnostic message kept only on the failing branch with more than sixty four bytes";
        msg.as_bytes()[index]
    }
    pub fn probe_forever(n: u32) {
        let mut s = 0u32;
        loop {
            s = s.wrapping_add(*E);
            if s == n {
                continue;
            }
        }
    }
"#;

/// The `(offset, value)` seeds of `obj_id` whose cell is `width` bits.
fn seeds_of(chc_ctx: &ChcCtx<'_, '_>, obj_id: u32, width: u32) -> Vec<(u64, String)> {
    let mut seeds: Vec<(u64, String)> = chc_ctx
        .ref_resolution
        .const_ref_memory_inits
        .iter()
        .filter(|(_, sort, _, id, _)| *id == obj_id && sort.bitvec_width() == Some(width))
        .map(|(_, _, value, _, offset)| (*offset, value.to_string()))
        .collect();
    seeds.sort();
    seeds.dedup();
    seeds
}

/// D2, "at every type the harness reads through a pointer into the object".
/// `E as *const u32 as *const u8` reads `E`'s object at `u8`, a type no
/// constant names: the object is seeded byte by byte too. Before, only its
/// u32 cells were, and `*p.add(1) == 0` FAILED certified Genuine on a free
/// byte (a false certificate, on main as well).
#[test]
fn fixed_object_is_seeded_at_every_deref_type() {
    with_test_ay_ctx_for_source(READ_SET_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_bytes").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_bytes");
        let local = const_pointer_local(&body);
        let obj_id = chc_ctx.ref_resolution.const_ref_objects[&local].obj_id;
        let bytes: Vec<(u64, String)> = [1u128, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]
            .into_iter()
            .enumerate()
            .map(|(at, b)| (at as u64, bv(b, 8)))
            .collect();
        assert_eq!(seeds_of(&chc_ctx, obj_id, 8), bytes);
        assert_eq!(seeds_of(&chc_ctx, obj_id, 32).len(), 3, "and its u32 cells");
    });
}

/// D2's read set leaves out a constant nothing dereferences: the message of
/// an `assert!` is used only on its panic path, so its object gets its one
/// address but no seeds. Seeding every such message cost: an 89-byte loop
/// contract message became 89 entry-rule seeds and bb0 stores, and pushed
/// `lc_dual_guard_entry`'s loop-skipped harness off its straight-line proof.
#[test]
fn panic_path_message_is_minted_but_not_seeded() {
    with_test_ay_ctx_for_source(READ_SET_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_message").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_message");
        let walk = const_pointer::reachable_targets(ctx.tcx, &body, |_| true);
        let messages: Vec<u32> = walk
            .targets
            .iter()
            .filter(|reached| {
                reached.bytes.as_ref().is_some_and(|(bytes, _)| {
                    bytes
                        .read_data_bytes(0, bytes.len())
                        .is_some_and(|b| b.starts_with(b"a message the model never reads"))
                })
            })
            .map(|reached| chc_ctx.global_object(&reached.key).expect("minted").obj_id)
            .collect();
        assert_eq!(messages.len(), 1, "the message's one object");
        assert!(
            chc_ctx.ref_resolution.const_ref_memory_inits.iter().all(|init| init.3 != messages[0]),
            "a panic-path message is not seeded"
        );
    });
}

/// The panic-only test is "cannot reach a `Return` AND cannot reach a
/// cycle": a body that loops forever never returns, and its loop still reads
/// `E` where a value decides a verdict, so `E`'s object is seeded.
#[test]
fn a_body_that_loops_forever_is_still_seeded() {
    with_test_ay_ctx_for_source(READ_SET_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_forever").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_forever");
        let local = const_pointer_local(&body);
        let obj_id = chc_ctx.ref_resolution.const_ref_objects[&local].obj_id;
        assert_eq!(
            seeds_of(&chc_ctx, obj_id, 32),
            vec![(0, bv(1, 32)), (4, bv(2, 32)), (8, bv(3, 32))]
        );
    });
}

const OPTION_REF_SOURCE: &str = r#"
    #![allow(dead_code)]
    const O: Option<&u32> = Some(&[1u32, 2, 3][1]);
    pub fn probe_o() -> u32 {
        let o = O;
        *o.unwrap()
    }
"#;

/// Unit test 18 (R7). An `Option<&T>` constant's payload, decoded
/// value-semantically as `T`, is the pointee WINDOW at the stored pointer's
/// offset: `O = Some(&[1, 2, 3][1])` gives 2. On main the payload reader
/// decoded the target from byte 0 (1). No dual row separates this reader:
/// on `const_pointer_offset_dual.rs::safe_option_ref` the dereference is
/// answered by memory seeded whole (D2) through the payload's pointer slot
/// (D8), and that row still matches when this reader reads from byte 0
/// (mutation measured round 10).
#[test]
fn option_ref_payload_decodes_its_window() {
    with_test_ay_ctx_for_source(OPTION_REF_SOURCE, |ctx| {
        use crate::codegen_ay::chc::expr::codegen_expr_constant_payload::extract_payload_from_alloc;
        let body = find_instance_by_suffix(ctx.tcx, "probe_o").body().unwrap();
        let c = const_assigns(&body)
            .into_iter()
            .map(|(_, c)| c)
            .find(|c| matches!(c.ty().kind(), TyKind::RigidTy(RigidTy::Adt(..))))
            .expect("the Option<&u32> constant O");
        let TyKind::RigidTy(RigidTy::Adt(_, args)) = c.ty().kind() else { unreachable!() };
        let payload_ty = match args.0.first() {
            Some(rustc_public::ty::GenericArgKind::Type(ty)) => *ty,
            other => panic!("Option's type argument, got {other:?}"),
        };
        let bytes = const_pointer::const_bytes(&c).expect("O's bytes");
        let value = extract_payload_from_alloc(
            &bytes,
            c.ty(),
            1,
            payload_ty,
            &ay_bindings::Sort::bitvec(32),
            &|_| None,
        )
        .expect("Some's payload decodes");
        assert_eq!(value.to_string(), bv(2, 32), "the window at the pointer's offset");
    });
}

/// The object id of the one reached target whose data starts with `prefix`.
fn message_object(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
    prefix: &[u8],
) -> u32 {
    let walk = const_pointer::reachable_targets(tcx, body, |_| true);
    let found: Vec<u32> = walk
        .targets
        .iter()
        .filter(|reached| {
            reached.bytes.as_ref().is_some_and(|(bytes, _)| {
                bytes.read_data_bytes(0, bytes.len()).is_some_and(|b| b.starts_with(prefix))
            })
        })
        .map(|reached| chc_ctx.global_object(&reached.key).expect("minted").obj_id)
        .collect();
    assert_eq!(found.len(), 1, "the message's one object");
    found[0]
}

/// D2's read set, Pass 4 half: a constant ASSIGNED to a local in a block
/// from which every path fails (`let msg = "..."; panic!("{}", msg)`, the
/// shape of `assert_unsafe_precondition!`'s message) keeps its address and
/// value fact, but its object is neither noted as read nor seeded. Before,
/// Pass 4 noted every constant assignment whatever its block: `ptr::copy`'s
/// 221-byte precondition message became 221 entry-rule seeds and took
/// `negative/copy_family_symbolic.rs`'s must-fail harnesses from 0.01 s to
/// 18-22 s (round-10 full CHC gate).
#[test]
fn panic_only_message_local_is_not_seeded() {
    with_test_ay_ctx_for_source(READ_SET_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_message_local").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_message_local");
        let obj_id =
            message_object(ctx.tcx, &chc_ctx, &body, b"a message a local holds on a failing path");
        assert!(
            chc_ctx.ref_resolution.const_ref_objects.values().any(|o| o.obj_id == obj_id),
            "the local still names the message's object"
        );
        assert!(
            chc_ctx.ref_resolution.const_ref_memory_inits.iter().all(|init| init.3 != obj_id),
            "a panic-only message is not seeded"
        );
        assert!(
            chc_ctx
                .ref_resolution
                .object_read_types
                .iter()
                .all(|(key, _)| { chc_ctx.global_object(key).is_none_or(|o| o.obj_id != obj_id) }),
            "nor noted as read"
        );
    });
}

#[test]
fn panic_only_long_message_has_exact_value_without_memory_seeds() {
    const MESSAGE: &[u8] = b"a long diagnostic message kept only on the failing branch with more than sixty four bytes";
    with_test_ay_ctx_for_source(READ_SET_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_long_message_local").body().unwrap();
        let chc = ctx_for(ctx.tcx, &body, "probe_long_message_local");
        let obj_id = message_object(ctx.tcx, &chc, &body, MESSAGE);
        let local = chc
            .ref_resolution
            .const_ref_objects
            .iter()
            .find_map(|(local, object)| (object.obj_id == obj_id).then_some(*local))
            .expect("the diagnostic reference keeps its object identity");
        let value = chc.ref_resolution.const_ref_values.get(&local).expect("exact message value");
        let mut base = value;
        while let ay_bindings::ExprValue::Store { array, .. } = base.value() {
            base = array;
        }
        assert!(matches!(base.value(), ay_bindings::ExprValue::Var { .. }));
        let bytes_exact = MESSAGE
            .iter()
            .enumerate()
            .map(|(index, byte)| {
                value
                    .clone()
                    .select(Expr::bitvec_const(index as u64, POINTER_WIDTH))
                    .eq(Expr::bitvec_const(*byte, 8))
            })
            .reduce(|a, b| a.and(b))
            .unwrap();
        let query = format!(
            "(set-logic ALL)\n(declare-const {base} (Array (_ BitVec 64) (_ BitVec 8)))\n(assert (not {bytes_exact}))\n(check-sat)\n"
        );
        assert_eq!(
            run_z3_on_smt2_with_timeout(&query, 30).unwrap(),
            "unsat",
            "every diagnostic byte must be exact for every unobserved array base"
        );
        assert!(chc.ref_resolution.const_ref_memory_inits.iter().all(|init| init.3 != obj_id));
        assert!(chc.ref_resolution.object_read_types.iter().all(|(key, _)| {
            chc.global_object(key).is_none_or(|object| object.obj_id != obj_id)
        }));
        assert_eq!(chc.diagnostics.sound_havoc_drop.get(), 0, "no unread diagnostic bytes");
    });
}

#[test]
fn live_long_string_keeps_its_untracked_bytes_diagnostic() {
    with_test_ay_ctx_for_source(READ_SET_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_long_string_live").body().unwrap();
        let chc = ctx_for(ctx.tcx, &body, "probe_long_string_live");
        assert!(chc.diagnostics.sound_havoc_drop.get() > 0);
        let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        assert!(reasons["probe_long_string_live"].contains_key("untracked_constant_bytes"));
    });
}

#[test]
fn direct_fixed_array_window_requires_the_exact_decoded_cache_entry() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        const VALUES: [u8; 3] = [9, 1, 2];
        const TAIL: &[u8; 2] = unsafe { &*(VALUES.as_ptr().add(1) as *const [u8; 2]) };
        #[inline(never)]
        fn read(value: &[u8; 2]) -> [u8; 2] { *value }
        pub fn probe_cached() -> [u8; 2] { read(TAIL) }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_cached").body().unwrap();
        let mut chc = ctx_for(ctx.tcx, &body, "probe_cached");
        let local = const_pointer_local(&body);
        let object = chc.ref_resolution.const_ref_objects[&local];
        assert_eq!(object.offset, 1, "the real MIR retains the window offset");
        assert!(chc.direct_fixed_array_window_value(local).is_some());
        let cached = std::mem::take(&mut chc.ref_resolution.window_values);
        assert!(chc.ref_resolution.const_ref_values.contains_key(&local));
        assert!(
            chc.direct_fixed_array_window_value(local).is_none(),
            "a pointer fact or same-sort value is not a decoded typed window"
        );
        chc.ref_resolution.window_values = cached;
        chc.ref_resolution.const_ref_objects.get_mut(&local).unwrap().offset = 0;
        assert!(
            chc.direct_fixed_array_window_value(local).is_none(),
            "the cached offset must agree with the current object fact"
        );
    });
}

#[test]
fn direct_fixed_array_window_refuses_an_argument_with_a_later_assignment() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        const VALUES: [u8; 3] = [9, 1, 2];
        const TAIL: &[u8; 2] = unsafe { &*(VALUES.as_ptr().add(1) as *const [u8; 2]) };
        pub fn probe_argument(mut pointer: &'static [u8; 2]) -> ([u8; 2], [u8; 2]) {
            let original = *pointer;
            pointer = TAIL;
            (original, *pointer)
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_argument").body().unwrap();
        assert_eq!(body.arg_locals().len(), 1);
        assert!(body.blocks.iter().flat_map(|block| &block.statements).any(|statement| {
            matches!(&statement.kind, StatementKind::Assign(place, Rvalue::Use(Operand::Constant(_), _)) if place.local == 1)
        }), "the input argument's later constant assignment must survive in MIR");
        let chc = ctx_for(ctx.tcx, &body, "probe_argument");
        assert!(
            chc.direct_fixed_array_window_value(1).is_none(),
            "a future assignment cannot replace the argument's implicit entry definition"
        );
    });
}

#[test]
fn direct_fixed_array_window_refuses_a_reference_slot_that_can_be_replaced() {
    const SOURCE: &str = r#"
        #![allow(dead_code)]
        const VALUES: [u8; 3] = [9, 1, 2];
        const TAIL: &[u8; 2] = unsafe { &*(VALUES.as_ptr().add(1) as *const [u8; 2]) };
        #[inline(never)]
        fn replace_ref(value: &mut &'static [u8; 2]) { *value = &[7, 8]; }
        #[inline(never)]
        fn read(value: &[u8; 2]) -> [u8; 2] { *value }
        pub fn probe_alias() -> [u8; 2] {
            let mut pointer = TAIL;
            replace_ref(&mut pointer);
            read(pointer)
        }
    "#;
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_alias").body().unwrap();
        let chc = ctx_for(ctx.tcx, &body, "probe_alias");
        let local = const_pointer_local(&body);
        assert!(chc.ref_resolution.const_ref_objects.contains_key(&local));
        assert!(!chc.ref_resolution.window_values.is_empty());
        assert!(
            chc.direct_fixed_array_window_value(local).is_none(),
            "one constant assignment does not make an address-taken reference slot immutable"
        );
    });
}

const ZST_AND_FN_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub struct Plain;
    const P: &Plain = &Plain;
    fn one() -> u8 { 1 }
    static SF: fn() -> u8 = one;
    pub fn probe_zst() -> *const Plain { P as *const Plain }
    pub fn probe_fn_static() -> fn() -> u8 { SF }
"#;

/// A constant pointer to a zero-sized value names no cells, so nothing is
/// left free and nothing is recorded. Before, the undecodable (empty) window
/// recorded `const_ref_contents_unmodeled`, which uncertified every
/// counterexample of the harness: six bug rows whose `&dyn Trait` came from a
/// `&Plain` lost their Genuine certificate (walker_validity_intrinsics_dual.rs
/// zeroed_bug and others, round-10 full CHC gate).
#[test]
fn zero_sized_const_ref_records_nothing() {
    with_test_ay_ctx_for_source(ZST_AND_FN_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_zst").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_zst");
        let local = const_pointer_local(&body);
        assert!(chc_ctx.ref_resolution.const_ref_objects.contains_key(&local), "P's object");
        assert_eq!(
            chc_ctx.diagnostics.sound_havoc_drop.get(),
            0,
            "no sound-havoc reason for a pointee with no cells"
        );
    });
}

/// A FIXED static holding a function pointer (`static SF: fn() -> u8 = one`)
/// is folded through the reference MIR reads it by: its value is the identity
/// of the function its relocation names. Before, the window decoder had no
/// fn-pointer arm, so `SF`'s contents were "not decoded" and recorded, and
/// `walker_fn_ptr_completeness_dual.rs::bug_static_eq_other` lost its Genuine
/// certificate.
#[test]
fn fn_pointer_static_folds_to_its_function_identity() {
    with_test_ay_ctx_for_source(ZST_AND_FN_SOURCE, |ctx| {
        let body = find_instance_by_suffix(ctx.tcx, "probe_fn_static").body().unwrap();
        let chc_ctx = ctx_for(ctx.tcx, &body, "probe_fn_static");
        let local = const_pointer_local(&body);
        let c = const_assigns(&body).into_iter().find(|(l, _)| *l == local).unwrap().1;
        let key = const_pointer::const_bytes(&c).unwrap().stored_pointer(0).unwrap().key().unwrap();
        let (sf_bytes, _) = const_pointer::target_bytes(ctx.tcx, &key).expect("SF's bytes");
        let one = sf_bytes.stored_pointer(0).expect("SF holds a function pointer");
        let identity = ChcCtx::fn_ptr_identity_of_const_ptr(&one).expect("one's identity");
        let value = chc_ctx.ref_resolution.const_ref_values.get(&local).expect("SF's value fact");
        assert_eq!(value.to_string(), identity.into_expr().to_string());
        assert_eq!(chc_ctx.diagnostics.sound_havoc_drop.get(), 0, "nothing recorded");
    });
}
