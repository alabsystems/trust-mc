// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! C5b (design trust-mc-reds-final §4.2): a Field path on a flattened value is
//! placed through its MIR types (`flat_field_path_from`). A step `translate_ty`
//! collapses (`UnsafeCell<T>.0`) has no level in the sort tree and is dropped;
//! the raw walk took the next index one level too high, and
//! `RefCell::into_inner(..).1` read the tuple's field 0 for the whole tuple
//! (tools/soundness-duals/refcell_tuple_path_dual.rs, a false certificate on
//! main 756f6eabf).

#![allow(clippy::unwrap_used)]

use super::common::*;
use crate::codegen_ay::chc::codegen_decl_flatten::compute_nested_flat_slot;
use crate::codegen_ay::chc::expr::codegen_expr_flat_struct_path::sort_identity_run;
#[allow(unused_imports)]
use crate::rustc_compat::prelude::*;
use rustc_public::mir::ProjectionElem;

const SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::cell::{Cell, RefCell, UnsafeCell};
    pub struct W(pub u32);
    pub struct S { pub tag: u8, pub cell: RefCell<(u8, u8)> }
    pub fn c5b_probe(
        u: UnsafeCell<(u8, u8)>,
        r: RefCell<(u8, u8)>,
        w: W,
        c: Cell<u16>,
        s: S,
        m: core::mem::ManuallyDrop<(u8, u8)>,
        st: String,
    ) -> u8 {
        0
    }
"#;

fn field(ty: rustc_public::ty::Ty, idx: usize) -> rustc_public::ty::Ty {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Tuple(elems)) => elems[idx],
        TyKind::RigidTy(RigidTy::Adt(def, args)) => {
            crate::codegen_ay::shared::mono_ty::field_ty(&def.variants()[0].fields()[idx], &args)
                .unwrap()
        }
        other => panic!("not a struct or tuple: {other:?}"),
    }
}

fn path(root: rustc_public::ty::Ty, indices: &[usize]) -> Vec<FieldProjection> {
    let mut ty = root;
    indices
        .iter()
        .map(|&idx| {
            ty = field(ty, idx);
            FieldProjection { field_idx: idx, cons_idx: None, field_ty: Some(ty) }
        })
        .collect()
}

fn kept(projs: Result<Vec<FieldProjection>, &'static str>) -> Vec<usize> {
    projs.unwrap().iter().map(|fp| fp.field_idx).collect()
}

/// One step through a wrapper `translate_ty` collapses is a sort-identity
/// run of one; a user newtype's field and RefCell's fields are levels.
#[test]
fn a_wrapper_translate_ty_collapses_is_a_sort_identity_step() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "c5b_probe");
        let [u, r, w, c, _, _, _] = sig.inputs()[..] else { panic!("seven parameters") };
        let run = |ty, indices: &[usize]| {
            sort_identity_run(ty, &ChcCtx::translate_ty(ty).unwrap(), &path(ty, indices))
        };
        assert_eq!(run(u, &[0]), 1, "UnsafeCell<(u8, u8)>.value");
        assert_eq!(run(c, &[0]), 1, "Cell<u16>.value");
        // A user newtype is its own datatype: its field is a level.
        assert_eq!(run(w, &[0]), 0, "W.0");
        // RefCell has two fields with a payload (the borrow flag and the value).
        assert_eq!(run(r, &[1]), 0, "RefCell.value");
        assert_eq!(run(r, &[0]), 0, "RefCell.borrow");
    });
}

/// `into_inner`'s `self.value` then `.1`: the UnsafeCell step is dropped, so the
/// tuple's field 1 is what is read, not its field 0.
#[test]
fn the_unsafe_cell_step_of_into_inner_is_dropped() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "c5b_probe");
        let u = sig.inputs()[0];
        assert_eq!(kept(ChcCtx::flat_field_path_from(u, &path(u, &[0]))), Vec::<usize>::new());
        assert_eq!(kept(ChcCtx::flat_field_path_from(u, &path(u, &[0, 1]))), vec![1]);
    });
}

/// `translate_ty` models `ManuallyDrop<T>` as T's sort. Follow native core's
/// direct `value: T` field or its former `MaybeDangling<T>` carrier: the
/// transparent run disappears and the tuple's field 1 remains field 1.
#[test]
fn a_manually_drop_run_is_dropped_whole() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "c5b_probe");
        let m = sig.inputs()[5];
        let TyKind::RigidTy(RigidTy::Adt(_, args)) = m.kind() else {
            panic!("native ManuallyDrop must be an ADT");
        };
        let [rustc_public::ty::GenericArgKind::Type(value)] = args.0.as_slice() else {
            panic!("native ManuallyDrop has one type argument");
        };
        let (indices, identity_steps) = if field(m, 0) == *value {
            (vec![0, 1], 1)
        } else {
            assert_eq!(field(field(m, 0), 0), *value, "the former carrier contains T");
            (vec![0, 0, 1], 2)
        };
        let sort = ChcCtx::translate_ty(m).unwrap();
        assert_eq!(sort_identity_run(m, &sort, &path(m, &indices)), identity_steps);
        assert_eq!(kept(ChcCtx::flat_field_path_from(m, &path(m, &indices))), vec![1]);
    });
}

/// A step whose sort field is not `translate_ty` of the MIR field is refused:
/// `String`'s model sort is `(fld_ptr, fld_len, fld_cap)`, and its MIR field 0
/// is the whole `Vec<u8>`, not the model's pointer. (A read of `st.vec` takes
/// the String view instead: `string_vec_reads_the_vec_model_from_the_string_slots`.)
#[test]
fn a_step_whose_sort_disagrees_with_its_type_is_refused() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "c5b_probe");
        let st = sig.inputs()[6];
        assert_eq!(
            ChcCtx::flat_field_path_from(st, &path(st, &[0])).err(),
            Some("field_sort_differs_from_type")
        );
    });
}

/// `s.cell.value.0.1` on `S { tag: u8, cell: RefCell<(u8, u8)> }`, flattened to
/// `[tag, borrow, v0, v1]`: the tuple's second byte is slot 3.
#[test]
fn a_path_through_a_refcell_lands_on_the_tuple_leaf() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let sig = fn_sig_by_suffix(ctx.tcx, "c5b_probe");
        let s = sig.inputs()[4];
        let sort = ChcCtx::translate_ty(s).unwrap();
        let sort_path = kept(ChcCtx::flat_field_path_from(s, &path(s, &[1, 1, 0, 1])));
        assert_eq!(sort_path, vec![1, 1, 1], "the UnsafeCell step is dropped");
        assert_eq!(compute_nested_flat_slot(&sort, &sort_path), Some(3));
    });
}

const TUPLE_DEST_SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_tuple_dest(a: u8, b: u8) -> u8 {
        let t = (a, b);
        t.1
    }
"#;

/// A value whose leaves do not tile the destination binds no slot and is
/// booked fail-closed: a single-byte value assigned to a two-byte tuple used
/// to bind slot 0 and leave slot 1 free with nothing booked.
#[test]
fn a_value_that_does_not_tile_the_destination_fails_closed() {
    with_test_ay_ctx_for_source(TUPLE_DEST_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_tuple_dest");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_tuple_dest", ChcConfig::default());
        chc_ctx.declare_block_relations();
        let dest = (0..body.locals().len())
            .find(|&l| {
                chc_ctx.flatten.flattened_tuple_locals.contains(&l)
                    && matches!(body.locals()[l].ty.kind(), TyKind::RigidTy(RigidTy::Tuple(ref e)) if e.len() == 2)
            })
            .expect("the (u8, u8) local is flattened");
        let fail_closed_before = chc_ctx.diagnostics.place_translation_drop.get();
        let constraints = chc_ctx
            .build_flattened_destination_field_constraints(dest, Expr::bitvec_const(7u64, 8))
            .expect("the builder answers");
        assert_eq!(constraints.len(), 2, "every slot is named");
        assert!(
            constraints.iter().all(|(_, c)| *c == Expr::bool_const(true)),
            "no slot is bound to a misaligned leaf: {constraints:?}"
        );
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), fail_closed_before + 1);
    });
}

/// `st.vec` has no level in the String model (`RustString(fld_ptr, fld_len,
/// fld_cap)`), and the raw walk read the model's pointer as the whole vector.
/// The read is the `Vec<u8>` model value built from the String's three slots,
/// in order, with its data array a booked, identified havoc; nothing is
/// dropped fail-closed (`codegen_expr_string_vec_view.rs`).
#[test]
fn string_vec_reads_the_vec_model_from_the_string_slots() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "c5b_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "c5b_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();
        // Locals: 0 is the return place, the parameters follow; `st` is the 7th.
        let st_local = 7;
        let st_ty = body.locals()[st_local].ty;
        let vec_ty = field(st_ty, 0);
        assert_eq!(
            chc_ctx.flattened_field_count(st_local),
            3,
            "st is flattened to the model's leaves"
        );
        let base = chc_ctx.state_idx_for_local(st_local);
        let slots: Vec<String> =
            (0..3).map(|i| chc_ctx.state_var_mgr.state_vars[base + i].0.to_string()).collect();

        let havoc_before = chc_ctx.diagnostics.sound_havoc_drop.get();
        let fail_closed_before = chc_ctx.diagnostics.place_translation_drop.get();
        let place = Place { local: st_local, projection: vec![ProjectionElem::Field(0, vec_ty)] };
        let view = chc_ctx
            .translate_place_with_modified(&place, &HashSet::new())
            .expect("st.vec reads through the String model");
        chc_ctx.flush_deferred_approximation_identities();

        assert_eq!(
            Some(view.sort().clone()),
            ChcCtx::translate_ty(vec_ty),
            "the Vec<u8> model sort"
        );
        let text = view.to_string();
        let at: Vec<usize> = slots
            .iter()
            .map(|name| text.find(name.as_str()).unwrap_or_else(|| panic!("{name} in {text}")))
            .collect();
        assert!(at[0] < at[1] && at[1] < at[2], "ptr, len, cap in order: {text}");
        assert!(text.contains("string_vec_data"), "the data is the booked havoc: {text}");
        assert_eq!(chc_ctx.diagnostics.sound_havoc_drop.get(), havoc_before + 1);
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), fail_closed_before);
        assert!(
            chc_ctx.vc.approximated_vars.iter().any(|v| v.starts_with("string_vec_data")),
            "the havoc carries its identity: {:?}",
            chc_ctx.vc.approximated_vars
        );
    });
}

/// The other way: a `Vec<u8>` value stored into the flattened `String` binds
/// its slots to the vector's pointer, length and capacity, and books the
/// dropped data array (unattributed). The leaf guard refused it (four leaves,
/// three slots) and main bound them without a booking.
#[test]
fn a_vec_stored_into_a_string_binds_ptr_len_cap() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "c5b_probe");
        let body = instance.body().expect("body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "c5b_probe", ChcConfig::default());
        chc_ctx.declare_block_relations();
        let st_local = 7;
        let vec_ty = field(body.locals()[st_local].ty, 0);
        let vec_sort = ChcCtx::translate_ty(vec_ty).unwrap();
        let value = Expr::var("probe_vec_value", vec_sort);

        let havoc_before = chc_ctx.diagnostics.sound_havoc_drop.get();
        let fail_closed_before = chc_ctx.diagnostics.place_translation_drop.get();
        let constraints = chc_ctx
            .build_flattened_destination_field_constraints(st_local, value)
            .expect("the builder answers");
        let texts: Vec<(usize, String)> =
            constraints.iter().map(|(i, c)| (*i, c.to_string())).collect();
        assert_eq!(texts.len(), 3, "every String slot is bound: {texts:?}");
        for (slot, field_name) in ["fld_ptr", "fld_len", "fld_cap"].iter().enumerate() {
            let (i, text) = &texts[slot];
            assert_eq!(*i, slot);
            assert!(
                text.contains(field_name) && text.contains("probe_vec_value"),
                "slot {slot} is the vector's {field_name}: {text}"
            );
        }
        assert_eq!(chc_ctx.diagnostics.sound_havoc_drop.get(), havoc_before + 1);
        assert_eq!(chc_ctx.diagnostics.place_translation_drop.get(), fail_closed_before);
    });
}
