// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The unsize-to-dyn alias store (`try_translate_dyn_trait_coercion`,
//! `heap/heap_unsize_alias.rs`) republished a `Box` payload's CONCRETE view
//! into the field cells the dyn read uses. A field store reaches only those
//! field cells, so `d.a = 255; let o: Box<dyn Tv> = d;` put the constructor's
//! `a` back and `assert!(o.get() < 255)` was proved
//! (tools/soundness-duals/walker_dyn_heap_write_dual.rs,
//! bug_write_then_coerce_*). After a field store the alias store now
//! republishes the field view itself; a fresh allocation's initializer, which
//! writes both views, does not count as a field store. A tuple field is read
//! back through its leaves too: the walked impl's field map rebuilds tuples
//! and nested structs from the leaves a field store writes
//! (`bug_tuple_leaf_then_coerce`, review of fix/chc-lost-writes). A field the
//! field map still loads whole (an array of tuples) fails closed after a field
//! store.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;

const UNSIZE_PROBE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    pub trait Tv { fn get(&self) -> u8; }
    pub struct DV { pub a: u8, pub b: u8 }
    impl Tv for DV { fn get(&self) -> u8 { self.a } }

    pub fn probe_write_then_coerce_bug(a: u8) {
        let mut d = Box::new(DV { a, b: 1 });
        d.a = 255;
        let o: Box<dyn Tv> = d;
        kani::assert(o.get() < 255, "the written field is read through the dyn receiver");
    }

    pub fn probe_write_then_coerce_safe(a: u8) {
        let mut d = Box::new(DV { a, b: 1 });
        d.a = 200;
        let o: Box<dyn Tv> = d;
        kani::assert(o.get() == 200, "the written field is read through the dyn receiver");
    }

    pub struct D3 { pub x: ((u8, u8), u8), pub z: u8 }
    impl Tv for D3 { fn get(&self) -> u8 { (self.x.0).0 } }

    pub fn probe_tuple_leaf_then_coerce_safe(a: u8) {
        let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
        d.x.0.0 = 200;
        let o: Box<dyn Tv> = d;
        kani::assert(o.get() == 200, "the written leaf is read through the dyn receiver");
    }

    pub fn probe_tuple_leaf_then_coerce_bug(a: u8) {
        let mut d = Box::new(D3 { x: ((a, 1), 2), z: 4 });
        d.x.0.0 = 255;
        let o: Box<dyn Tv> = d;
        kani::assert(o.get() < 255, "the written leaf is read through the dyn receiver");
    }

    pub struct DA { pub x: [(u8, u8); 2], pub z: u8 }
    impl Tv for DA { fn get(&self) -> u8 { self.z } }

    pub fn probe_array_of_tuples_field_store_safe(a: u8) {
        let mut d = Box::new(DA { x: [(a, 1), (2, 3)], z: 4 });
        d.z = 200;
        let o: Box<dyn Tv> = d;
        kani::assert(o.get() == 200, "the written field is read through the dyn receiver");
    }

    pub struct N2 { pub x: (u8, u8), pub z: u8 }
    #[derive(Clone, Copy)]
    pub struct I { pub p: u8, pub q: u8 }
    pub struct N3 { pub i: I, pub z: u8 }

    pub fn probe_pair_leaf_whole_read_bug(a: u8) {
        let mut d = Box::new(N2 { x: (a, 1), z: 4 });
        d.x.0 = 255;
        let t = d.x;
        kani::assert(t.0 < 255, "the written leaf is read back through the whole field");
    }

    pub fn probe_pair_leaf_whole_read_safe(a: u8) {
        let mut d = Box::new(N2 { x: (a, 1), z: 4 });
        d.x.0 = 200;
        let t = d.x;
        kani::assert(t.0 == 200, "the written leaf is read back through the whole field");
    }

    pub fn probe_struct_leaf_whole_read_safe(a: u8) {
        let mut d = Box::new(N3 { i: I { p: a, q: 1 }, z: 4 });
        d.i.p = 200;
        let i = d.i;
        kani::assert(i.p == 200 && i.q == 1, "the written leaf is read back through the whole field");
    }

    pub fn probe_coerce_after_new_safe(a: u8) {
        let o: Box<dyn Tv> = Box::new(DV { a, b: 1 });
        kani::assert(o.get() == a, "the constructed field is read through the dyn receiver");
    }
"#;

fn solve_probe(fn_name: &str) -> (String, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(UNSIZE_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let mut vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );
        vc.propagate_constants();
        vc.prune_orphan_block_rules();
        vc.prune_dead_identity_scalars();
        vc.normalize_free_array_bases();
        crate::codegen_ay::chc::scalarize_vc(&mut vc);
        vc.prune_dead_vars_and_constraints();
        let smt = emit_chc(&vc).to_string();
        verdict = Some(
            run_z3_on_smt2_with_timeout(&smt, z3_test_timeout_secs_or(30))
                .unwrap_or_else(|e| panic!("AY failed on {fn_name}: {e}")),
        );
    });
    let reasons = crate::codegen_ay::take_translation_drop_site_reasons_by_fn()
        .remove(fn_name)
        .unwrap_or_default();
    (verdict.expect("the probe was encoded"), reasons)
}

#[test]
fn test_field_store_before_unsize_reaches_the_dyn_read() {
    let (verdict, reasons) = solve_probe("probe_write_then_coerce_bug");
    assert_eq!(verdict, "sat", "the dyn read must see the stored 255; reasons {reasons:?}");
}

#[test]
fn test_field_store_before_unsize_safe_twin_proves() {
    let (verdict, reasons) = solve_probe("probe_write_then_coerce_safe");
    assert_eq!(verdict, "unsat", "the dyn read must see the stored 200; reasons {reasons:?}");
    assert!(!reasons.contains_key("unsize_alias_view_stale"), "got {reasons:?}");
}

#[test]
fn test_unsize_after_box_new_is_not_a_field_store() {
    let (verdict, reasons) = solve_probe("probe_coerce_after_new_safe");
    assert_eq!(verdict, "unsat", "the constructed field must be read back; reasons {reasons:?}");
    assert!(!reasons.contains_key("unsize_alias_view_stale"), "got {reasons:?}");
}

/// A leaf store into a tuple field reaches the walked impl's `(self.x.0).0`:
/// the field map rebuilds the tuple from its leaves, which the field-view
/// republish writes. On the first fix the bug twin verified SUCCESSFUL clean
/// (the read selected the tuple's own type-indexed array), and the interim
/// fix failed closed on every tuple payload.
#[test]
fn test_tuple_field_leaf_store_reaches_the_dyn_read() {
    let (verdict, reasons) = solve_probe("probe_tuple_leaf_then_coerce_bug");
    assert_eq!(verdict, "sat", "the dyn read must see the stored 255; reasons {reasons:?}");
}

#[test]
fn test_tuple_field_leaf_store_safe_twin_proves() {
    let (verdict, reasons) = solve_probe("probe_tuple_leaf_then_coerce_safe");
    assert_eq!(verdict, "unsat", "the dyn read must see the stored 200; reasons {reasons:?}");
    assert!(!reasons.contains_key("unsize_alias_view_stale"), "got {reasons:?}");
}

/// An array of tuples is loaded whole by the field map, from an array no leaf
/// store writes: after a field store the coercion fails closed.
#[test]
fn test_field_read_as_a_whole_fails_closed_after_a_field_store() {
    let (_verdict, reasons) = solve_probe("probe_array_of_tuples_field_store_safe");
    assert!(
        reasons.contains_key("unsize_alias_view_stale"),
        "an array-of-tuples field is read whole; got {reasons:?}"
    );
}

/// A whole read of a struct or tuple field through the Box rebuilds it from
/// its leaves, which a leaf store writes; it used to select the field type's
/// own array, which kept the constructor's value (the safe twin was a Genuine
/// failure on main, and the bug twin was left to a solver timeout).
#[test]
fn test_whole_tuple_field_read_sees_the_leaf_store() {
    let (verdict, reasons) = solve_probe("probe_pair_leaf_whole_read_bug");
    assert_eq!(verdict, "sat", "the whole-field read must see the stored 255; reasons {reasons:?}");
}

#[test]
fn test_whole_tuple_field_read_safe_twin_proves() {
    let (verdict, reasons) = solve_probe("probe_pair_leaf_whole_read_safe");
    assert_eq!(verdict, "unsat", "the whole-field read must see the stored 200; reasons {reasons:?}");
}

#[test]
fn test_whole_struct_field_read_safe_twin_proves() {
    let (verdict, reasons) = solve_probe("probe_struct_leaf_whole_read_safe");
    assert_eq!(verdict, "unsat", "the whole-field read must see the stored 200; reasons {reasons:?}");
}
