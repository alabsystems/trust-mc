// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! An element store through a pointer to an array with no register referent
//! (`stmt/codegen_stmt_store/deref_elem_store.rs`) and through a static array
//! (`codegen_stmt_store_ref.rs`, the static lane). Both used to reach the
//! projection fallback, which havocked the POINTER and lost the write, so a
//! read of the element returned its old value and an assertion over it was
//! proved from a false error obligation
//! (tools/soundness-duals/lost_deref_elem_store_dual.rs). Each bug probe must
//! now reach its error, and each safe twin must prove with no drop reason.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;
use std::collections::BTreeMap;

const ELEM_STORE_PROBE: &str = r#"
    #![allow(dead_code, static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AssertHook"]
        pub fn assert(cond: bool, _msg: &str) {
            let _ = cond;
        }
    }

    static mut G_BUG: [u8; 4] = [1, 2, 3, 4];
    static mut G_SAFE: [u8; 4] = [1, 2, 3, 4];
    static mut G_SYM: [u8; 4] = [1, 2, 3, 4];
    static mut G_RAW: [u8; 4] = [1, 2, 3, 4];
    static mut G_WHOLE: [u8; 4] = [1, 2, 3, 4];

    pub fn probe_box_elem_ref_read_bug() {
        let mut b = Box::new([1u8, 2, 3, 4]);
        b[3] = 8;
        let e = &b[3];
        kani::assert(*e == 4, "stale element through its address");
    }

    pub fn probe_box_elem_ref_read_safe() {
        let mut b = Box::new([1u8, 2, 3, 4]);
        b[3] = 8;
        let e = &b[3];
        kani::assert(*e == 8, "written element through its address");
    }

    pub fn probe_static_raw_elem_read_safe() {
        unsafe {
            G_RAW[3] = 99;
            let p = core::ptr::addr_of!(G_RAW) as *const u8;
            kani::assert(*p.add(3) == 99, "written element in the memory image");
        }
    }

    pub fn probe_static_whole_store_raw_read_safe() {
        unsafe {
            G_WHOLE = [1, 2, 3, 99];
            let p = core::ptr::addr_of!(G_WHOLE) as *const u8;
            kani::assert(*p.add(3) == 99, "whole store in the memory image");
        }
    }

    pub fn probe_box_elem_store_bug() {
        let mut b = Box::new([1u8, 2, 3, 4]);
        b[3] = 8;
        kani::assert(b[3] == 4, "stale element");
    }

    pub fn probe_box_elem_store_safe() {
        let mut b = Box::new([1u8, 2, 3, 4]);
        b[3] = 8;
        kani::assert(b[3] == 8, "written element");
        kani::assert(b[2] == 3, "other element kept");
    }

    pub fn probe_box_elem_store_symbolic_safe(i: usize) {
        let mut b = Box::new([1u8, 2, 3, 4]);
        if i < 4 {
            b[i] = 9;
            kani::assert(b[i] == 9, "written element");
        }
    }

    pub fn probe_static_elem_store_bug() {
        unsafe {
            G_BUG[3] = 99;
            kani::assert(G_BUG[3] == 4, "stale element");
        }
    }

    pub fn probe_static_elem_store_safe() {
        unsafe {
            G_SAFE[3] = 99;
            kani::assert(G_SAFE[3] == 99, "written element");
            kani::assert(G_SAFE[1] == 2, "other element kept");
        }
    }

    pub fn probe_static_elem_store_symbolic_bug(i: usize) {
        unsafe {
            if i < 4 {
                G_SYM[i] = 99;
                kani::assert(G_SYM[0] == 1, "element 0 may be written");
            }
        }
    }
"#;

/// Encode `fn_name`, solve it, and return the verdict with the drop reasons.
fn solve_probe(fn_name: &str) -> (String, BTreeMap<String, usize>) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let mut verdict = None;
    with_test_ay_ctx_for_source(ELEM_STORE_PROBE, |ctx| {
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

fn assert_bug_reached(fn_name: &str) {
    let (verdict, reasons) = solve_probe(fn_name);
    assert_eq!(
        verdict, "sat",
        "{fn_name}: the stale-element assertion must be refutable; reasons {reasons:?}"
    );
}

fn assert_safe_clean(fn_name: &str) {
    let (verdict, reasons) = solve_probe(fn_name);
    assert_eq!(
        verdict, "unsat",
        "{fn_name}: the written element must be read back; reasons {reasons:?}"
    );
    for lost in
        ["proj_no_field_projections", "deref_elem_store_unplaced", "static_elem_store_unplaced"]
    {
        assert!(
            !reasons.contains_key(lost),
            "{fn_name}: the store must be placed, got {reasons:?}"
        );
    }
}

#[test]
fn test_box_elem_store_reaches_the_read() {
    assert_bug_reached("probe_box_elem_store_bug");
}

#[test]
fn test_box_elem_store_safe_twin_proves_clean() {
    assert_safe_clean("probe_box_elem_store_safe");
}

#[test]
fn test_box_elem_store_symbolic_index_safe_twin_proves_clean() {
    assert_safe_clean("probe_box_elem_store_symbolic_safe");
}

#[test]
fn test_static_elem_store_reaches_the_read() {
    assert_bug_reached("probe_static_elem_store_bug");
}

#[test]
fn test_static_elem_store_safe_twin_proves_clean() {
    assert_safe_clean("probe_static_elem_store_safe");
}

#[test]
fn test_static_elem_store_symbolic_index_may_hit_element_zero() {
    assert_bug_reached("probe_static_elem_store_symbolic_bug");
}

/// A read through the element's address selects the ELEMENT's type-indexed
/// array; the first fix wrote only the array's, so this bug probe was proved
/// and the safe twin refuted (review of fix/chc-lost-writes, 2026-09-27).
#[test]
fn test_box_elem_store_reaches_a_read_through_the_element_address() {
    assert_bug_reached("probe_box_elem_ref_read_bug");
}

#[test]
fn test_box_elem_store_element_address_safe_twin_proves_clean() {
    assert_safe_clean("probe_box_elem_ref_read_safe");
}

/// A raw read of a static selects its memory image, which the element store
/// now writes too (`store_static_array_element_image`).
#[test]
fn test_static_elem_store_reaches_the_memory_image() {
    assert_safe_clean("probe_static_raw_elem_read_safe");
}

/// A whole-array static store writes the memory image element by element
/// (`store_static_array_image`); pre-existing on main.
#[test]
fn test_static_whole_store_reaches_the_memory_image() {
    assert_safe_clean("probe_static_whole_store_raw_read_safe");
}
