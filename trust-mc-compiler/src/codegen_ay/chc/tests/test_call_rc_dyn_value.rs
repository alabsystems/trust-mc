// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Part of #4014: Focused classification matrix for `check_rc_dyn_value` failure.
//!
//! Three probes isolate whether the live CTREX is caused by:
//! 1. Full-shape composition (constructor + Rc + scope cleanup)
//! 2. Scope cleanup contamination (drop tail)
//! 3. Constructor return/value-store integration (`Table::new(...)`)
//!
//! Design: `designs/2026-03-19-issue-4014-rc-dyn-value-full-shape-reroute.md`

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// ---------------------------------------------------------------------------
// Probe 1: Full shape — mirrors check_rc_dyn_value exactly
// ---------------------------------------------------------------------------
const PROBE_RC_DYN_VALUE_FULL_SHAPE: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            unsafe {
                COUNTER += 1;
            }
            Table { fancy }
        }

        fn new_furniture(fancy: bool) -> Rc<dyn Furniture> {
            Rc::new(Table::new(fancy))
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn probe_rc_dyn_value_full_shape(val: bool) {
        let table = Table::new(val);
        let furniture = Table::new_furniture(val);
        assert!(furniture.cost() == table.cost());
    }
"#;

// ---------------------------------------------------------------------------
// Probe 2: Same assertion, but neutralize cleanup with forget
// ---------------------------------------------------------------------------
const PROBE_RC_DYN_VALUE_FORGET_TAIL: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            unsafe {
                COUNTER += 1;
            }
            Table { fancy }
        }

        fn new_furniture(fancy: bool) -> Rc<dyn Furniture> {
            Rc::new(Table::new(fancy))
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn probe_rc_dyn_value_forget_tail(val: bool) {
        let table = Table::new(val);
        let furniture = Table::new_furniture(val);
        assert!(furniture.cost() == table.cost());
        core::mem::forget(table);
        core::mem::forget(furniture);
    }
"#;

// ---------------------------------------------------------------------------
// Probe 3: Literal ctor (no Table::new) + forget tail
// ---------------------------------------------------------------------------
const PROBE_RC_DYN_VALUE_LITERAL_CTOR_FORGET_TAIL: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn probe_rc_dyn_value_literal_ctor_forget_tail(val: bool) {
        let table = Table { fancy: val };
        let furniture: Rc<dyn Furniture> = Rc::new(Table { fancy: val });
        assert!(furniture.cost() == table.cost());
        core::mem::forget(table);
        core::mem::forget(furniture);
    }
"#;

// ---------------------------------------------------------------------------
// Probe 4: Table::new ctor with Rc but NO dyn dispatch — isolate ctor vs dyn
// ---------------------------------------------------------------------------
const PROBE_RC_DYN_VALUE_CTOR_NO_DYN: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            unsafe {
                COUNTER += 1;
            }
            Table { fancy }
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn probe_rc_dyn_value_ctor_no_dyn(val: bool) {
        let table = Table::new(val);
        let table2 = Table::new(val);
        assert!(table.fancy == table2.fancy);
        core::mem::forget(table);
        core::mem::forget(table2);
    }
"#;

// ---------------------------------------------------------------------------
// Probe 5: Table::new ctor into Rc (concrete, no dyn) + forget
// ---------------------------------------------------------------------------
const PROBE_RC_CONCRETE_CTOR_FORGET: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            unsafe {
                COUNTER += 1;
            }
            Table { fancy }
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn probe_rc_concrete_ctor_forget(val: bool) {
        let table = Table::new(val);
        let rc_table: Rc<Table> = Rc::new(Table::new(val));
        assert!(rc_table.cost() == table.cost());
        core::mem::forget(table);
        core::mem::forget(rc_table);
    }
"#;

// ---------------------------------------------------------------------------
// Probe 6: Table::new + Box<dyn> (no Rc) + forget — isolate Rc vs dyn coercion
// ---------------------------------------------------------------------------
const PROBE_BOX_DYN_CTOR_FORGET: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            unsafe {
                COUNTER += 1;
            }
            Table { fancy }
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn probe_box_dyn_ctor_forget(val: bool) {
        let table = Table::new(val);
        let boxed: Box<dyn Furniture> = Box::new(Table::new(val));
        assert!(boxed.cost() == table.cost());
        core::mem::forget(table);
        core::mem::forget(boxed);
    }
"#;

// ---------------------------------------------------------------------------
// Probe 7: Table::new_furniture wrapper + forget — isolate wrapper inlining
// ---------------------------------------------------------------------------
const PROBE_NEW_FURNITURE_WRAPPER_FORGET: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    static mut COUNTER: i8 = 0;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            unsafe {
                COUNTER += 1;
            }
            Table { fancy }
        }
    }

    impl Drop for Table {
        fn drop(&mut self) {
            unsafe {
                COUNTER -= 1;
            }
        }
    }

    pub fn probe_new_furniture_wrapper_forget(val: bool) {
        let table = Table::new(val);
        // Inline Rc::new(Table::new(val)) directly, no wrapper fn
        let furniture: Rc<dyn Furniture> = Rc::new(Table::new(val));
        assert!(furniture.cost() == table.cost());
        core::mem::forget(table);
        core::mem::forget(furniture);
    }
"#;

// ---------------------------------------------------------------------------
// Probe 8: Wrapper fn with literal ctor (no Table::new nested call)
// Isolates: is the issue Table::new as nested call, or Rc::new as nested call?
// ---------------------------------------------------------------------------
const PROBE_WRAPPER_LITERAL_CTOR_FORGET: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        fn new_furniture_literal(fancy: bool) -> Rc<dyn Furniture> {
            Rc::new(Table { fancy })
        }
    }

    pub fn probe_wrapper_literal_ctor_forget(val: bool) {
        let table = Table { fancy: val };
        let furniture = Table::new_furniture_literal(val);
        assert!(furniture.cost() == table.cost());
        core::mem::forget(table);
        core::mem::forget(furniture);
    }
"#;

// ---------------------------------------------------------------------------
// Probe 9: Wrapper fn with Table::new but NO static mut write
// Isolates: is the static mut write the specific nested-call blocker?
// ---------------------------------------------------------------------------
const PROBE_WRAPPER_PURE_CTOR_FORGET: &str = r#"
    #![allow(dead_code, unused_unsafe)]

    use std::rc::Rc;

    struct Table {
        fancy: bool,
    }

    trait Furniture {
        fn cost(&self) -> i16;
    }

    impl Furniture for Table {
        fn cost(&self) -> i16 {
            if self.fancy { 1000 } else { 200 }
        }
    }

    impl Table {
        pub fn new(fancy: bool) -> Self {
            Table { fancy }
        }

        fn new_furniture(fancy: bool) -> Rc<dyn Furniture> {
            Rc::new(Table::new(fancy))
        }
    }

    pub fn probe_wrapper_pure_ctor_forget(val: bool) {
        let table = Table::new(val);
        let furniture = Table::new_furniture(val);
        assert!(furniture.cost() == table.cost());
        core::mem::forget(table);
        core::mem::forget(furniture);
    }
"#;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// Part of #4014 D2 probe 1: Full-shape mirror of check_rc_dyn_value.
#[test]
fn test_probe_rc_dyn_value_full_shape_classification() {
    with_test_ay_ctx_for_source(PROBE_RC_DYN_VALUE_FULL_SHAPE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_dyn_value_full_shape");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_dyn_value_full_shape", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "full_shape should produce rules");
        assert!(has_any_constraints(&vc), "full_shape should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 1] full_shape -> {result:?}");
        // Classification probe — log result for matrix interpretation.
    });
}

/// Part of #4014 D2 probe 2: Neutralize cleanup with forget.
#[test]
fn test_probe_rc_dyn_value_forget_tail_classification() {
    with_test_ay_ctx_for_source(PROBE_RC_DYN_VALUE_FORGET_TAIL, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_dyn_value_forget_tail");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_dyn_value_forget_tail", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "forget_tail should produce rules");
        assert!(has_any_constraints(&vc), "forget_tail should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 2] forget_tail -> {result:?}");
    });
}

/// Part of #4014 D2 probe 3: Literal ctor (no Table::new) + forget.
#[test]
fn test_probe_rc_dyn_value_literal_ctor_forget_tail_classification() {
    with_test_ay_ctx_for_source(PROBE_RC_DYN_VALUE_LITERAL_CTOR_FORGET_TAIL, |ctx| {
        let instance =
            find_instance_by_suffix(ctx.tcx, "probe_rc_dyn_value_literal_ctor_forget_tail");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            "probe_rc_dyn_value_literal_ctor_forget_tail",
            ChcConfig::default(),
        );

        assert!(!vc.rules.is_empty(), "literal_ctor_forget should produce rules");
        assert!(has_any_constraints(&vc), "literal_ctor_forget should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 3] literal_ctor_forget_tail -> {result:?}");
    });
}

/// Part of #4014: Probe 4 — Table::new ctor without Rc/dyn, forget tail.
/// Isolates whether Table::new return value itself is correct.
/// Dumps full SMT2 for analysis when SAT.
#[test]
fn test_probe_rc_dyn_value_ctor_no_dyn_classification() {
    with_test_ay_ctx_for_source(PROBE_RC_DYN_VALUE_CTOR_NO_DYN, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_dyn_value_ctor_no_dyn");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_dyn_value_ctor_no_dyn", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "ctor_no_dyn should produce rules");
        assert!(has_any_constraints(&vc), "ctor_no_dyn should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        // Dump full SMT2 for analysis (#4014)
        eprintln!("[#4014 probe 4] === FULL SMT2 ===");
        for line in smt.lines() {
            eprintln!("[#4014 probe 4] {line}");
        }
        eprintln!("[#4014 probe 4] === END SMT2 ===");
        eprintln!("[#4014 probe 4] rule_count = {}", vc.rules.len());
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 4] ctor_no_dyn -> {result:?}");
    });
}

/// Part of #4014: Probe 5 — Table::new into Rc<Table> (concrete, no dyn), forget.
/// Isolates whether Rc allocation preserves ctor return value without dyn coercion.
#[test]
fn test_probe_rc_concrete_ctor_forget_classification() {
    with_test_ay_ctx_for_source(PROBE_RC_CONCRETE_CTOR_FORGET, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_concrete_ctor_forget");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_concrete_ctor_forget", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "rc_concrete_ctor should produce rules");
        assert!(has_any_constraints(&vc), "rc_concrete_ctor should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 5] rc_concrete_ctor_forget -> {result:?}");
    });
}

/// Part of #4014: Probe 6 — Table::new + Box<dyn Furniture>, forget.
/// Isolates whether the issue is Rc-specific or general dyn coercion.
#[test]
fn test_probe_box_dyn_ctor_forget_classification() {
    with_test_ay_ctx_for_source(PROBE_BOX_DYN_CTOR_FORGET, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_box_dyn_ctor_forget");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_box_dyn_ctor_forget", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "box_dyn_ctor should produce rules");
        assert!(has_any_constraints(&vc), "box_dyn_ctor should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 6] box_dyn_ctor_forget -> {result:?}");
    });
}

/// Part of #4014: Probe 7 — Rc::new(Table::new(val)) directly (no wrapper fn), forget.
/// Isolates whether the wrapper fn `new_furniture` inlining causes the issue.
#[test]
fn test_probe_new_furniture_wrapper_forget_classification() {
    with_test_ay_ctx_for_source(PROBE_NEW_FURNITURE_WRAPPER_FORGET, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_new_furniture_wrapper_forget");
        let body = instance.body().expect("function body");
        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_new_furniture_wrapper_forget", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "wrapper_forget should produce rules");
        assert!(has_any_constraints(&vc), "wrapper_forget should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 7] new_furniture_wrapper_forget -> {result:?}");
    });
}

/// Part of #4014: Probe 8 — Wrapper fn with literal ctor (no Table::new nested call).
/// Isolates whether the issue is Table::new as nested call vs Rc::new as nested call.
#[test]
fn test_probe_wrapper_literal_ctor_forget_classification() {
    with_test_ay_ctx_for_source(PROBE_WRAPPER_LITERAL_CTOR_FORGET, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapper_literal_ctor_forget");
        let body = instance.body().expect("function body");
        let vc =
            mir_to_chc(ctx.tcx, &body, "probe_wrapper_literal_ctor_forget", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "wrapper_literal_ctor should produce rules");
        assert!(has_any_constraints(&vc), "wrapper_literal_ctor should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 8] wrapper_literal_ctor_forget -> {result:?}");
    });
}

/// Part of #4014: Probe 9 — Wrapper fn with Table::new but NO static mut write.
/// Isolates whether the static mut write is the specific nested-call blocker.
#[test]
fn test_probe_wrapper_pure_ctor_forget_classification() {
    with_test_ay_ctx_for_source(PROBE_WRAPPER_PURE_CTOR_FORGET, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_wrapper_pure_ctor_forget");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_wrapper_pure_ctor_forget", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "wrapper_pure_ctor should produce rules");
        assert!(has_any_constraints(&vc), "wrapper_pure_ctor should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let result = run_z3_on_smt2_with_timeout(&smt, timeout);
        eprintln!("[#4014 probe 9] wrapper_pure_ctor_forget -> {result:?}");
    });
}

// ---------------------------------------------------------------------------
// Part of #4014 D2: Diagnostic classification — compare fallback reasons
// between probe 7 (PROOF) and probe 8 (CTREX).
// ---------------------------------------------------------------------------

fn classify_with_diagnostics(source: &str, fn_name: &str, label: &str) -> String {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    let mut result = String::new();
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(30);
        let solver_result = run_z3_on_smt2_with_timeout(&smt, timeout);

        eprintln!("[#4014 {label}] solver -> {solver_result:?}");
        eprintln!("[#4014 {label}] fallback_count = {fallback_count}");
        eprintln!("[#4014 {label}] rule_count = {}", vc.rules.len());

        // Dump state variable names and sorts for debugging
        for decl in vc.vars() {
            if decl.name.contains("_out_") || decl.name.contains("_in_") {
                let sort_str = format!("{}", decl.sort);
                let sort_short = if sort_str.len() > 80 { &sort_str[..80] } else { &sort_str };
                eprintln!("[#4014 {label}] var: {} : {sort_short}", decl.name);
            }
        }

        // Print SMT2 for manual analysis
        eprintln!("[#4014 {label}] === SMT2 START ===");
        for line in smt.lines().take(200) {
            eprintln!("[#4014 {label}] {line}");
        }
        eprintln!("[#4014 {label}] === SMT2 END (truncated at 200 lines) ===");

        result = format!("{solver_result:?}");
    });

    let translation_drops = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    if !translation_drops.is_empty() {
        eprintln!("[#4014 {label}] translation_drops = {translation_drops:?}");
    }
    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    if inferable_count > 0 {
        eprintln!("[#4014 {label}] inferable_predicate_count = {inferable_count}");
    }

    result
}

/// Part of #4014: Diagnostic dump for probe 4 (ctor_no_dyn) — simplest SAT case.
/// Table::new with static mut, no Rc/dyn. Should isolate the inline walker's
/// handling of static mut writes in Table::new.
#[test]
fn test_probe_4_ctor_no_dyn_diagnostic_dump() {
    let r4 = classify_with_diagnostics(
        PROBE_RC_DYN_VALUE_CTOR_NO_DYN,
        "probe_rc_dyn_value_ctor_no_dyn",
        "probe4_ctor_no_dyn",
    );
    let r9 = classify_with_diagnostics(
        PROBE_WRAPPER_PURE_CTOR_FORGET,
        "probe_wrapper_pure_ctor_forget",
        "probe9_pure_ctor",
    );
    eprintln!("[#4014 COMPARISON] probe4(static_mut_ctor)={r4}, probe9(pure_ctor)={r9}");
}

/// Part of #4014 D2: Diagnostic comparison — probe 7 (passing) vs probe 8 (failing).
/// Probe 7: Rc::new(Table::new(val)) directly — no wrapper fn.
/// Probe 8: Table::new_furniture_literal(val) — wrapper fn returning Rc<dyn Furniture>.
/// The diff identifies the inline return path as the failure seam.
#[test]
fn test_probe_7_vs_8_diagnostic_comparison() {
    let r7 = classify_with_diagnostics(
        PROBE_NEW_FURNITURE_WRAPPER_FORGET,
        "probe_new_furniture_wrapper_forget",
        "probe7_direct",
    );
    let r8 = classify_with_diagnostics(
        PROBE_WRAPPER_LITERAL_CTOR_FORGET,
        "probe_wrapper_literal_ctor_forget",
        "probe8_wrapper",
    );
    eprintln!("[#4014 COMPARISON] probe7(direct)={r7}, probe8(wrapper)={r8}");
    // Part of #4014: Both probes are now unsat (PROOF) after fixing
    // try_inline_rc_arc_new to return value_ptr (alloc + header) instead of
    // alloc_ptr. The store/load address mismatch is resolved.
    assert_eq!(r7, "Ok(\"unsat\")", "probe7 (direct) should be PROOF");
    assert_eq!(r8, "Ok(\"unsat\")", "probe8 (wrapper) should be PROOF");
}

// ---------------------------------------------------------------------------
// Part of #4009: raw-parts classification packet
// ---------------------------------------------------------------------------

const RC_DYN_SOURCE: &str =
    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../tests/trust_mc/Drop/rc_dyn.rs"));

const CHECK_RC_DYN_RAW_PARTS_BLOCK: &str = r#"
#[kani::proof]
fn check_rc_dyn_raw_parts() {
    let table = Table::new_furniture(kani::any());
    let furniture = table.clone();

    let (table_ptr, table_vtable) = Rc::as_ptr(&table).to_raw_parts();
    let (furn_ptr, furn_vtable) = Rc::as_ptr(&furniture).to_raw_parts();
    assert_eq!(table_ptr, furn_ptr);
    assert_eq!(table_vtable, furn_vtable);
}
"#;

const CHECK_RC_DYN_RAW_PARTS_FORGET_BLOCK: &str = r#"
#[kani::proof]
fn check_rc_dyn_raw_parts() {
    let table = Table::new_furniture(kani::any());
    let furniture = table.clone();

    let (table_ptr, table_vtable) = Rc::as_ptr(&table).to_raw_parts();
    let (furn_ptr, furn_vtable) = Rc::as_ptr(&furniture).to_raw_parts();
    assert_eq!(table_ptr, furn_ptr);
    assert_eq!(table_vtable, furn_vtable);
    core::mem::forget(table);
    core::mem::forget(furniture);
}
"#;

const CHECK_RC_DYN_DIFF_RAW_PARTS_BLOCK: &str = r#"
#[kani::proof]
fn check_rc_dyn_diff_raw_parts() {
    let table = Table::new_furniture(kani::any());
    let furniture = Table::new_furniture(kani::any());

    let (table_ptr, table_vtable) = Rc::as_ptr(&table).to_raw_parts();
    let (furn_ptr, furn_vtable) = Rc::as_ptr(&furniture).to_raw_parts();

    // Check that they have different data but same vtable.
    assert_ne!(table_ptr, furn_ptr);
    assert_eq!(table_vtable, furn_vtable);

    // TODO: Enable this once fat pointer comparison has been fixed.
    // https://github.com/model-checking/kani/issues/327
    // assert_ne!(Rc::as_ptr(&table), Rc::as_ptr(&furniture));
}
"#;

const CHECK_RC_DYN_DIFF_RAW_PARTS_FORGET_BLOCK: &str = r#"
#[kani::proof]
fn check_rc_dyn_diff_raw_parts() {
    let table = Table::new_furniture(kani::any());
    let furniture = Table::new_furniture(kani::any());

    let (table_ptr, table_vtable) = Rc::as_ptr(&table).to_raw_parts();
    let (furn_ptr, furn_vtable) = Rc::as_ptr(&furniture).to_raw_parts();

    // Check that they have different data but same vtable.
    assert_ne!(table_ptr, furn_ptr);
    assert_eq!(table_vtable, furn_vtable);
    core::mem::forget(table);
    core::mem::forget(furniture);

    // TODO: Enable this once fat pointer comparison has been fixed.
    // https://github.com/model-checking/kani/issues/327
    // assert_ne!(Rc::as_ptr(&table), Rc::as_ptr(&furniture));
}
"#;

fn replace_exact_block(source: &str, needle: &str, replacement: &str) -> String {
    assert!(source.contains(needle), "expected exact block missing from rc_dyn raw-parts probe");
    source.replacen(needle, replacement, 1)
}

fn normalize_rc_dyn_source(source: &str) -> String {
    let source = source.replace("#[kani::proof]\n", "");
    source.replacen(
        "#![feature(ptr_metadata)]",
        r#"#![feature(ptr_metadata)]
#![allow(static_mut_refs)]
#![allow(dead_code)]
#![feature(register_tool)]
#![register_tool(kanitool)]

mod kani {
    #[kanitool::fn_marker = "AnyModel"]
    pub fn any<T>() -> T {
        panic!("model-only marker function")
    }
}
"#,
        1,
    )
}

fn rc_dyn_raw_parts_forget_tail_source() -> String {
    let source = replace_exact_block(
        RC_DYN_SOURCE,
        CHECK_RC_DYN_RAW_PARTS_BLOCK,
        CHECK_RC_DYN_RAW_PARTS_FORGET_BLOCK,
    );
    normalize_rc_dyn_source(&source)
}

fn rc_dyn_diff_raw_parts_forget_tail_source() -> String {
    let source = replace_exact_block(
        RC_DYN_SOURCE,
        CHECK_RC_DYN_DIFF_RAW_PARTS_BLOCK,
        CHECK_RC_DYN_DIFF_RAW_PARTS_FORGET_BLOCK,
    );
    normalize_rc_dyn_source(&source)
}

const RC_DYN_RAW_PARTS_METADATA_CEILING: usize = 2;
type RcDynRawPartsProbeResult = (String, usize, usize, Vec<String>);

fn probe_rc_dyn_raw_parts(source: &str, fn_name: &str) -> RcDynRawPartsProbeResult {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

    let mut classification = String::new();
    let mut fallback_count = 0;
    let mut inferable_decls = Vec::new();
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        inferable_decls = vc
            .vars()
            .iter()
            .filter(|decl| decl.name.starts_with("P_inf_"))
            .map(|decl| decl.name.to_string())
            .collect();

        fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);

        let smt = emit_chc(&vc).to_string();
        let timeout = z3_test_timeout_secs_or(60);
        classification = run_z3_on_smt2_with_timeout(&smt, timeout).expect("z3 result");
        assert!(
            matches!(classification.as_str(), "sat" | "unsat"),
            "{fn_name} should classify to sat/unsat, got {classification}"
        );
        eprintln!("[#4009 {fn_name}] -> {classification}");
    });

    let inferable_count = crate::codegen_ay::take_inferable_predicate_count();
    (classification, fallback_count, inferable_count, inferable_decls)
}

fn assert_rc_dyn_raw_parts_classification(
    source: &str,
    fn_name: &str,
    expected: &str,
    label: &str,
) {
    let result = probe_rc_dyn_raw_parts(source, fn_name);
    assert_eq!(
        result.0, expected,
        "{label} should classify to {expected} on the exact rc_dyn source"
    );
    eprintln!("[#4009] {label} classification: {}", result.0);
}

fn assert_rc_dyn_raw_parts_metadata_ceiling(source: &str, fn_name: &str, label: &str) {
    let result = probe_rc_dyn_raw_parts(source, fn_name);
    assert!(
        result.1 <= RC_DYN_RAW_PARTS_METADATA_CEILING,
        "{label} fallback_count {} exceeds current-head ceiling {}",
        result.1,
        RC_DYN_RAW_PARTS_METADATA_CEILING
    );
    assert!(
        result.2 <= RC_DYN_RAW_PARTS_METADATA_CEILING,
        "{label} inferable_count {} exceeds current-head ceiling {}",
        result.2,
        RC_DYN_RAW_PARTS_METADATA_CEILING
    );
    assert!(
        result.3.len() <= RC_DYN_RAW_PARTS_METADATA_CEILING,
        "{label} inferable decl count {} exceeds current-head ceiling {}: {:?}",
        result.3.len(),
        RC_DYN_RAW_PARTS_METADATA_CEILING,
        result.3
    );
}

#[test]
fn test_check_rc_dyn_raw_parts_full_shape_classification() {
    let source = normalize_rc_dyn_source(RC_DYN_SOURCE);
    // sat: rc_dyn encoding currently has CTREX (4/4 harnesses), tracked by #4014
    assert_rc_dyn_raw_parts_classification(
        &source,
        "check_rc_dyn_raw_parts",
        "sat",
        "check_rc_dyn_raw_parts full-shape",
    );
}

#[test]
fn test_check_rc_dyn_raw_parts_forget_tail_classification() {
    let source = rc_dyn_raw_parts_forget_tail_source();
    // sat: rc_dyn encoding currently has CTREX (4/4 harnesses), tracked by #4014
    assert_rc_dyn_raw_parts_classification(
        &source,
        "check_rc_dyn_raw_parts",
        "sat",
        "check_rc_dyn_raw_parts forget-tail",
    );
}

#[test]
fn test_check_rc_dyn_diff_raw_parts_full_shape_classification() {
    let source = normalize_rc_dyn_source(RC_DYN_SOURCE);
    // sat: rc_dyn encoding currently has CTREX (4/4 harnesses), tracked by #4014
    assert_rc_dyn_raw_parts_classification(
        &source,
        "check_rc_dyn_diff_raw_parts",
        "sat",
        "check_rc_dyn_diff_raw_parts full-shape",
    );
}

#[test]
fn test_check_rc_dyn_diff_raw_parts_forget_tail_classification() {
    let source = rc_dyn_diff_raw_parts_forget_tail_source();
    // sat: rc_dyn encoding currently has CTREX (4/4 harnesses), tracked by #4014
    assert_rc_dyn_raw_parts_classification(
        &source,
        "check_rc_dyn_diff_raw_parts",
        "sat",
        "check_rc_dyn_diff_raw_parts forget-tail",
    );
}

#[test]
fn test_check_rc_dyn_raw_parts_metadata_stays_within_current_ceiling() {
    let source = normalize_rc_dyn_source(RC_DYN_SOURCE);
    for (fn_name, label) in [
        ("check_rc_dyn_raw_parts", "check_rc_dyn_raw_parts full-shape"),
        ("check_rc_dyn_diff_raw_parts", "check_rc_dyn_diff_raw_parts full-shape"),
    ] {
        assert_rc_dyn_raw_parts_metadata_ceiling(&source, fn_name, label);
    }
}
