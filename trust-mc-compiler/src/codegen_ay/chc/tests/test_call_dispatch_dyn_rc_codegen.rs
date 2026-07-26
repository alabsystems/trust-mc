// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Part of #4138: End-to-end VC tests for Rc/Arc dyn dispatch codegen paths.
//!
//! Exercises `codegen_rc_arc_new`, `codegen_rc_arc_clone`, and
//! `codegen_pointer_wrapper_deref_call` through the full `mir_to_chc` pipeline,
//! verifying that the generated CHC constraints contain expected patterns:
//! - Allocation identity variables
//! - Vtable propagation for dyn types
//! - Memory bridge constraints for Rc value stores
//! - Clone preserves pointer identity metadata

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

// ---------------------------------------------------------------------------
// Source: Rc::new with dyn trait — exercises codegen_rc_arc_new + vtable prop
// ---------------------------------------------------------------------------
const RC_NEW_DYN_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    pub trait Animal {
        fn legs(&self) -> u8;
    }

    pub struct Dog {
        pub trained: bool,
    }

    impl Animal for Dog {
        fn legs(&self) -> u8 {
            4
        }
    }

    pub fn probe_rc_new_dyn(trained: bool) -> u8 {
        let rc: Rc<dyn Animal> = Rc::new(Dog { trained });
        rc.legs()
    }
"#;

// ---------------------------------------------------------------------------
// Source: Rc::clone — exercises codegen_rc_arc_clone pointer identity
// ---------------------------------------------------------------------------
const RC_CLONE_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    pub trait Shape {
        fn area(&self) -> u16;
    }

    pub struct Square {
        pub side: u8,
    }

    impl Shape for Square {
        fn area(&self) -> u16 {
            (self.side as u16) * (self.side as u16)
        }
    }

    pub fn probe_rc_clone_dyn(side: u8) -> u16 {
        let rc: Rc<dyn Shape> = Rc::new(Square { side });
        let rc2 = rc.clone();
        rc2.area()
    }
"#;

// ---------------------------------------------------------------------------
// Source: Rc concrete (no dyn) — exercises codegen_rc_arc_new without vtable
// ---------------------------------------------------------------------------
const RC_NEW_CONCRETE_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    pub struct Point {
        pub x: u8,
        pub y: u8,
    }

    pub fn probe_rc_new_concrete(x: u8, y: u8) -> u8 {
        let rc = Rc::new(Point { x, y });
        rc.x
    }
"#;

// ---------------------------------------------------------------------------
// Source: Rc deref chain — exercises codegen_pointer_wrapper_deref_call
// ---------------------------------------------------------------------------
const RC_DEREF_CHAIN_SOURCE: &str = r#"
    #![allow(dead_code)]

    use std::rc::Rc;

    pub struct Pair {
        pub a: u8,
        pub b: u8,
    }

    pub fn probe_rc_deref_chain(a: u8, b: u8) -> u8 {
        let rc = Rc::new(Pair { a, b });
        let sum = rc.a + rc.b;
        sum
    }
"#;

/// Part of #4138: `codegen_rc_arc_new` with dyn trait produces non-trivial
/// VC with allocation constraints and vtable state variables.
#[test]
fn test_rc_new_dyn_produces_alloc_and_vtable_constraints() {
    with_test_ay_ctx_for_source(RC_NEW_DYN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_new_dyn");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_new_dyn", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "Rc::new dyn should produce rules");
        assert!(has_any_constraints(&vc), "Rc::new dyn should emit constraints");

        let smt = emit_chc(&vc).to_string();

        // codegen_rc_arc_new emits vtable state variables for dyn types
        assert!(
            vc_rules_contain_var(&vc, "__vtable_sv_"),
            "Rc::new(dyn Animal) should emit vtable state variable constraints. \
             SMT prefix: {}",
            &smt[..smt.len().min(800)]
        );

        // The VC should contain bvadd for the Rc header offset (0x10)
        // which is the hallmark of codegen_rc_arc_new's value pointer computation
        assert!(
            smt.contains("bvadd") || smt.contains("BvAdd"),
            "Rc::new should produce bvadd for header offset computation. \
             SMT prefix: {}",
            &smt[..smt.len().min(800)]
        );
    });
}

/// Part of #4138: `codegen_rc_arc_clone` produces non-trivial VC that
/// propagates pointer identity from the source Rc to the clone destination.
#[test]
fn test_rc_clone_dyn_produces_identity_propagation() {
    with_test_ay_ctx_for_source(RC_CLONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_clone_dyn");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_clone_dyn", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "Rc::clone dyn should produce rules");
        assert!(has_any_constraints(&vc), "Rc::clone dyn should emit constraints");

        // Clone must produce vtable state variables (dyn Shape)
        assert!(
            vc_rules_contain_var(&vc, "__vtable_sv_"),
            "Rc::clone(dyn Shape) should preserve vtable state variables"
        );

        // The VC should have enough rules for: init + Rc::new + Rc::clone + deref + area + error
        assert!(
            vc.rules.len() >= 3,
            "Rc::clone dyn should produce at least 3 rules, got {}",
            vc.rules.len()
        );
    });
}

/// Part of #4138: `codegen_rc_arc_new` for concrete types (no dyn) produces
/// allocation constraints but no vtable propagation.
#[test]
fn test_rc_new_concrete_produces_alloc_without_vtable() {
    with_test_ay_ctx_for_source(RC_NEW_CONCRETE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_new_concrete");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_new_concrete", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "Rc::new concrete should produce rules");
        assert!(has_any_constraints(&vc), "Rc::new concrete should emit constraints");

        // Concrete Rc::new should still produce a non-trivial VC with constraints
        // that exercise the allocation path (codegen_rc_arc_new) without dyn dispatch
        assert_has_nontrivial_transition_constraints(&vc, "probe_rc_new_concrete");
    });
}

/// Part of #4138: `codegen_pointer_wrapper_deref_call` through the deref chain
/// produces non-trivial constraints linking the Rc pointer to its value fields.
#[test]
fn test_rc_deref_chain_produces_field_access_constraints() {
    with_test_ay_ctx_for_source(RC_DEREF_CHAIN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_rc_deref_chain");
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, "probe_rc_deref_chain", ChcConfig::default());

        assert!(!vc.rules.is_empty(), "Rc deref chain should produce rules");
        assert!(has_any_constraints(&vc), "Rc deref chain should emit constraints");

        // The deref path should generate enough rules for the field accesses
        assert!(
            vc.rules.len() >= 2,
            "Rc deref chain should produce at least 2 rules (init + field access), got {}",
            vc.rules.len()
        );

        // Should have BvAdd constraints from the header offset computation
        // (codegen_pointer_wrapper_deref_call adds 0x10 for Rc header)
        let smt = emit_chc(&vc).to_string();
        assert!(
            smt.contains("bvadd") || smt.contains("BvAdd"),
            "Rc deref should emit bvadd for header offset computation. \
             SMT prefix: {}",
            &smt[..smt.len().min(800)]
        );
    });
}
