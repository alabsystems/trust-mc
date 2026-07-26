// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for all collection dispatch functions in `codegen_call_collections.rs`
//! through the full CHC pipeline (`mir_to_chc`). Covers:
//! - `codegen_call_vec_core` — Vec new/push/pop/len/clear/clone/capacity
//! - `codegen_call_string_core` — String new/push/push_str/len/clear/clone/eq/from
//! - `codegen_call_hashmap` — HashMap new/insert/get/remove/len/contains_key/is_empty
//! - `codegen_call_vec_iter` — Vec into_iter/next
//! - `codegen_call_hashmap_iter` — HashMap into_iter/next
//! - `codegen_call_iterator_intrinsic` — checked_add_unsigned
//!
//! Tests exercise the dispatch path:
//!   mir_to_chc → generate_transition_rules → codegen_call → detect_*_stub → codegen_call_*
//!
//! Part of #2213 (codegen_call_collections.rs coverage gap).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::super::chc_call_context::ChcCallContext;
use super::super::codegen_call_collections::CallCollections;
use super::common::*;

// =============================================================================
// Vec core operations through mir_to_chc
// =============================================================================

const VEC_NEW_PUSH_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::vec::Vec;

    pub fn probe_vec_new_push() {
        let mut v: Vec<u32> = Vec::new();
        v.push(42);
    }
"#;

#[test]
fn test_vec_new_generates_vc_with_rules() {
    with_test_ay_ctx_for_source(VEC_NEW_PUSH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_new_push");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_new_push", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_new_push", body.blocks.len());

        // Vec new+push should produce transition rules for call dispatch
        assert!(
            vc.rules.len() >= 2,
            "Vec new+push should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_new_push");

        // Semantic: at least one rule should contain an Eq constraint (state assignment)
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_new_push",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_new_push_detects_stubs() {
    with_test_ay_ctx_for_source(VEC_NEW_PUSH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_new_push");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_new_push", ChcConfig::default());

        let mut found_new = false;
        let mut found_push = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                match stub {
                    StubKind::VecNew | StubKind::VecWithCapacity => found_new = true,
                    StubKind::VecPush => found_push = true,
                    _ => {} // internal enum: StubKind (test scan)
                }
            }
        }
        assert!(found_new, "Should detect Vec::new() stub");
        assert!(found_push, "Should detect Vec::push() stub");
    });
}

const VEC_POP_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::vec::Vec;

    pub fn probe_vec_pop() -> Option<u32> {
        let mut v: Vec<u32> = Vec::new();
        v.push(1);
        v.pop()
    }
"#;

#[test]
fn test_vec_pop_generates_vc() {
    with_test_ay_ctx_for_source(VEC_POP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_pop");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_pop", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_pop", body.blocks.len());

        // Vec pop returns Option<u32> — Bool sort for discriminant should be present
        assert_relation_has_arg_sort(&vc, "probe_vec_pop", ay_bindings::Sort::is_bool, "Bool");

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_pop");

        // Semantic: pop should produce Eq constraints linking option discriminant/payload
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_pop",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_pop_detects_stub() {
    with_test_ay_ctx_for_source(VEC_POP_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_pop");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_pop", ChcConfig::default());

        let mut found_pop = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::VecPop) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                found_pop = true;
            }
        }
        assert!(found_pop, "Should detect Vec::pop() stub");
    });
}

const VEC_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::vec::Vec;

    pub fn probe_vec_len() -> usize {
        let mut v: Vec<u32> = Vec::new();
        v.push(1);
        v.push(2);
        v.len()
    }
"#;

#[test]
fn test_vec_len_generates_vc() {
    with_test_ay_ctx_for_source(VEC_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_len", body.blocks.len());

        // Vec::len pipeline with new+push+push+len should produce multiple rules
        assert!(
            vc.rules.len() >= 2,
            "Vec len pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_len");

        // Semantic: len result should be constrained via Eq
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_len",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_len_detects_stub() {
    with_test_ay_ctx_for_source(VEC_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_len", ChcConfig::default());

        let mut found_len = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::VecLen) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                found_len = true;
            }
        }
        assert!(found_len, "Should detect Vec::len() stub");
    });
}

const VEC_CLEAR_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::vec::Vec;

    pub fn probe_vec_clear() {
        let mut v: Vec<u32> = Vec::new();
        v.push(10);
        v.clear();
    }
"#;

#[test]
fn test_vec_clear_generates_vc() {
    with_test_ay_ctx_for_source(VEC_CLEAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clear");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clear", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_clear", body.blocks.len());

        // Vec clear pipeline should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "Vec clear pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_clear");

        // Semantic: clear resets len to 0 — Eq constraint for state update
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_clear",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_clear_detects_stub() {
    with_test_ay_ctx_for_source(VEC_CLEAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clear");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_clear", ChcConfig::default());

        let mut found_clear = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::VecClear) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                found_clear = true;
            }
        }
        assert!(found_clear, "Should detect Vec::clear() stub");
    });
}

const VEC_CLONE_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::vec::Vec;

    pub fn probe_vec_clone() -> Vec<u32> {
        let v: Vec<u32> = Vec::new();
        v.clone()
    }
"#;

#[test]
fn test_vec_clone_generates_vc() {
    with_test_ay_ctx_for_source(VEC_CLONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_clone");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_clone", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_clone", body.blocks.len());
        // Vec clone pipeline should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "Vec clone pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_clone");

        // Semantic: clone produces Eq constraints to copy collection state
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_clone",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

const VEC_CAPACITY_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::vec::Vec;

    pub fn probe_vec_capacity() -> usize {
        let v: Vec<u32> = Vec::with_capacity(10);
        v.capacity()
    }
"#;

#[test]
fn test_vec_with_capacity_generates_vc() {
    with_test_ay_ctx_for_source(VEC_CAPACITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_capacity");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_capacity", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_capacity", body.blocks.len());
        // Vec with_capacity+capacity should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "Vec capacity pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_capacity");

        // Semantic: Eq constraints for state transfer
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_capacity",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_with_capacity_detects_stubs() {
    with_test_ay_ctx_for_source(VEC_CAPACITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_capacity");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_capacity", ChcConfig::default());

        let mut found_with_capacity = false;
        let mut found_capacity = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                match stub {
                    StubKind::VecWithCapacity => found_with_capacity = true,
                    StubKind::VecCapacity => found_capacity = true,
                    _ => {} // internal enum: StubKind (test scan)
                }
            }
        }
        assert!(found_with_capacity, "Should detect Vec::with_capacity() stub");
        assert!(found_capacity, "Should detect Vec::capacity() stub");
    });
}

// =============================================================================
// String core operations through mir_to_chc
// =============================================================================

const STRING_NEW_PUSH_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_new_push() {
        let mut s = String::new();
        s.push('a');
    }
"#;

#[test]
fn test_string_new_generates_vc() {
    with_test_ay_ctx_for_source(STRING_NEW_PUSH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_new_push");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_new_push", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_new_push", body.blocks.len());
        // String new+push should produce transition rules for call dispatch
        assert!(
            vc.rules.len() >= 2,
            "String new+push should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_new_push");

        // Semantic: String push(char) — Eq constraints for state update
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_new_push",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_string_new_push_detects_stubs() {
    with_test_ay_ctx_for_source(STRING_NEW_PUSH_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_new_push");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_new_push", ChcConfig::default());

        let mut found_new = false;
        let mut found_push = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                match stub {
                    StubKind::StringNew => found_new = true,
                    StubKind::StringPush => found_push = true,
                    _ => {} // internal enum: StubKind (test scan)
                }
            }
        }
        assert!(found_new, "Should detect String::new() stub");
        assert!(found_push, "Should detect String::push() stub");
    });
}

const STRING_LEN_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_len() -> usize {
        let mut s = String::new();
        s.push('x');
        s.len()
    }
"#;

#[test]
fn test_string_len_generates_vc() {
    with_test_ay_ctx_for_source(STRING_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_len");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_len", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_len", body.blocks.len());
        // String new+push+len should produce multiple rules
        assert!(
            vc.rules.len() >= 2,
            "String len pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_len");

        // Semantic: Eq constraint for len result binding
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_len",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_string_len_detects_stub() {
    with_test_ay_ctx_for_source(STRING_LEN_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_len");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_len", ChcConfig::default());

        let mut found_len = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::StringLen) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                found_len = true;
            }
        }
        assert!(found_len, "Should detect String::len() stub");
    });
}

const STRING_CLEAR_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_clear() {
        let mut s = String::new();
        s.push('x');
        s.clear();
    }
"#;

#[test]
fn test_string_clear_generates_vc() {
    with_test_ay_ctx_for_source(STRING_CLEAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_clear");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_clear", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_clear", body.blocks.len());
        // String clear pipeline should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "String clear pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_clear");

        // Semantic: clear resets state — Eq constraints for state update
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_clear",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_string_clear_detects_stub() {
    with_test_ay_ctx_for_source(STRING_CLEAR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_clear");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_clear", ChcConfig::default());

        let mut found_clear = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::StringClear) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                found_clear = true;
            }
        }
        assert!(found_clear, "Should detect String::clear() stub");
    });
}

const STRING_CLONE_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_clone() -> String {
        let s = String::new();
        s.clone()
    }
"#;

#[test]
fn test_string_clone_generates_vc() {
    with_test_ay_ctx_for_source(STRING_CLONE_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_clone");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_clone", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_clone", body.blocks.len());
        // String clone pipeline should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "String clone pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_clone");

        // Semantic: clone copies collection state — Eq constraints
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_clone",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

const STRING_EQ_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_eq(a: &String, b: &String) -> bool {
        a == b
    }
"#;

#[test]
fn test_string_eq_generates_vc() {
    with_test_ay_ctx_for_source(STRING_EQ_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_eq");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_eq", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_eq", body.blocks.len());
        // String eq returns bool — Bool sort should be present
        assert_relation_has_arg_sort(&vc, "probe_string_eq", ay_bindings::Sort::is_bool, "Bool");

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_eq");

        // Semantic: string equality should produce an Eq constraint for the comparison result
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_eq",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

const STRING_PUSH_STR_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_push_str() {
        let mut s = String::new();
        s.push_str("hello");
    }
"#;

#[test]
fn test_string_push_str_generates_vc() {
    with_test_ay_ctx_for_source(STRING_PUSH_STR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_push_str");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_push_str", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_push_str", body.blocks.len());
        // String push_str pipeline should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "String push_str pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_push_str");

        // Semantic: push_str updates collection state — Eq constraints
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_push_str",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_string_push_str_detects_stub() {
    with_test_ay_ctx_for_source(STRING_PUSH_STR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_push_str");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_push_str", ChcConfig::default());

        let mut found_push_str = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::StringPushStr) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                found_push_str = true;
            }
        }
        assert!(found_push_str, "Should detect String::push_str() stub");
    });
}

const STRING_FROM_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_from(flag: bool) -> String {
        if flag { String::from("hello") } else { String::from("") }
    }
"#;

#[test]
fn test_string_from_generates_vc() {
    with_test_ay_ctx_for_source(STRING_FROM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_from");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_from", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_from", body.blocks.len());
        // String::from pipeline should produce transition rules
        assert!(
            !vc.rules.is_empty(),
            "String::from should produce at least 1 rule, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_from");

        // Semantic: branching probe generates SwitchInt guard via Not constraint.
        // This verifies the VC carries branch-condition encoding, not String::from-
        // specific semantics. The String::from stub assigns a symbolic dest without
        // producing Eq/Store in rule constraints — its effect is in the state-variable
        // sort declarations, validated by assert_vc_structure above.
        // See #2910 for analysis of what this assertion actually verifies.
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_from",
            |e| matches!(e.value(), ExprValue::Not(_)),
            "Not (SwitchInt branch guard)",
        );
    });
}

#[test]
fn test_string_from_detects_stub() {
    with_test_ay_ctx_for_source(STRING_FROM_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_from");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_from", ChcConfig::default());

        let mut found_from = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::StringFrom) =
                    chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                found_from = true;
            }
        }
        assert!(found_from, "Should detect String::from() stub");
    });
}

// =============================================================================
// HashMap operations through mir_to_chc (exercises codegen_call_hashmap)
// =============================================================================

const HASHMAP_INSERT_GET_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_insert_get() -> Option<u32> {
        let mut map: HashMap<u32, u32> = HashMap::new();
        let key1 = 1u32;
        let key2 = 2u32;
        let value1 = 100u32;
        let value2 = 200u32;
        map.insert(key1, value1);
        map.insert(key2, value2);
        map.get(&key1).copied()
    }
"#;

#[test]
fn test_hashmap_insert_get_generates_vc() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_hashmap_collection_metadata();
    with_test_ay_ctx_for_source(HASHMAP_INSERT_GET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert_get");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_insert_get", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashmap_insert_get", body.blocks.len());
        // HashMap insert+get pipeline should produce multiple rules
        assert!(
            vc.rules.len() >= 3,
            "HashMap insert+get pipeline should produce at least 3 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_hashmap_insert_get");

        // Semantic: HashMap insert uses Store (array update) for map model
        assert_rule_contains_expr_kind(
            &vc,
            "probe_hashmap_insert_get",
            |e| matches!(e.value(), ExprValue::Store { .. }),
            "Store (array update for HashMap insert)",
        );
    });
    assert_no_hashmap_collection_drop_metadata("probe_hashmap_insert_get");
}

#[test]
fn test_hashmap_insert_get_detects_stubs() {
    with_test_ay_ctx_for_source(HASHMAP_INSERT_GET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert_get");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_insert_get", ChcConfig::default());

        let mut found_new = false;
        let mut found_insert = false;
        let mut found_get = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_hashmap_stub(func, args)
            {
                match stub {
                    StubKind::HashMapNew => found_new = true,
                    StubKind::HashMapInsert => found_insert = true,
                    StubKind::HashMapGet => found_get = true,
                    _ => {} // internal enum: StubKind (test scan)
                }
            }
        }
        assert!(found_new, "Should detect HashMap::new() stub");
        assert!(found_insert, "Should detect HashMap::insert() stub");
        assert!(found_get, "Should detect HashMap::get() stub");
    });
}

fn find_hashmap_insert_call(
    chc_ctx: &ChcCtx<'_, '_>,
    body: &rustc_public::mir::Body,
) -> (usize, Vec<Operand>, Place, rustc_public::mir::BasicBlockIdx) {
    for (bb_idx, block) in body.blocks.iter().enumerate() {
        if let rustc_public::mir::TerminatorKind::Call {
            func,
            args,
            destination,
            target: Some(target),
            ..
        } = &block.terminator.kind
            && chc_ctx.detect_hashmap_stub(func, args) == Some(StubKind::HashMapInsert)
        {
            return (bb_idx, args.clone(), destination.clone(), *target);
        }
    }
    unreachable!("expected HashMapInsert call terminator");
}

fn build_collection_from_app(chc_ctx: &ChcCtx<'_, '_>, bb_idx: usize) -> RelationApp {
    let from_rel =
        chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
    let output_args: Vec<_> = chc_ctx
        .state_var_mgr
        .state_vars
        .iter()
        .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
        .collect();
    RelationApp::new(&from_rel, output_args)
}

#[test]
fn test_hashmap_insert_untracked_destination_still_emits_collection_update_rule() {
    with_test_ay_ctx_for_source(HASHMAP_INSERT_GET_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert_get");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_insert_get", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let (bb_idx, args, destination, target) = find_hashmap_insert_call(&chc_ctx, &body);
        let from_app = build_collection_from_app(&chc_ctx, bb_idx);
        let stmt_constraints = [Expr::bool_const(true)];
        let modified_locals = HashSet::new();

        let collection_local = chc_ctx
            .resolve_collection_local(&args)
            .expect("HashMapInsert should resolve self local");
        let collection_vec_idx = chc_ctx.state_idx_for_local(collection_local);
        let collection_out_name =
            chc_ctx.state_var_mgr.output_state_vars[collection_vec_idx].0.clone();

        let removed = chc_ctx.state_var_mgr.local_to_state_idx.remove(&destination.local);
        assert!(
            removed.is_some(),
            "test setup requires tracked destination local {}",
            destination.local
        );

        let before_rules = chc_ctx.vc.rules.len();
        let before_sound = chc_ctx.sound_fallback_count();
        let cx = ChcCallContext {
            stub: StubKind::HashMapInsert,
            args: &args,
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &modified_locals,
        };
        chc_ctx.codegen_call_hashmap(&cx);

        assert_eq!(
            chc_ctx.vc.rules.len(),
            before_rules + 1,
            "untracked destination should still emit one successor rule"
        );
        assert!(
            chc_ctx.sound_fallback_count() > before_sound,
            "untracked destination should increment sound_fallback_count"
        );

        let rule = chc_ctx.vc.rules.last().expect("HashMapInsert should emit one rule");
        assert_ne!(rule.head.name, "error", "untracked destination must not fail closed");

        let collection_head_arg = rule
            .head
            .args
            .get(collection_vec_idx)
            .expect("collection slot should exist in rule head");
        assert!(
            matches!(collection_head_arg.value(), ExprValue::Var { name } if name == &*collection_out_name),
            "collection slot should route through output var {collection_out_name}, got {:?}",
            collection_head_arg.value()
        );
    });
}

fn reset_hashmap_collection_metadata() {
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();
}

fn assert_no_hashmap_collection_drop_metadata(fn_name: &str) {
    let _translation_drops = take_translation_drop_by_fn();
    let drop_fallback_reasons = crate::codegen_ay::take_drop_fallback_reasons_by_fn();
    let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
    // Drain global counters to prevent cross-test contamination, but only
    // assert on per-fn maps — global counters are racy under parallel test
    // execution and produce nondeterministic failures (#3960).
    let _ = crate::codegen_ay::take_place_translation_drop_count();
    let _ = crate::codegen_ay::take_constant_translation_drop_count();
    let _ = crate::codegen_ay::take_unsupported_field_projection_count();

    // Per-fn maps are also racy under parallel test execution: concurrent
    // tests share the global per-fn HashMap and `take_*_by_fn()` drains ALL
    // entries. Only check this fn's entries if the map contains them.
    // The `state_idx_missing_collections_dest` fallback is a known-benign
    // sound over-approximation from the try_state_idx migration (#3768).
    let fn_sites = translation_sites.get(fn_name);
    let non_benign_sites: usize = fn_sites
        .map(|sites| {
            sites
                .iter()
                .filter(|(reason, _)| *reason != "state_idx_missing_collections_dest")
                .map(|(_, count)| count)
                .sum()
        })
        .unwrap_or(0);
    assert_eq!(
        non_benign_sites, 0,
        "{fn_name} should not record non-benign translation-drop site reasons, map={translation_sites:?}"
    );
    assert!(
        !drop_fallback_reasons.contains_key(fn_name),
        "{fn_name} should not record categorized sound-fallback reasons, map={drop_fallback_reasons:?}"
    );
}

const HASHMAP_CONTAINS_AFTER_INSERT_MEM_ASSERT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]
    use std::collections::HashMap;

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            panic!("model-only marker function")
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(_cond: bool) {}
    }

    pub fn probe_hashmap_contains_after_insert_mem_assert() {
        let mut map: HashMap<u32, u32> = HashMap::new();
        let k: u32 = kani::any();
        let v: u32 = kani::any();

        assert!(!map.contains_key(&k));
        map.insert(k, v);
        assert!(map.contains_key(&k));
    }
"#;

#[test]
fn test_hashmap_contains_after_insert_mem_assert_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_hashmap_collection_metadata();

    with_test_ay_ctx_for_source(HASHMAP_CONTAINS_AFTER_INSERT_MEM_ASSERT_SOURCE, |ctx| {
        let fn_name = "probe_hashmap_contains_after_insert_mem_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(
            ctx.tcx,
            &body,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(
            vc.rules.len() >= 4,
            "{fn_name} should produce a nontrivial HashMap assert pipeline at Mem track, got {} rules",
            vc.rules.len()
        );
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        let error_rules: Vec<_> =
            vc.rules.iter().filter(|rule| &*rule.head.name == "error").collect();
        assert!(
            !error_rules.is_empty(),
            "{fn_name} should emit error rules for the assert! cleanup edges"
        );
    });

    assert_no_hashmap_collection_drop_metadata("probe_hashmap_contains_after_insert_mem_assert");
}

#[test]
fn test_hashmap_contains_after_insert_mem_assert_with_instance_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_hashmap_collection_metadata();

    with_test_ay_ctx_for_source(HASHMAP_CONTAINS_AFTER_INSERT_MEM_ASSERT_SOURCE, |ctx| {
        let fn_name = "probe_hashmap_contains_after_insert_mem_assert";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_with_instance(
            ctx.tcx,
            &body,
            instance,
            fn_name,
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(
            vc.rules.len() >= 4,
            "{fn_name} should produce a nontrivial HashMap assert pipeline at Mem track with current instance, got {} rules",
            vc.rules.len()
        );
        assert_has_nontrivial_transition_constraints(&vc, fn_name);

        let error_rules: Vec<_> =
            vc.rules.iter().filter(|rule| &*rule.head.name == "error").collect();
        assert!(
            !error_rules.is_empty(),
            "{fn_name} should emit error rules for the assert! cleanup edges"
        );
    });

    assert_no_hashmap_collection_drop_metadata("probe_hashmap_contains_after_insert_mem_assert");
}

const HASHMAP_LEN_CONTAINS_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_len_contains() -> bool {
        let mut map: HashMap<u32, u32> = HashMap::new();
        let key = 5u32;
        let value = 50u32;
        map.insert(key, value);
        let _ = map.len();
        map.contains_key(&key)
    }
"#;

#[test]
fn test_hashmap_len_contains_generates_vc() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_hashmap_collection_metadata();
    with_test_ay_ctx_for_source(HASHMAP_LEN_CONTAINS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_len_contains");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_len_contains", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashmap_len_contains", body.blocks.len());

        // HashMap with multiple ops should produce rules with constraints
        assert!(
            vc.rules.len() >= 4,
            "HashMap len+contains pipeline should produce at least 4 rules, got {}",
            vc.rules.len()
        );

        assert_has_nontrivial_transition_constraints(&vc, "probe_hashmap_len_contains");
        assert_relation_has_arg_sort(
            &vc,
            "probe_hashmap_len_contains",
            ay_bindings::Sort::is_bool,
            "Bool",
        );
        assert_rule_contains_expr_kind(
            &vc,
            "probe_hashmap_len_contains",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
    assert_no_hashmap_collection_drop_metadata("probe_hashmap_len_contains");
}

const HASHMAP_REMOVE_IS_EMPTY_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_remove_is_empty() -> bool {
        let mut map: HashMap<u32, u32> = HashMap::new();
        let key = 1u32;
        let value = 10u32;
        map.insert(key, value);
        let _ = map.remove(&key);
        map.is_empty()
    }
"#;

#[test]
fn test_hashmap_remove_is_empty_generates_vc() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_hashmap_collection_metadata();
    with_test_ay_ctx_for_source(HASHMAP_REMOVE_IS_EMPTY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_remove_is_empty");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_remove_is_empty", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashmap_remove_is_empty", body.blocks.len());
        // HashMap remove+is_empty pipeline should produce multiple rules
        assert!(
            vc.rules.len() >= 3,
            "HashMap remove+is_empty pipeline should produce at least 3 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_hashmap_remove_is_empty");

        // Semantic: is_empty returns bool — Bool sort in relations
        assert_relation_has_arg_sort(
            &vc,
            "probe_hashmap_remove_is_empty",
            ay_bindings::Sort::is_bool,
            "Bool",
        );

        // Semantic: Eq constraints for state updates and result bindings
        assert_rule_contains_expr_kind(
            &vc,
            "probe_hashmap_remove_is_empty",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
    assert_no_hashmap_collection_drop_metadata("probe_hashmap_remove_is_empty");
}

const HASHMAP_PHASE5_PACKET_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_phase5_packet() -> bool {
        let mut map: HashMap<u32, u32> = HashMap::new();
        let key1 = 1u32;
        let key2 = 2u32;
        let missing = 3u32;
        let value1 = 10u32;
        let value2 = 20u32;
        map.insert(key1, value1);
        map.insert(key2, value2);
        let a = map.contains_key(&key1);
        let b = map.contains_key(&missing);
        let _ = map.remove(&key1);
        let c = map.is_empty();
        map.clear();
        let d = map.is_empty();
        a && !b && !c && d
    }
"#;

#[test]
fn test_hashmap_phase5_packet_has_clean_metadata() {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    reset_hashmap_collection_metadata();

    with_test_ay_ctx_for_source(HASHMAP_PHASE5_PACKET_SOURCE, |ctx| {
        let fn_name = "probe_hashmap_phase5_packet";
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert_vc_structure(&vc, fn_name, body.blocks.len());
        assert!(
            vc.rules.len() >= 6,
            "{fn_name} should produce a nontrivial HashMap phase-5 pipeline, got {} rules",
            vc.rules.len()
        );
        assert_has_nontrivial_transition_constraints(&vc, fn_name);
        assert_relation_has_arg_sort(&vc, fn_name, ay_bindings::Sort::is_bool, "Bool");
        assert_rule_contains_expr_kind(
            &vc,
            fn_name,
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });

    assert_no_hashmap_collection_drop_metadata("probe_hashmap_phase5_packet");
}

// =============================================================================
// Vec iterator operations through mir_to_chc (exercises codegen_call_vec_iter)
// =============================================================================

const VEC_INTO_ITER_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_vec_into_iter_pipeline() {
        let v: Vec<u32> = Vec::new();
        let mut iter = v.into_iter();
        let _ = iter.next();
    }
"#;

#[test]
fn test_vec_into_iter_pipeline_generates_vc() {
    with_test_ay_ctx_for_source(VEC_INTO_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_into_iter_pipeline");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_into_iter_pipeline", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_into_iter_pipeline", body.blocks.len());
        // Vec into_iter+next should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "Vec into_iter pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_into_iter_pipeline");

        // Semantic: iterator next returns Option — Bool sort for discriminant
        assert_relation_has_arg_sort(
            &vc,
            "probe_vec_into_iter_pipeline",
            ay_bindings::Sort::is_bool,
            "Bool",
        );

        // Semantic: Eq constraints for iterator state management
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_into_iter_pipeline",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_into_iter_detects_stubs() {
    with_test_ay_ctx_for_source(VEC_INTO_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_into_iter_pipeline");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_vec_into_iter_pipeline", ChcConfig::default());

        let mut found_into_iter = false;
        let mut found_next = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_vec_iter_stub(func)
            {
                match stub {
                    StubKind::VecIntoIter => found_into_iter = true,
                    StubKind::IntoIterNext => found_next = true,
                    _ => {} // internal enum: StubKind (test scan)
                }
            }
        }
        assert!(found_into_iter, "Should detect Vec::into_iter() stub");
        assert!(found_next, "Should detect Iterator::next() stub");
    });
}

// =============================================================================
// HashMap iterator operations through mir_to_chc (exercises codegen_call_hashmap_iter)
// =============================================================================

const HASHMAP_ITER_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_iter_pipeline() {
        let mut map: HashMap<u8, u16> = HashMap::new();
        map.insert(1, 10);
        let mut iter = map.into_iter();
        let _ = iter.next();
    }
"#;

#[test]
fn test_hashmap_iter_pipeline_generates_vc() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter_pipeline");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_iter_pipeline", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashmap_iter_pipeline", body.blocks.len());
        // HashMap into_iter+next should produce transition rules
        assert!(
            vc.rules.len() >= 2,
            "HashMap iter pipeline should produce at least 2 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_hashmap_iter_pipeline");

        // Semantic: Eq constraints for iterator state and element bindings
        assert_rule_contains_expr_kind(
            &vc,
            "probe_hashmap_iter_pipeline",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_hashmap_iter_pipeline_detects_stubs() {
    with_test_ay_ctx_for_source(HASHMAP_ITER_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_iter_pipeline");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_iter_pipeline", ChcConfig::default());

        let mut found_into_iter = false;
        let mut found_next = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_hashmap_iter_stub(func)
            {
                match stub {
                    StubKind::HashMapIntoIter => found_into_iter = true,
                    StubKind::HashMapIterNext => found_next = true,
                    _ => {} // internal enum: StubKind (test scan)
                }
            }
        }
        assert!(found_into_iter, "Should detect HashMap::into_iter() stub");
        assert!(found_next, "Should detect HashMap iter next() stub");
    });
}

// =============================================================================
// Iterator intrinsic operations through mir_to_chc
// (exercises codegen_call_iterator_intrinsic)
// Iterator intrinsics include checked_add_unsigned and option_unwrap_unchecked
// which are used by the standard library's iterator machinery.
// =============================================================================

const ITER_INTRINSIC_CHECKED_ADD_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn probe_checked_add_unsigned(a: i32) -> Option<i32> {
        a.checked_add_unsigned(1)
    }
"#;

#[test]
fn test_checked_add_unsigned_generates_vc() {
    with_test_ay_ctx_for_source(ITER_INTRINSIC_CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_unsigned");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add_unsigned", ChcConfig::default());

        assert_vc_structure(&vc, "probe_checked_add_unsigned", body.blocks.len());
        // checked_add_unsigned returns Option<i32> — Bool sort should be present
        assert_relation_has_arg_sort(
            &vc,
            "probe_checked_add_unsigned",
            ay_bindings::Sort::is_bool,
            "Bool",
        );

        // checked_add_unsigned operates on i32 — bv32 sort should be present
        assert_relation_has_arg_sort(
            &vc,
            "probe_checked_add_unsigned",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_checked_add_unsigned");

        // Semantic: checked_add should produce a BvAdd constraint for the addition
        assert_rule_contains_expr_kind(
            &vc,
            "probe_checked_add_unsigned",
            |e| matches!(e.value(), ExprValue::BvAdd(_, _)),
            "BvAdd (checked addition arithmetic)",
        );
    });
}

#[test]
fn test_checked_add_unsigned_flattened_option_constrains_payload_field() {
    with_test_ay_ctx_for_source(ITER_INTRINSIC_CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_unsigned");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_checked_add_unsigned", ChcConfig::default());

        let mut has_discriminant_true = false;
        let mut has_payload_bvadd = false;
        for rule in &vc.rules {
            for constraint in &rule.body.constraints {
                let c = constraint.to_string();
                if c.contains("_fld0") && c.contains("true") {
                    has_discriminant_true = true;
                }
                if c.contains("_fld1") && c.contains("bvadd") {
                    has_payload_bvadd = true;
                }
            }
        }

        assert!(
            has_discriminant_true,
            "checked_add_unsigned should constrain flattened Option discriminant to true"
        );
        assert!(
            has_payload_bvadd,
            "checked_add_unsigned should constrain flattened Option payload (_fld1) to bvadd result"
        );
    });
}

#[test]
fn test_checked_add_unsigned_detects_intrinsic_stub() {
    with_test_ay_ctx_for_source(ITER_INTRINSIC_CHECKED_ADD_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_unsigned");
        let body = instance.body().expect("function body");

        let chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_checked_add_unsigned", ChcConfig::default());

        let mut found = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(StubKind::CheckedAddUnsigned) =
                    chc_ctx.detect_iterator_intrinsic_stub(func)
            {
                found = true;
            }
        }
        assert!(found, "Should detect checked_add_unsigned() intrinsic stub");
    });
}

// =============================================================================
// Combined multi-collection operations (HashMap + iteration)
// =============================================================================

const HASHMAP_MULTI_OPS_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::HashMap;

    pub fn probe_hashmap_multi_ops() -> usize {
        let mut map: HashMap<u32, u32> = HashMap::new();
        map.insert(1, 10);
        map.insert(2, 20);
        map.insert(3, 30);
        let _ = map.remove(&2);
        map.len()
    }
"#;

#[test]
fn test_hashmap_multi_ops_generates_vc() {
    with_test_ay_ctx_for_source(HASHMAP_MULTI_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_multi_ops");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_hashmap_multi_ops", ChcConfig::default());

        assert_vc_structure(&vc, "probe_hashmap_multi_ops", body.blocks.len());

        // new + 3*insert + remove + len = many rules
        assert!(
            vc.rules.len() >= 6,
            "Multi-op HashMap should produce at least 6 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_hashmap_multi_ops");

        // Semantic: HashMap insert uses Store (array update) for map model
        assert_rule_contains_expr_kind(
            &vc,
            "probe_hashmap_multi_ops",
            |e| matches!(e.value(), ExprValue::Store { .. }),
            "Store (array update for HashMap insert)",
        );

        // Semantic: Eq constraints for state updates across multiple operations
        assert_rule_contains_expr_kind(
            &vc,
            "probe_hashmap_multi_ops",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_hashmap_multi_ops_detects_all_stubs() {
    with_test_ay_ctx_for_source(HASHMAP_MULTI_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_multi_ops");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_hashmap_multi_ops", ChcConfig::default());

        let mut stubs = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_hashmap_stub(func, args)
            {
                stubs.push(stub);
            }
        }

        let new_count = stubs.iter().filter(|s| matches!(s, StubKind::HashMapNew)).count();
        let insert_count = stubs.iter().filter(|s| matches!(s, StubKind::HashMapInsert)).count();
        let remove_count = stubs.iter().filter(|s| matches!(s, StubKind::HashMapRemove)).count();
        let len_count = stubs.iter().filter(|s| matches!(s, StubKind::HashMapLen)).count();

        assert!(new_count >= 1, "Should detect HashMap::new(), found {new_count}");
        assert!(insert_count >= 3, "Should detect 3 HashMap::insert(), found {insert_count}");
        assert!(remove_count >= 1, "Should detect HashMap::remove(), found {remove_count}");
        assert!(len_count >= 1, "Should detect HashMap::len(), found {len_count}");
    });
}

// =============================================================================
// Combined Vec operations (exercising multi-stub dispatch in sequence)
// =============================================================================

const VEC_MULTI_OPS_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::vec::Vec;

    pub fn probe_vec_multi_ops() -> usize {
        let mut v: Vec<u32> = Vec::new();
        v.push(1);
        v.push(2);
        v.push(3);
        let _ = v.pop();
        v.len()
    }
"#;

#[test]
fn test_vec_multi_ops_generates_vc() {
    with_test_ay_ctx_for_source(VEC_MULTI_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_multi_ops");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_vec_multi_ops", ChcConfig::default());

        assert_vc_structure(&vc, "probe_vec_multi_ops", body.blocks.len());

        // With new+3*push+pop+len, there should be many rules for all the call dispatch
        assert!(
            vc.rules.len() >= 6,
            "Multi-op Vec should produce at least 6 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_vec_multi_ops");

        // Semantic: Vec operations on u32 elements require BV32 relation arguments
        assert_relation_has_arg_sort(
            &vc,
            "probe_vec_multi_ops",
            |s| s.bitvec_width() == Some(32),
            "bv32",
        );

        // Semantic: Eq constraints for state updates across push/pop/len
        assert_rule_contains_expr_kind(
            &vc,
            "probe_vec_multi_ops",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_vec_multi_ops_detects_all_stubs() {
    with_test_ay_ctx_for_source(VEC_MULTI_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_vec_multi_ops");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_vec_multi_ops", ChcConfig::default());

        let mut stubs = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_vec_core)
            {
                stubs.push(stub);
            }
        }

        // Should find at least: new, push (x3), pop, len
        let new_count = stubs
            .iter()
            .filter(|s| matches!(s, StubKind::VecNew | StubKind::VecWithCapacity))
            .count();
        let push_count = stubs.iter().filter(|s| matches!(s, StubKind::VecPush)).count();
        let pop_count = stubs.iter().filter(|s| matches!(s, StubKind::VecPop)).count();
        let len_count = stubs.iter().filter(|s| matches!(s, StubKind::VecLen)).count();

        assert!(new_count >= 1, "Should detect Vec::new(), found {new_count}");
        assert!(push_count >= 3, "Should detect 3 Vec::push(), found {push_count}");
        assert!(pop_count >= 1, "Should detect Vec::pop(), found {pop_count}");
        assert!(len_count >= 1, "Should detect Vec::len(), found {len_count}");
    });
}

// =============================================================================
// Combined String operations
// =============================================================================

const STRING_MULTI_OPS_SOURCE: &str = r#"
    #![allow(dead_code)]
    extern crate alloc;
    use alloc::string::String;

    pub fn probe_string_multi_ops() -> usize {
        let mut s = String::new();
        s.push('a');
        s.push('b');
        s.push_str("cd");
        s.len()
    }
"#;

#[test]
fn test_string_multi_ops_generates_vc() {
    with_test_ay_ctx_for_source(STRING_MULTI_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_multi_ops");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc(ctx.tcx, &body, "probe_string_multi_ops", ChcConfig::default());

        assert_vc_structure(&vc, "probe_string_multi_ops", body.blocks.len());

        // With new+2*push+push_str+len, expect many rules
        assert!(
            vc.rules.len() >= 5,
            "Multi-op String should produce at least 5 rules, got {}",
            vc.rules.len()
        );

        // Semantic: transition rules must carry non-trivial constraints
        assert_has_nontrivial_transition_constraints(&vc, "probe_string_multi_ops");

        // Semantic: Eq constraints for state updates across push/push_str/len
        assert_rule_contains_expr_kind(
            &vc,
            "probe_string_multi_ops",
            |e| matches!(e.value(), ExprValue::Eq(_, _)),
            "Eq",
        );
    });
}

#[test]
fn test_string_multi_ops_detects_all_stubs() {
    with_test_ay_ctx_for_source(STRING_MULTI_OPS_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_string_multi_ops");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_string_multi_ops", ChcConfig::default());

        let mut stubs = Vec::new();
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, .. } = &block.terminator.kind
                && let Some(stub) = chc_ctx.detect_stub_matching(func, StubKind::is_string_core)
            {
                stubs.push(stub);
            }
        }

        let new_count = stubs.iter().filter(|s| matches!(s, StubKind::StringNew)).count();
        let push_count = stubs.iter().filter(|s| matches!(s, StubKind::StringPush)).count();
        let push_str_count = stubs.iter().filter(|s| matches!(s, StubKind::StringPushStr)).count();
        let len_count = stubs.iter().filter(|s| matches!(s, StubKind::StringLen)).count();

        assert!(new_count >= 1, "Should detect String::new(), found {new_count}");
        assert!(push_count >= 2, "Should detect 2 String::push(), found {push_count}");
        assert!(push_str_count >= 1, "Should detect String::push_str(), found {push_str_count}");
        assert!(len_count >= 1, "Should detect String::len(), found {len_count}");
    });
}

// =============================================================================
// Fail-closed caller behavior on translation None (Part of #2497 Batch 0)
// =============================================================================

const COLLECTIONS_CALLER_FAIL_CLOSED_SOURCE: &str = r#"
    #![allow(dead_code)]
    use std::collections::{BTreeSet, HashMap, HashSet};

    pub fn probe_hashmap_insert_fail_closed() {
        let mut m: HashMap<u32, u32> = HashMap::new();
        let _ = m.insert(1, 2);
    }

    pub fn probe_btreeset_insert_fail_closed() {
        let mut s: BTreeSet<u32> = BTreeSet::new();
        let _ = s.insert(1);
    }

    pub fn probe_hashset_insert_fail_closed() {
        let mut s: HashSet<u32> = HashSet::new();
        let _ = s.insert(1);
    }

    pub fn probe_checked_add_unsigned_fail_closed(a: i32) -> Option<i32> {
        a.checked_add_unsigned(1)
    }
"#;

#[test]
fn test_hashmap_call_translation_none_emits_error_rule() {
    with_test_ay_ctx_for_source(COLLECTIONS_CALLER_FAIL_CLOSED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashmap_insert_fail_closed");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashmap_insert_fail_closed", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_hashmap_stub(func, args) == Some(StubKind::HashMapInsert)
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) =
            call_site.expect("expected HashMapInsert call terminator");
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashMapInsert,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_hashmap(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        let rule = chc_ctx.vc.rules.last().expect("hashmap call should emit one rule");
        assert_eq!(rule.head.name, "error", "fallback should emit fail-closed error rule");
        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "fallback error rule should preserve statement constraints"
        );
    });
}

#[test]
fn test_btreeset_call_translation_none_emits_error_rule() {
    with_test_ay_ctx_for_source(COLLECTIONS_CALLER_FAIL_CLOSED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_btreeset_insert_fail_closed");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_btreeset_insert_fail_closed", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_btreeset)
                    == Some(StubKind::BTreeSetInsert)
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) =
            call_site.expect("expected BTreeSetInsert call terminator");
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::BTreeSetInsert,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_btreeset(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        let rule = chc_ctx.vc.rules.last().expect("btreeset call should emit one rule");
        assert_eq!(rule.head.name, "error", "fallback should emit fail-closed error rule");
        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "fallback error rule should preserve statement constraints"
        );
    });
}

#[test]
fn test_hashset_call_translation_none_emits_error_rule() {
    with_test_ay_ctx_for_source(COLLECTIONS_CALLER_FAIL_CLOSED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_hashset_insert_fail_closed");
        let body = instance.body().expect("function body");
        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_hashset_insert_fail_closed", ChcConfig::default());
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_stub_matching(func, StubKind::is_hashset)
                    == Some(StubKind::HashSetInsert)
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) =
            call_site.expect("expected HashSetInsert call terminator");
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::HashSetInsert,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_hashset(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        let rule = chc_ctx.vc.rules.last().expect("hashset call should emit one rule");
        assert_eq!(rule.head.name, "error", "fallback should emit fail-closed error rule");
        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "fallback error rule should preserve statement constraints"
        );
    });
}

#[test]
fn test_iterator_intrinsic_translation_none_emits_error_rule() {
    with_test_ay_ctx_for_source(COLLECTIONS_CALLER_FAIL_CLOSED_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_checked_add_unsigned_fail_closed");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "probe_checked_add_unsigned_fail_closed",
            ChcConfig::default(),
        );
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();

        let mut call_site = None;
        for (bb_idx, block) in body.blocks.iter().enumerate() {
            if let rustc_public::mir::TerminatorKind::Call {
                func,
                destination,
                target: Some(target),
                ..
            } = &block.terminator.kind
                && chc_ctx.detect_iterator_intrinsic_stub(func)
                    == Some(StubKind::CheckedAddUnsigned)
            {
                call_site = Some((bb_idx, destination.clone(), *target));
                break;
            }
        }

        let (bb_idx, destination, target) =
            call_site.expect("expected CheckedAddUnsigned call terminator");
        let from_rel =
            chc_ctx.block_relations.get(&bb_idx).expect("source relation for call block").clone();
        let output_args: Vec<_> = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .map(|(name, sort)| Expr::var(name.to_string(), sort.clone()))
            .collect();
        let from_app = RelationApp::new(&from_rel, output_args);
        let stmt_constraints = [Expr::bool_const(true)];

        let before_rules = chc_ctx.vc.rules.len();
        let cx = ChcCallContext {
            stub: StubKind::CheckedAddUnsigned,
            args: &[],
            destination: &destination,
            target,
            from_app: &from_app,
            stmt_constraints: &stmt_constraints,
            modified_locals: &HashSet::new(),
        };
        chc_ctx.codegen_call_iterator_intrinsic(&cx);

        assert_eq!(chc_ctx.vc.rules.len(), before_rules + 1, "expected one fallback rule");
        let rule = chc_ctx.vc.rules.last().expect("iterator intrinsic call should emit one rule");
        assert_eq!(rule.head.name, "error", "fallback should emit fail-closed error rule");
        assert_eq!(
            rule.body.constraints.len(),
            stmt_constraints.len(),
            "fallback error rule should preserve statement constraints"
        );
    });
}
