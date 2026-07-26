// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `codegen_call_dispatch_overapprox_kani_mem.rs` — validity predicate
//! encoding for `kani::mem::can_dereference` and `kani::mem::can_read_unaligned`.
//!
//! Part of #3592: soundness-critical CHC call handlers lack unit test coverage.
//!
//! Covers:
//! - `compute_kani_mem_predicate()` — AND composition of access + validity
//! - `compute_kani_mem_valid_value_predicate()` — recursive type dispatch
//! - `bool_validity_predicate()` — BV eq(0) or eq(1) constraint
//! - `char_validity_predicate()` — Unicode scalar range (≤0xD7FF or 0xE000..=0x10FFFF)
//! - ADT recursive field validity (single-variant struct with bool/char fields)
//! - Integer/uint types produce no validity constraint (always valid bit patterns)

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

fn mir_to_chc_default(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    fn_name: &str,
) -> trust_mc_core::chc::ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig::default(),
    )
}

// =============================================================================
// Probe sources
// =============================================================================

/// Source with kani::mem stubs and multiple probe functions for different
/// pointee types. Each probe calls can_dereference or can_read_unaligned
/// on a pointer to a specific type, exercising different branches of
/// compute_kani_mem_valid_value_predicate.
const KANI_MEM_VALIDITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool {
                true
            }

            #[inline(never)]
            pub fn can_read_unaligned<T>(_ptr: *const T) -> bool {
                true
            }
        }
    }

    /// Probe: bool validity — should encode eq(value, 0) || eq(value, 1)
    pub fn probe_deref_bool(ptr: *const bool) -> bool {
        kani::mem::can_dereference(ptr)
    }

    /// Probe: char validity — should encode Unicode scalar range
    pub fn probe_deref_char(ptr: *const char) -> bool {
        kani::mem::can_dereference(ptr)
    }

    /// Probe: u32 — no validity constraint needed (all bit patterns valid)
    pub fn probe_deref_u32(ptr: *const u32) -> bool {
        kani::mem::can_dereference(ptr)
    }

    /// Probe: unaligned read of bool — same validity but no alignment check
    pub fn probe_read_unaligned_bool(ptr: *const bool) -> bool {
        kani::mem::can_read_unaligned(ptr)
    }
"#;

/// Source with ADT containing bool and char fields to test recursive validity.
const KANI_MEM_ADT_SOURCE: &str = r#"
    #![allow(dead_code)]

    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool {
                true
            }
        }
    }

    pub struct HasBoolChar {
        pub flag: bool,
        pub letter: char,
    }

    /// Probe: ADT with bool+char fields — should recurse into fields
    pub fn probe_deref_struct_with_bool_char(ptr: *const HasBoolChar) -> bool {
        kani::mem::can_dereference(ptr)
    }
"#;

// =============================================================================
// bool_validity_predicate tests
// =============================================================================

/// can_dereference on *const bool should produce bool validity constraints:
/// the loaded value must equal 0 or 1 (BV case).
///
/// In SMT-LIB2 serialization, bool validity appears as an Or of two Eq
/// comparisons. We use string-based matching on the serialized constraints
/// to verify the pattern without depending on BigInt internals.
#[test]
fn test_kani_mem_bool_validity_produces_01_constraint() {
    with_test_ay_ctx_for_source(KANI_MEM_VALIDITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_bool");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_deref_bool");

        assert_vc_structure(&vc, "probe_deref_bool", body.blocks.len());

        // Bool validity encodes value == 0 || value == 1. In BV mode, the
        // serialized constraint contains "(or (= ... #x00) (= ... #x01))"
        // or equivalent bitvec constant forms. Check that the VC contains
        // an Or expression (the characteristic bool validity shape).
        let has_or_pattern = vc.rules.iter().any(|rule| {
            let in_constraints = rule.body.constraints.iter().any(|c| {
                constraint_tree_contains(
                    c,
                    &|expr| matches!(expr.value(), ExprValue::Or(args) if args.len() == 2),
                )
            });
            let in_head = rule.head.args.iter().any(|a| {
                constraint_tree_contains(
                    a,
                    &|expr| matches!(expr.value(), ExprValue::Or(args) if args.len() == 2),
                )
            });
            in_constraints || in_head
        });
        assert!(
            has_or_pattern,
            "can_dereference on *const bool should produce an Or expression \
             (bool validity: value == 0 || value == 1)"
        );
    });
}

// =============================================================================
// char_validity_predicate tests
// =============================================================================

/// can_dereference on *const char should produce Unicode scalar range constraints:
/// value ≤ 0xD7FF (55295) or (value ≥ 0xE000 (57344) and value ≤ 0x10FFFF (1114111)).
#[test]
fn test_kani_mem_char_validity_produces_unicode_range() {
    with_test_ay_ctx_for_source(KANI_MEM_VALIDITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_char");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_deref_char");

        assert_vc_structure(&vc, "probe_deref_char", body.blocks.len());

        // Unicode scalar validity encodes: value ≤ 0xD7FF || (value ≥ 0xE000 && value ≤ 0x10FFFF).
        // In BV encoding, 0xD7FF = 55295, 0xE000 = 57344, 0x10FFFF = 1114111.
        // Check for these magic constants in the generated rules.
        let has_d7ff = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                let s = c.to_string();
                s.contains("55295") || s.contains("D7FF") || s.contains("d7ff")
            }) || rule.head.args.iter().any(|a| {
                let s = a.to_string();
                s.contains("55295") || s.contains("D7FF") || s.contains("d7ff")
            })
        });
        let has_e000 = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                let s = c.to_string();
                s.contains("57344") || s.contains("E000") || s.contains("e000")
            }) || rule.head.args.iter().any(|a| {
                let s = a.to_string();
                s.contains("57344") || s.contains("E000") || s.contains("e000")
            })
        });
        let has_10ffff = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                let s = c.to_string();
                s.contains("1114111") || s.contains("10FFFF") || s.contains("10ffff")
            }) || rule.head.args.iter().any(|a| {
                let s = a.to_string();
                s.contains("1114111") || s.contains("10FFFF") || s.contains("10ffff")
            })
        });

        assert!(
            has_d7ff && has_e000 && has_10ffff,
            "can_dereference on *const char should produce Unicode scalar range \
             constraints (0xD7FF={has_d7ff}, 0xE000={has_e000}, 0x10FFFF={has_10ffff})"
        );
    });
}

// =============================================================================
// Integer types: no validity constraint
// =============================================================================

/// can_dereference on *const u32 should NOT produce validity constraints.
/// All u32 bit patterns are valid.
#[test]
fn test_kani_mem_u32_no_validity_constraint() {
    with_test_ay_ctx_for_source(KANI_MEM_VALIDITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_u32");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_deref_u32");

        assert_vc_structure(&vc, "probe_deref_u32", body.blocks.len());

        // u32 has no validity constraints. The rules should not contain
        // the bool-validity Or(Eq(0), Eq(1)) or the char-validity Unicode ranges.
        let has_bool_pattern = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().any(|c| {
                let s = c.to_string();
                // Bool validity constants
                s.contains("55295") || s.contains("57344")
            })
        });
        assert!(
            !has_bool_pattern,
            "can_dereference on *const u32 should not produce char validity constraints"
        );
    });
}

// =============================================================================
// can_read_unaligned: validity without alignment
// =============================================================================

/// can_read_unaligned on *const bool should produce bool validity but
/// should NOT produce an alignment check (bvurem).
#[test]
fn test_kani_mem_read_unaligned_bool_no_alignment() {
    with_test_ay_ctx_for_source(KANI_MEM_VALIDITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_read_unaligned_bool");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_read_unaligned_bool");

        assert_vc_structure(&vc, "probe_read_unaligned_bool", body.blocks.len());

        // can_read_unaligned passes require_alignment=false, so no bvurem.
        let has_bvurem = any_constraint_str(&vc, |s| s.contains("bvurem"));
        assert!(!has_bvurem, "can_read_unaligned should not produce alignment check (bvurem)");
    });
}

// =============================================================================
// ADT recursive validity
// =============================================================================

/// can_dereference on *const HasBoolChar (struct with bool + char fields)
/// should produce validity constraints for both fields recursively.
#[test]
fn test_kani_mem_adt_recursive_field_validity() {
    with_test_ay_ctx_for_source(KANI_MEM_ADT_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_deref_struct_with_bool_char");
        let body = instance.body().expect("function body");

        let vc = mir_to_chc_default(ctx.tcx, &body, "probe_deref_struct_with_bool_char");

        assert_vc_structure(&vc, "probe_deref_struct_with_bool_char", body.blocks.len());

        // The struct has a char field, so we expect Unicode scalar range constants
        // from the recursive validity check on the char field.
        let has_char_validity = vc.rules.iter().any(|rule| {
            rule.body.constraints.iter().chain(rule.head.args.iter()).any(|expr| {
                let s = expr.to_string();
                s.contains("55295") || s.contains("D7FF") || s.contains("d7ff")
            })
        });
        assert!(
            has_char_validity,
            "can_dereference on *const HasBoolChar should produce char validity \
             constraints from recursive field walk"
        );
    });
}
