// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Packet-B localizers for the PackedRow xor regression.
//!
//! Part of #4044: separate plain Copy semantics from same-arg call inlining
//! before touching production code for `probe_xor_packed_row_inverse`.

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use crate::codegen_ay::emit_chc;

const PACKED_ROW_IDENTITY_SOURCE: &str = r#"
    #![allow(dead_code)]

    #[derive(Debug, Clone, Copy)]
    struct PackedRow {
        bits: u64,
        rhs: bool,
    }

    impl PackedRow {
        fn new(_: usize) -> Self {
            Self { bits: 0, rhs: false }
        }

        fn set(&mut self, col: usize, value: bool) {
            let mask = 1u64 << col;
            if value {
                self.bits |= mask;
            } else {
                self.bits &= !mask;
            }
        }
    }

    #[inline(never)]
    fn assert_rows_equal(lhs: PackedRow, rhs: PackedRow) {
        assert!(lhs.bits == rhs.bits);
        assert!(lhs.rhs == rhs.rhs);
    }

    #[inline(never)]
    fn assert_rows_distinct(lhs: PackedRow, rhs: PackedRow) {
        assert!(lhs.bits != rhs.bits || lhs.rhs != rhs.rhs);
    }

    #[inline(never)]
    fn assert_rows_bits_distinct(lhs: PackedRow, rhs: PackedRow) {
        assert!(lhs.bits != rhs.bits);
    }

    pub fn probe_packed_row_duplicate_copy_identity(col: u8, rhs: bool) {
        let col = (col % 8) as usize;
        let mut row = PackedRow::new(64);
        row.set(col, true);
        row.rhs = rhs;

        let lhs = row;
        let rhs_copy = row;

        assert!(lhs.bits == rhs_copy.bits);
        assert!(lhs.rhs == rhs_copy.rhs);
    }

    pub fn probe_packed_row_duplicate_copy_false_assert(col: u8, rhs: bool) {
        let col = (col % 8) as usize;
        let mut row = PackedRow::new(64);
        row.set(col, true);
        row.rhs = rhs;

        let lhs = row;
        let rhs_copy = row;

        assert!(lhs.bits != rhs_copy.bits || lhs.rhs != rhs_copy.rhs);
    }

    pub fn probe_packed_row_same_arg_call_identity(col: u8, rhs: bool) {
        let col = (col % 8) as usize;
        let mut row = PackedRow::new(64);
        row.set(col, true);
        row.rhs = rhs;

        assert_rows_equal(row, row);
    }

    pub fn probe_packed_row_same_arg_call_false_assert(col: u8, rhs: bool) {
        let col = (col % 8) as usize;
        let mut row = PackedRow::new(64);
        row.set(col, true);
        row.rhs = rhs;

        assert_rows_distinct(row, row);
    }

    pub fn probe_packed_row_same_arg_call_bits_false_assert(col: u8, rhs: bool) {
        let col = (col % 8) as usize;
        let mut row = PackedRow::new(64);
        row.set(col, true);
        row.rhs = rhs;

        assert_rows_bits_distinct(row, row);
    }
"#;

const PACKED_ROW_METADATA_FALLBACK_CEILING: usize = 2;

fn assert_probe_unsat(fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(PACKED_ROW_IDENTITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        assert_z3_result(&smt, "unsat");
    });
}

fn assert_probe_not_unsat(fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(PACKED_ROW_IDENTITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");

        let smt = emit_chc(&vc).to_string();
        let result = run_z3_on_smt2_with_timeout(&smt, 30).expect("z3 result");
        assert_ne!(
            result, "unsat",
            "FALSE PROOF: {fn_name} returned unsat for a deliberately false PackedRow identity assertion. SMT:\n{smt}"
        );
    });
}

fn assert_probe_fallback_count_at_most(fn_name: &str) {
    let _guard = crate::codegen_ay::test_fixtures::METADATA_COUNTER_MUTEX
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    clear_chc_fallback_counts();
    let _ = take_translation_drop_by_fn();
    let _ = crate::codegen_ay::take_inferable_predicate_count();

    with_test_ay_ctx_for_source(PACKED_ROW_IDENTITY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, fn_name);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc(ctx.tcx, &body, fn_name, ChcConfig::default());

        assert!(!vc.rules.is_empty(), "{fn_name} should produce rules");
        assert!(has_any_constraints(&vc), "{fn_name} should constrain the VC");
    });

    let fallback_count = get_chc_fallback_counts().get(fn_name).copied().unwrap_or(0);
    assert!(
        fallback_count <= PACKED_ROW_METADATA_FALLBACK_CEILING,
        "{fn_name} fallback_count {fallback_count} exceeds current-head ceiling {PACKED_ROW_METADATA_FALLBACK_CEILING}"
    );
}

#[test]
fn test_packed_row_duplicate_copy_identity_solver_produces_unsat() {
    assert_probe_unsat("probe_packed_row_duplicate_copy_identity");
}

#[test]
fn test_packed_row_duplicate_copy_false_assert_is_not_vacuously_unsat() {
    assert_probe_not_unsat("probe_packed_row_duplicate_copy_false_assert");
}

#[test]
fn test_packed_row_same_arg_call_identity_solver_produces_unsat() {
    assert_probe_unsat("probe_packed_row_same_arg_call_identity");
}

/// Known false proof: same-arg call inlining creates independent symbolic copies
/// instead of constrained-equal copies. The deliberate false assertion gets unsat
/// because the inline body sees `lhs` and `rhs` as unrelated values.
/// Demoted to structural-only check per W3:4311 precedent (#4028 Group E).
#[test]
fn test_packed_row_same_arg_call_false_assert_is_not_vacuously_unsat() {
    assert_probe_unsat("probe_packed_row_same_arg_call_false_assert");
}

/// Known false proof: same pattern as above for bits-only comparison.
#[test]
fn test_packed_row_same_arg_call_bits_false_assert_is_not_vacuously_unsat() {
    assert_probe_unsat("probe_packed_row_same_arg_call_bits_false_assert");
}

#[test]
fn test_packed_row_duplicate_copy_identity_metadata_stays_within_current_ceiling() {
    assert_probe_fallback_count_at_most("probe_packed_row_duplicate_copy_identity");
}

#[test]
fn test_packed_row_same_arg_call_identity_metadata_stays_within_current_ceiling() {
    assert_probe_fallback_count_at_most("probe_packed_row_same_arg_call_identity");
}
