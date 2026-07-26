// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for SMT logic classification (Linear, NIA, NRA, DtBvArrays).

use super::super::classifier::{SmtLogicClass, classify_smt_logic};
use super::super::nonlinear::{content_has_arrays, content_has_bitvectors, content_has_datatypes};
use std::io::Write;
use tempfile::NamedTempFile;

// Tests for NIA logic classification

#[test]
fn test_classify_smt_logic_linear() {
    // Linear integer arithmetic: x + y, x * 5 (constant multiplication)
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x Int)\n\
                   (declare-const y Int)\n\
                   (assert (= (+ x y) 10))\n\
                   (assert (= (* x 5) 25))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "x + y and x * 5 are linear"
    );
}

#[test]
fn test_classify_smt_logic_nia_multiplication() {
    // Non-linear: x * y where both are Int variables
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x Int)\n\
                   (declare-const y Int)\n\
                   (assert (= (* x y) 100))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Nia,
        "x * y with Int variables is NIA"
    );
}

#[test]
fn test_classify_smt_logic_nia_squaring() {
    // Non-linear: x * x (squaring)
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x Int)\n\
                   (assert (= (* x x) 100))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Nia,
        "x * x (squaring) is NIA"
    );
}

#[test]
fn test_classify_smt_logic_nia_division() {
    // Non-linear: x / y where y is a variable
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x Int)\n\
                   (declare-const y Int)\n\
                   (assert (= (/ x y) 5))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Nia,
        "x / y with variable divisor is NIA"
    );
}

#[test]
fn test_classify_smt_logic_division_by_constant() {
    // Linear: x / 5 (division by constant)
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x Int)\n\
                   (assert (= (/ x 5) 10))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "x / 5 (constant divisor) is linear"
    );
}

#[test]
fn test_classify_smt_logic_nra_multiplication() {
    // Non-linear real: x * y where both are Real variables
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x Real)\n\
                   (declare-const y Real)\n\
                   (assert (= (* x y) 100.0))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Nra,
        "x * y with Real variables is NRA"
    );
}

// ========== DT+BV/Arrays detection tests ==========

#[test]
fn test_content_has_bitvectors_sort() {
    let content = "(declare-const x (_ BitVec 32))\n(check-sat)\n";
    assert!(content_has_bitvectors(content), "Should detect BitVec sort");
}

#[test]
fn test_content_has_bitvectors_operations() {
    let content = "(declare-const x (_ BitVec 32))\n(assert (= (bvadd x #x00000001) #x00000002))\n";
    assert!(content_has_bitvectors(content), "Should detect bvadd");

    let content2 = "(assert (bvslt a b))\n";
    assert!(content_has_bitvectors(content2), "Should detect bvslt");
}

#[test]
fn test_content_has_bitvectors_false() {
    let content = "(declare-const x Int)\n(assert (= x 5))\n";
    assert!(!content_has_bitvectors(content), "Should not detect BV in Int-only");
}

#[test]
fn test_content_has_arrays_sort() {
    let content = "(declare-const arr (Array Int Int))\n(check-sat)\n";
    assert!(content_has_arrays(content), "Should detect Array sort");
}

#[test]
fn test_content_has_arrays_operations() {
    let content = "(assert (= (select arr 0) 5))\n";
    assert!(content_has_arrays(content), "Should detect select");

    let content2 = "(assert (= arr2 (store arr 0 5)))\n";
    assert!(content_has_arrays(content2), "Should detect store");
}

#[test]
fn test_content_has_arrays_false() {
    let content = "(declare-const x Int)\n(assert (= x 5))\n";
    assert!(!content_has_arrays(content), "Should not detect Arrays in Int-only");
}

#[test]
fn test_content_has_datatypes() {
    let content1 = "(declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n";
    assert!(content_has_datatypes(content1), "Should detect declare-datatype");

    let content2 =
        "(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T))))))))\n";
    assert!(content_has_datatypes(content2), "Should detect declare-datatypes");
}

#[test]
fn test_classify_smt_logic_dt_plus_bv() {
    // Datatypes + BV triggers DtBvArrays
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::DtBvArrays,
        "DT + BV should be classified as DtBvArrays"
    );
}

#[test]
fn test_classify_smt_logic_dt_plus_arrays() {
    // Datatypes + Arrays triggers DtBvArrays
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n\
                   (declare-const arr (Array Int Int))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::DtBvArrays,
        "DT + Arrays should be classified as DtBvArrays"
    );
}

#[test]
fn test_classify_smt_logic_dt_only() {
    // Datatypes alone are fine (no BV/Arrays)
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n\
                   (declare-const x Int)\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "DT alone (no BV/Arrays) should be Linear"
    );
}

#[test]
fn test_classify_smt_logic_bv_only() {
    // BV alone without DT is fine
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-const x (_ BitVec 32))\n\
                   (assert (= (bvadd x #x00000001) #x00000002))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "BV alone (no DT) should be Linear"
    );
}

// Part of #2851: BV-only DT classification tests

#[test]
fn test_classify_smt_logic_bv_only_dt_plus_bv_not_demoted() {
    // Range<u32> is a DT with only BV fields — should NOT trigger demotion.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Range_u32 ((Range_u32_mk (fld_start (_ BitVec 32)) (fld_end (_ BitVec 32)))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (assert (bvult x #x00000010))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "BV-only DT (Range<u32>) + BV should NOT trigger DtBvArrays demotion (#2851)"
    );
}

#[test]
fn test_classify_smt_logic_bool_field_dt_not_demoted() {
    // DT with Bool field alongside BV — decidable, should not demote.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype OptionLike ((OptionLike_mk (is_some Bool) (value (_ BitVec 32)))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "DT with Bool+BV fields should NOT trigger DtBvArrays demotion"
    );
}

#[test]
fn test_classify_smt_logic_nullary_ctor_dt_not_demoted() {
    // Enum with nullary constructors (no fields) + BV field — should not demote.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Option_i32 ((None) (Some (value (_ BitVec 32)))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "DT with nullary ctor + BV field should NOT trigger demotion"
    );
}

#[test]
fn test_classify_smt_logic_multiline_bv_only_dt_plus_bv_not_demoted() {
    // Multiline Range<u32> declaration should still be treated as BV-only.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Range_u32\n\
                     ((Range_u32_mk\n\
                       (fld_start (_ BitVec 32))\n\
                       (fld_end (_ BitVec 32)))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "Multiline BV-only DT + BV should NOT trigger DtBvArrays demotion"
    );
}

#[test]
fn test_classify_smt_logic_multiline_int_dt_still_demoted() {
    // Multiline complex DT declaration (Int fields) + BV should still demote.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Pair\n\
                     ((mk-pair\n\
                       (fst Int)\n\
                       (snd Int))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::DtBvArrays,
        "Multiline Int-field DT + BV should still trigger DtBvArrays demotion"
    );
}

#[test]
fn test_classify_smt_logic_int_field_dt_still_demoted() {
    // DT with Int fields + BV — should still demote (Int+DT is the problematic combo).
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::DtBvArrays,
        "DT with Int fields + BV should STILL trigger DtBvArrays demotion"
    );
}

#[test]
fn test_classify_smt_logic_nested_bv_only_dt_not_demoted() {
    // DT referencing another DT whose all leaf fields are BV — decidable,
    // should NOT demote. This is the nested tuple case: ((u32, bool), u8)
    // produces Tuple_bv32_bool (all BV/Bool) and Tuple_Tuple_bv32_bool_bv8
    // (field referencing Tuple_bv32_bool). Since Inner's fields are all
    // decidable, Outer's reference to Inner is transitively decidable.
    // Part of #2979: fixpoint decidability for nested DTs.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Inner ((Inner_mk (val (_ BitVec 32)))))\n\
                   (declare-datatype Outer ((Outer_mk (inner Inner))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "DT with nested BV-only DT field + BV should NOT trigger DtBvArrays demotion"
    );
}

#[test]
fn test_classify_smt_logic_nested_int_dt_still_demoted() {
    // DT referencing another DT with Int fields — should still demote.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Inner ((Inner_mk (val Int))))\n\
                   (declare-datatype Outer ((Outer_mk (inner Inner))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::DtBvArrays,
        "DT with nested Int-field DT + BV should trigger DtBvArrays demotion"
    );
}

#[test]
fn test_classify_smt_logic_nested_tuple_three_level_not_demoted() {
    // Exact pattern from ((u32, bool), u8): three DT declarations where
    // the outermost references the middle, which has BV+Bool fields.
    // All leaf sorts are decidable, so none should trigger demotion.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Tuple_bv32_bool ((Tuple_bv32_bool_mk (fld_0 (_ BitVec 32)) (fld_1 Bool))))\n\
                   (declare-datatype Tuple_Tuple_bv32_bool_bv8 ((Tuple_Tuple_bv32_bool_bv8_mk (fld_0 Tuple_bv32_bool) (fld_1 (_ BitVec 8)))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (assert (bvult x #x00000010))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "Nested tuple ((u32, bool), u8) DTs with all-BV/Bool leaves should NOT trigger demotion"
    );
}

#[test]
fn test_classify_smt_logic_mixed_bv_and_int_dt_demoted() {
    // One BV-only DT + one Int-field DT — the Int-field DT triggers demotion.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Range_u32 ((Range_u32_mk (fld_start (_ BitVec 32)) (fld_end (_ BitVec 32)))))\n\
                   (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::DtBvArrays,
        "Mixed BV-only + Int-field DTs should trigger demotion (Int DT is complex)"
    );
}

#[test]
fn test_classify_smt_logic_vec_dt_not_demoted() {
    // Vec<i32> DT with Array(BV64, BV32) data field + BV should NOT demote.
    let mut input = NamedTempFile::new().unwrap();
    let content = "(declare-datatype Vec_bv32 ((Vec_bv32_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 32))))))\n\
                   (declare-const x (_ BitVec 32))\n\
                   (assert (bvult x #x00000010))\n\
                   (check-sat)\n";
    input.write_all(content.as_bytes()).unwrap();

    assert_eq!(
        classify_smt_logic(input.path()).unwrap(),
        SmtLogicClass::Linear,
        "Vec DT with Array(BV, BV) field + BV should NOT trigger DtBvArrays demotion (#2876)"
    );
}
