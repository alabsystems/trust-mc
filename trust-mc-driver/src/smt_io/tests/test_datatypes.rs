// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Tests for datatype declaration parsing, decidability analysis, and block collection.

use super::super::datatypes::{
    collect_datatype_decl_blocks, content_has_complex_datatypes, datatype_decl_has_non_bv_fields,
    is_decidable_sort,
};

// Part of #1766 follow-up: arrays whose ELEMENT is a decidable datatype are
// themselves decidable (QF_ADTBV) and must NOT trigger DT+BV demotion. These
// exercise the cross-declaration fixpoint (`content_has_complex_datatypes`),
// not the pure leaf check (`is_decidable_sort`), which intentionally rejects
// bare DT names.

#[test]
fn test_array_of_decidable_dt_element_not_complex() {
    // PbTerm is a decidable record (BV128 + a decidable Vec DT); a Slice whose
    // fld_data is Array(BV64, PbTerm) must be recognized as decidable.
    let content = "\
(declare-datatype Vec_bv40 ((Vec_bv40_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 40))))))
(declare-datatype PbTerm ((PbTerm_mk (fld_coeff (_ BitVec 128)) (fld_lits Vec_bv40))))
(declare-datatype Slice_PbTerm ((Slice_PbTerm_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_data (Array (_ BitVec 64) PbTerm)))))
(check-sat)";
    assert!(
        !content_has_complex_datatypes(content),
        "Array(BV64, <decidable DT>) field should NOT be complex (QF_ADTBV is decidable)"
    );
}

#[test]
fn test_array_of_decidable_dt_element_order_independent() {
    // Same as above but the array-bearing DT is declared BEFORE its element DT,
    // proving the fixpoint resolves the dependency regardless of order.
    let content = "\
(declare-datatype Slice_LiftedItem ((Slice_LiftedItem_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_data (Array (_ BitVec 64) LiftedItem)))))
(declare-datatype PbLit ((PbLit_mk (fld_var (_ BitVec 32)) (fld_negated Bool))))
(declare-datatype LiftedItem ((LiftedItem_mk (fld_lit PbLit) (fld_weight (_ BitVec 128)) (fld_coeff (_ BitVec 128)))))
(check-sat)";
    assert!(
        !content_has_complex_datatypes(content),
        "BV-only DT (LiftedItem) as an array element must be recognized decidable"
    );
}

#[test]
fn test_array_of_int_dt_element_still_complex() {
    // An array whose element DT carries an Int field is genuinely undecidable
    // in combination (ay#1766) and must still be flagged complex.
    let content = "\
(declare-datatype HasInt ((HasInt_mk (x Int))))
(declare-datatype SliceHasInt ((SliceHasInt_mk (fld_data (Array (_ BitVec 64) HasInt)))))
(check-sat)";
    assert!(
        content_has_complex_datatypes(content),
        "Array(BV64, <DT with Int field>) must remain complex"
    );
}

#[test]
fn test_datatype_decl_has_non_bv_fields_bv_only() {
    assert!(
        !datatype_decl_has_non_bv_fields(
            "(declare-datatype Range_u32 ((Range_u32_mk (fld_start (_ BitVec 32)) (fld_end (_ BitVec 32)))))"
        ),
        "Range with BV32 fields should be BV-only"
    );
}

#[test]
fn test_datatype_decl_has_non_bv_fields_bool_field() {
    assert!(
        !datatype_decl_has_non_bv_fields(
            "(declare-datatype OptionLike ((OptionLike_mk (is_some Bool) (value (_ BitVec 32)))))"
        ),
        "Bool + BV fields should be BV-only"
    );
}

#[test]
fn test_datatype_decl_has_non_bv_fields_int_field() {
    assert!(
        datatype_decl_has_non_bv_fields("(declare-datatype Pair ((mk-pair (fst Int) (snd Int))))"),
        "Int fields should NOT be BV-only"
    );
}

#[test]
fn test_datatype_decl_has_non_bv_fields_nullary_ctor() {
    assert!(
        !datatype_decl_has_non_bv_fields(
            "(declare-datatype Option_i32 ((None) (Some (value (_ BitVec 32)))))"
        ),
        "Nullary ctor + BV field should be BV-only"
    );
}

#[test]
fn test_datatype_decl_has_non_bv_fields_nested_dt() {
    assert!(
        datatype_decl_has_non_bv_fields("(declare-datatype Outer ((Outer_mk (inner Inner))))"),
        "Nested DT reference should NOT be BV-only"
    );
}

#[test]
fn test_datatype_decl_has_non_bv_fields_all_nullary() {
    assert!(
        !datatype_decl_has_non_bv_fields("(declare-datatype MyEnum ((A) (B) (C)))"),
        "All-nullary enum should be BV-only (no fields to check)"
    );
}

#[test]
fn test_datatype_decl_has_non_bv_fields_parametric() {
    assert!(
        datatype_decl_has_non_bv_fields(
            "(declare-datatypes ((List 1)) ((par (T) ((nil) (cons (head T) (tail (List T)))))))"
        ),
        "Parametric datatypes should conservatively be treated as non-BV"
    );
}

// Part of #2876: Array(BV,BV) fields in Datatypes are decidable

#[test]
fn test_datatype_decl_array_bv_bv_not_demoted() {
    // Vec_bv32 has fld_data: Array(BV64, BV32) — decidable, should not demote.
    assert!(
        !datatype_decl_has_non_bv_fields(
            "(declare-datatype Vec_bv32 ((Vec_bv32_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_cap (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 32))))))"
        ),
        "Vec DT with Array(BV64, BV32) field should NOT trigger demotion (#2876)"
    );
}

#[test]
fn test_datatype_decl_slice_array_bv_not_demoted() {
    // Slice_bv32 has fld_data: Array(BV64, BV32) — same pattern as Vec.
    assert!(
        !datatype_decl_has_non_bv_fields(
            "(declare-datatype Slice_bv32 ((Slice_bv32_mk (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64)) (fld_data (Array (_ BitVec 64) (_ BitVec 32))))))"
        ),
        "Slice DT with Array(BV64, BV32) field should NOT trigger demotion (#2876)"
    );
}

#[test]
fn test_datatype_decl_array_int_still_demoted() {
    // Array(Int, Int) field should still trigger demotion.
    assert!(
        datatype_decl_has_non_bv_fields(
            "(declare-datatype Container ((Container_mk (data (Array Int Int)))))"
        ),
        "DT with Array(Int, Int) field should trigger demotion"
    );
}

#[test]
fn test_datatype_decl_array_bv_int_still_demoted() {
    // Array(BV64, Int) element sort is Int — should still demote.
    assert!(
        datatype_decl_has_non_bv_fields(
            "(declare-datatype Container ((Container_mk (data (Array (_ BitVec 64) Int)))))"
        ),
        "DT with Array(BV64, Int) field should trigger demotion"
    );
}

#[test]
fn test_is_decidable_sort_basic() {
    assert!(is_decidable_sort("Bool"));
    assert!(is_decidable_sort("(_ BitVec 32)"));
    assert!(is_decidable_sort("(_ BitVec 64)"));
    assert!(!is_decidable_sort("Int"));
    assert!(!is_decidable_sort("Real"));
    assert!(!is_decidable_sort("MyType"));
}

#[test]
fn test_is_decidable_sort_array() {
    assert!(is_decidable_sort("(Array (_ BitVec 64) (_ BitVec 32))"));
    assert!(is_decidable_sort("(Array (_ BitVec 64) Bool)"));
    assert!(!is_decidable_sort("(Array Int Int)"));
    assert!(!is_decidable_sort("(Array (_ BitVec 64) Int)"));
}

#[test]
fn test_collect_datatype_decl_blocks_multiline() {
    let content = "(declare-datatype Range_u32\n\
                     ((Range_u32_mk\n\
                       (fld_start (_ BitVec 32))\n\
                       (fld_end (_ BitVec 32)))))\n\
                   (declare-datatype Pair ((mk-pair (fst Int) (snd Int))))\n\
                   (check-sat)\n";
    let blocks = collect_datatype_decl_blocks(content);
    assert_eq!(blocks.len(), 2, "Should collect two datatype declarations");
    assert!(
        blocks[0].contains("fld_start (_ BitVec 32)"),
        "First block should contain multiline Range fields"
    );
    assert!(blocks[1].starts_with("(declare-datatype Pair "), "Second block should be Pair");
}
