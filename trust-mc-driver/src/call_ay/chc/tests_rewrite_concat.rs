// Copyright 2026 Andrew Yates, Inc.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

use super::rewrite_concat::*;
use ay_frontend::sexp::{SExpr, parse_sexps};
use std::fs;
use std::path::Path;

#[test]
fn test_rewrite_simple_split_pointer_concat() {
    let input = "\
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (= x (concat a b)))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 1);
    assert_eq!(result.rewritten, 1);
    assert_eq!(result.skipped, 0);
    assert!(
        !result.output.contains("concat"),
        "output should not contain concat: {}",
        result.output
    );
    assert!(result.output.contains("bvor"));
    assert!(result.output.contains("bvshl"));
    assert!(result.output.contains("zero_extend"));
}

#[test]
fn test_rewrite_nested_byte_concat_chain() {
    let input = "\
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (= x (concat (concat a b) c)))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 2);
    assert_eq!(result.rewritten, 2);
    assert_eq!(result.skipped, 0);
    assert!(
        !result.output.contains("concat"),
        "output should not contain concat: {}",
        result.output
    );
}

#[test]
fn test_preserves_non_concat_script() {
    let input = "\
(set-logic HORN)
(declare-fun inv ((_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32))) (inv x)))
(check-sat)
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 0);
    assert_eq!(result.rewritten, 0);
    assert_eq!(result.skipped, 0);
    parse_sexps(&result.output).expect("output should be valid S-expression stream");
}

#[test]
fn test_unknown_width_stays_unchanged() {
    let input = "\
(declare-const a (_ BitVec 32))
(assert (= x (concat a unknown_sym)))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 1);
    assert_eq!(result.rewritten, 0);
    assert_eq!(result.skipped, 1);
    assert!(result.output.contains("concat"));
}

#[test]
fn test_rewritten_script_parses_as_sexp() {
    let input = "\
(declare-const a (_ BitVec 16))
(declare-const b (_ BitVec 16))
(assert (= (concat a b) #x00000000))
(check-sat)
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.rewritten, 1);
    let parsed =
        parse_sexps(&result.output).expect("rewritten output should parse as S-expressions");
    assert!(!parsed.is_empty());
}

#[test]
fn test_infer_width_hex_literal() {
    let widths = SortEnv::default();
    let sexp = SExpr::Hexadecimal("#xABCD".to_string());
    assert_eq!(infer_width(&sexp, &widths), Some(16));
}

#[test]
fn test_infer_width_binary_literal() {
    let widths = SortEnv::default();
    let sexp = SExpr::Binary("#b10101010".to_string());
    assert_eq!(infer_width(&sexp, &widths), Some(8));
}

#[test]
fn test_infer_width_bv_literal() {
    let widths = SortEnv::default();
    let sexp = SExpr::List(vec![
        SExpr::Symbol("_".to_string()),
        SExpr::Symbol("bv42".to_string()),
        SExpr::Numeral("64".to_string()),
    ]);
    assert_eq!(infer_width(&sexp, &widths), Some(64));
}

#[test]
fn test_infer_width_declared_symbol() {
    let mut widths = SortEnv::default();
    widths.insert_bv_width("x", 32);
    let sexp = SExpr::Symbol("x".to_string());
    assert_eq!(infer_width(&sexp, &widths), Some(32));
}

#[test]
fn test_infer_width_extract() {
    let widths = SortEnv::default();
    let sexp = SExpr::List(vec![
        SExpr::List(vec![
            SExpr::Symbol("_".to_string()),
            SExpr::Symbol("extract".to_string()),
            SExpr::Numeral("7".to_string()),
            SExpr::Numeral("0".to_string()),
        ]),
        SExpr::Hexadecimal("#xABCD".to_string()),
    ]);
    assert_eq!(infer_width(&sexp, &widths), Some(8));
}

#[test]
fn test_infer_width_select_from_declared_array() {
    let mut widths = SortEnv::default();
    widths.insert_array_value_width("mem", 8);
    let sexp = SExpr::List(vec![
        SExpr::Symbol("select".to_string()),
        SExpr::Symbol("mem".to_string()),
        SExpr::List(vec![
            SExpr::Symbol("_".to_string()),
            SExpr::Symbol("bv0".to_string()),
            SExpr::Numeral("64".to_string()),
        ]),
    ]);
    assert_eq!(infer_width(&sexp, &widths), Some(8));
}

#[test]
fn test_infer_width_select_from_store_keeps_array_value_width() {
    let mut widths = SortEnv::default();
    widths.insert_array_value_width("mem", 8);
    let sexp = SExpr::List(vec![
        SExpr::Symbol("select".to_string()),
        SExpr::List(vec![
            SExpr::Symbol("store".to_string()),
            SExpr::Symbol("mem".to_string()),
            SExpr::List(vec![
                SExpr::Symbol("_".to_string()),
                SExpr::Symbol("bv1".to_string()),
                SExpr::Numeral("64".to_string()),
            ]),
            SExpr::Hexadecimal("#xAB".to_string()),
        ]),
        SExpr::List(vec![
            SExpr::Symbol("_".to_string()),
            SExpr::Symbol("bv2".to_string()),
            SExpr::Numeral("64".to_string()),
        ]),
    ]);
    assert_eq!(infer_width(&sexp, &widths), Some(8));
}

#[test]
fn test_declare_fun_collects_width() {
    let input = "\
(declare-fun my_var () (_ BitVec 64))
(assert (= x (concat my_var my_var)))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.rewritten, 1);
    assert!(!result.output.contains("concat"));
}

#[test]
fn test_declare_var_collects_width() {
    let input = "\
(declare-var a (_ BitVec 32))
(declare-var b (_ BitVec 32))
(assert (= x (concat a b)))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 1);
    assert_eq!(result.rewritten, 1);
    assert_eq!(result.skipped, 0);
    assert!(!result.output.contains("concat"));
    assert!(result.output.contains("bvor"));
}

#[test]
fn test_declare_var_non_bv_ignored() {
    let input = "\
(declare-var flag Bool)
(declare-const a (_ BitVec 32))
(assert (= x (concat a flag)))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 1);
    assert_eq!(result.rewritten, 0);
    assert_eq!(result.skipped, 1);
    assert!(result.output.contains("concat"));
}

#[test]
fn test_datatype_selector_application_collects_width() {
    let input = "\
(declare-datatype Pair ((Pair_mk (hi (_ BitVec 32)) (lo (_ BitVec 32)))))
(declare-const p Pair)
(assert (= x (concat (hi p) (lo p))))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 1);
    assert_eq!(result.rewritten, 1);
    assert_eq!(result.skipped, 0);
    assert!(!result.output.contains("concat"));
}

#[test]
fn test_declare_var_array_select_collects_width() {
    let input = "\
(declare-datatype Range_u8 ((Range_u8_mk (fld_start (_ BitVec 8)) (fld_end (_ BitVec 8)))))
(declare-datatype CoroutineVariantView ((CoroutineVariantView_mk (coroutine_field_0 Range_u8))))
(declare-var mem (Array (_ BitVec 64) (_ BitVec 8)))
(declare-var view CoroutineVariantView)
(assert (= x (concat (concat (concat #x0006 (select mem #x0000000200000000)) (fld_start (coroutine_field_0 view))) (fld_end (coroutine_field_0 view)))))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 3);
    assert_eq!(result.rewritten, 3);
    assert_eq!(result.skipped, 0);
    assert!(!result.output.contains("concat"));
}

#[test]
fn test_declare_var_non_bv_array_range_ignored() {
    let input = "\
(declare-var flag_mem (Array (_ BitVec 64) Bool))
(declare-const a (_ BitVec 32))
(assert (= x (concat a (select flag_mem #x0000000000000000))))
";
    let result = rewrite_concat_for_native_parser(input).expect("rewrite should succeed");
    assert_eq!(result.seen, 1);
    assert_eq!(result.rewritten, 0);
    assert_eq!(result.skipped, 1);
    assert!(result.output.contains("concat"));
}

#[test]
fn test_iterator_count_snapshot_rewrites_all_concats() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "../tests/trust_mc/Coroutines/rustc-coroutine-tests/iterator_count__RNvCslmzq8f5gb6m_14iterator_count4main.symtab.z3_fixed.smt2",
    );
    let input = match fs::read_to_string(&path) {
        Ok(contents) => contents,
        Err(_) => {
            eprintln!(
                "iterator-count snapshot not found at {}; running inline representative SMT",
                path.display()
            );
            let inline = "\
(declare-var _main_9_fld0 (_ BitVec 64))
(declare-var __nested_call_overapprox_3 (_ BitVec 64))
(declare-var mem (Array (_ BitVec 64) (_ BitVec 8)))
(assert (= result (concat _main_9_fld0 __nested_call_overapprox_3)))
(assert (= byte_pair (concat (select mem #x0000000000000001) (select mem #x0000000000000000))))
";
            let result =
                rewrite_concat_for_native_parser(inline).expect("inline rewrite should succeed");
            assert_eq!(result.seen, 2);
            assert_eq!(result.rewritten, 2);
            assert_eq!(result.skipped, 0);
            return;
        }
    };
    let result = rewrite_concat_for_native_parser(&input).expect("rewrite should succeed");
    assert_eq!(
        result.skipped, 0,
        "iterator-count snapshot should leave no concat widths unknown; seen={}, rewritten={}, skipped={}",
        result.seen, result.rewritten, result.skipped
    );
    assert_eq!(result.rewritten, result.seen);
}
