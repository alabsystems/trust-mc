// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Classification coverage and drift guard tests for violation labels.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use regex::Regex;

use super::classify_violation;

const GENERIC_CLASSIFICATION: (&str, &str) = ("assertion", "property check failed");
const STATEMENT_ROOT: &str = "../trust-mc-compiler/src/codegen_ay/statement";
// Part of #2740: Also scan context/ for record_property_violation labels.
const CONTEXT_ROOT: &str = "../trust-mc-compiler/src/codegen_ay/context";

// Additional label sources where record_violation_guarded receives a variable label.
const DYNAMIC_LABEL_PATTERNS: &[(&str, &str)] = &[
    ("codegen_sort.rs", r#"(?s)AssertMessage::.*?=>\s*"([a-z0-9_]+)""#),
    ("arithmetic_checks.rs", r#"(?s)Some\(\(.*?,\s*"([a-z0-9_]+)"\)\)"#),
    (
        "intrinsics/simd/access.rs",
        r#"emit_simd_index_bounds_check\([^,]+,\s*[^,]+,\s*"([a-z0-9_]+)""#,
    ),
    (
        "collections/bigint_shift.rs",
        r#"(?s)emit_(?:shl|shr)_constraints\(.*?,\s*"[a-z0-9_]+",\s*"([a-z0-9_]+)""#,
    ),
    ("dispatch/math_unary.rs", r#"EuclidOp::\w+\s*=>\s*"([a-z0-9_]+)""#),
];

// Generated labels without literal forms in source.
const GENERATED_LABEL_EXAMPLES: &[&str] = &["fadd_fast_non_finite_lhs", "fadd_fast_non_finite_rhs"];

fn assert_maps(label: &str, class: &'static str, description: &'static str) {
    assert_eq!(classify_violation(label), (class, description), "unexpected mapping for {label}");
}

fn collect_rs_files_recursively(dir: &Path, files: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(dir).expect("failed to read statement dir");
    for entry in entries {
        let path = entry.expect("failed to read statement dir entry").path();
        if path.is_dir() {
            if path.file_name().is_some_and(|name| name == "tests") {
                continue;
            }
            collect_rs_files_recursively(&path, files);
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            files.push(path);
        }
    }
}

fn collect_regex_labels(contents: &str, pattern: &Regex, labels: &mut BTreeSet<String>) {
    for capture in pattern.captures_iter(contents) {
        labels.insert(capture[1].to_string());
    }
}

fn collect_dynamic_labels(statement_root: &Path, labels: &mut BTreeSet<String>) {
    for (relative_path, pattern) in DYNAMIC_LABEL_PATTERNS {
        let source_path = statement_root.join(relative_path);
        let contents =
            fs::read_to_string(&source_path).expect("failed to read dynamic label source");
        let regex = Regex::new(pattern).expect("dynamic label regex must compile");
        collect_regex_labels(&contents, &regex, labels);
    }

    for label in GENERATED_LABEL_EXAMPLES {
        labels.insert((*label).to_string());
    }
}

fn emitted_violation_labels() -> BTreeSet<String> {
    let statement_root = Path::new(env!("CARGO_MANIFEST_DIR")).join(STATEMENT_ROOT);
    let mut files = Vec::new();
    collect_rs_files_recursively(&statement_root, &mut files);

    let label_pattern = Regex::new(r#"record_violation_guarded\([^,]+,\s*"([a-z0-9_]+)""#)
        .expect("record_violation_guarded regex must compile");
    let mut labels = BTreeSet::new();
    for file in &files {
        let contents = fs::read_to_string(file).expect("failed to read statement file");
        collect_regex_labels(&contents, &label_pattern, &mut labels);
    }

    collect_dynamic_labels(&statement_root, &mut labels);

    // Part of #2740: Also scan record_property_violation calls in context/.
    let context_root = Path::new(env!("CARGO_MANIFEST_DIR")).join(CONTEXT_ROOT);
    let mut context_files = Vec::new();
    collect_rs_files_recursively(&context_root, &mut context_files);
    let property_pattern = Regex::new(r#"record_property_violation\([^,]+,\s*"([a-z0-9_]+)""#)
        .expect("record_property_violation regex must compile");
    let property_with_loc_pattern =
        Regex::new(r#"record_property_violation_with_location\([^,]+,\s*"([a-z0-9_]+)""#)
            .expect("record_property_violation_with_location regex must compile");
    for file in &context_files {
        let contents = fs::read_to_string(file).expect("failed to read context file");
        collect_regex_labels(&contents, &property_pattern, &mut labels);
        collect_regex_labels(&contents, &property_with_loc_pattern, &mut labels);
    }

    labels
}

#[test]
fn test_classify_violation_expanded_families() {
    assert_maps("panic", "assertion", "panic reached");
    assert_maps("panic_stub", "assertion", "panic reached");
    assert_maps("unreachable", "assertion", "panic reached");

    assert_maps("bigint_div_by_zero", "division-by-zero", "division by zero");
    assert_maps("bigint_mod_by_zero", "division-by-zero", "division by zero");

    assert_maps("simd_extract", "array_bounds", "SIMD index out of bounds");
    assert_maps("simd_insert", "array_bounds", "SIMD index out of bounds");

    assert_maps("offset_value_overflow", "pointer-overflow", "pointer arithmetic overflow");
    assert_maps("offset_bytes_overflow", "pointer-overflow", "pointer arithmetic overflow");
    assert_maps("offset_result_overflow", "pointer-overflow", "pointer arithmetic overflow");

    assert_maps("bigint_shl_negative_shift", "undefined-shift", "negative shift amount");
    assert_maps("bigint_shr_negative_shift", "undefined-shift", "negative shift amount");
    assert_maps("bigint_shl_assign_negative_shift", "undefined-shift", "negative shift amount");
    assert_maps("bigint_shr_assign_negative_shift", "undefined-shift", "negative shift amount");

    assert_maps("ctlz_nonzero_ub", "undefined-behavior", "undefined behavior");
    assert_maps("cttz_nonzero_ub", "undefined-behavior", "undefined behavior");
    assert_maps("biguint_neg_positive", "undefined-behavior", "undefined behavior");

    assert_maps(
        "use_after_free_check",
        "pointer_dereference",
        "dereference failure: use after free",
    );
    // Part of #2740: Heap deallocation safety labels.
    assert_maps(
        "dealloc_base_pointer_check",
        "pointer_dereference",
        "dereference failure: dealloc base pointer mismatch",
    );
    assert_maps(
        "dealloc_size_mismatch",
        "pointer_dereference",
        "dereference failure: dealloc size mismatch",
    );
    assert_maps("double_free_check", "pointer_dereference", "dereference failure: double free");

    assert_maps("unsupported_check", "unsupported_construct", "unsupported construct");
    assert_maps(
        "iterator_sort_mismatch_unsound",
        "unsoundness",
        "iterator sort mismatch over-approximation",
    );
    assert_maps(
        "unsound_interior_mutable_read",
        "unsoundness",
        "interior-mutable read over-approximation",
    );

    // Part of #3404: div_euclid/rem_euclid violation labels.
    assert_maps("div_euclid_zero", "division-by-zero", "euclidean division by zero");
    assert_maps("rem_euclid_zero", "division-by-zero", "euclidean division by zero");
    assert_maps("div_euclid_overflow", "overflow", "euclidean division signed overflow");
    assert_maps("rem_euclid_overflow", "overflow", "euclidean division signed overflow");

    // Part of #3406: Step unchecked overflow label.
    assert_maps("step_unchecked_overflow", "overflow", "step unchecked overflow");

    // Compile-time type-validity assertion (assert_inhabited/assert_zero_valid/
    // assert_mem_uninitialized_valid); classified with the assertion siblings.
    assert_maps("assert_type_validity", "assertion", "type validity assertion failed");

    // Part of #3742: BMC assert fail-closed labels.
    assert_maps("kani_assert_no_args", "assertion", "kani::assert missing condition");
    assert_maps(
        "untranslatable_assert_operand",
        "assertion",
        "assert condition operand untranslatable",
    );
    assert_maps(
        "untranslatable_assert_bv_width",
        "assertion",
        "assert condition bitvector width unavailable",
    );
    assert_maps("untranslatable_assert_sort", "assertion", "assert condition sort unsupported");
    assert_maps(
        "untranslatable_overflow_assert",
        "overflow",
        "overflow check operands untranslatable",
    );
}

#[test]
fn test_classify_violation_generated_label_prefixes() {
    assert_maps(
        "fadd_fast_non_finite_lhs",
        "undefined-behavior",
        "fast-math operand is non-finite",
    );
    assert_maps(
        "fmul_fast_non_finite_rhs",
        "undefined-behavior",
        "fast-math operand is non-finite",
    );
    assert_maps("overflow_check_assign", "overflow", "arithmetic overflow");
}

#[test]
fn test_classify_violation_label_drift_guard() {
    let labels = emitted_violation_labels();
    assert!(!labels.is_empty(), "drift guard extraction found no emitted violation labels");

    let mut generic_fallback_labels: Vec<String> = labels
        .into_iter()
        .filter(|label| classify_violation(label) == GENERIC_CLASSIFICATION)
        .collect();
    generic_fallback_labels.sort();

    assert!(
        generic_fallback_labels.is_empty(),
        "emitted labels still falling back to generic assertion classification: {:?}",
        generic_fallback_labels
    );
}
