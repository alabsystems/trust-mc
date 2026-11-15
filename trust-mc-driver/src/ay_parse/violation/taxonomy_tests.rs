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
// codegen_ay's own top-level files (not recursive): codegen_function.rs records
// whole-function stand-ins such as `bmc_codegen_panic`. The CHC lane (chc/)
// reports through `PropertyKind`, not this taxonomy, so it is not scanned.
const CODEGEN_ROOT: &str = "../trust-mc-compiler/src/codegen_ay";
// Every BMC recorder that takes a literal label as its second argument: the
// guarded statement forms, with and without a message, the context property
// forms, with a location or with location and message, and the
// `emit_division_by_zero_check` helper that forwards its literal label to the
// guarded form. A form left out here is a label the guard cannot see.
const RECORDER_LABEL_PATTERN: &str = r#"(?:record_(?:violation_guarded(?:_with_message|_ungated)?|property_violation(?:_with_location|_full)?)|emit_division_by_zero_check)\([^,]+,\s*"([a-z0-9_]+)""#;

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
    // The copy family binds its label once and records it at several sites.
    ("codegen_copy.rs", r#"let label = "([a-z0-9_]+)";"#),
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

    let label_pattern =
        Regex::new(RECORDER_LABEL_PATTERN).expect("recorder label regex must compile");
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
    for file in &context_files {
        let contents = fs::read_to_string(file).expect("failed to read context file");
        collect_regex_labels(&contents, &label_pattern, &mut labels);
    }

    let codegen_root = Path::new(env!("CARGO_MANIFEST_DIR")).join(CODEGEN_ROOT);
    for entry in fs::read_dir(&codegen_root).expect("failed to read codegen_ay dir") {
        let path = entry.expect("failed to read codegen_ay dir entry").path();
        if path.is_file() && path.extension().is_some_and(|ext| ext == "rs") {
            let contents = fs::read_to_string(&path).expect("failed to read codegen_ay file");
            collect_regex_labels(&contents, &label_pattern, &mut labels);
        }
    }

    labels
}

#[test]
fn test_classify_violation_expanded_families() {
    assert_maps("panic", "assertion", "panic reached");
    assert_maps("panic_stub", "assertion", "panic reached");
    // Kani-identical: TerminatorKind::Unreachable reports as its own class,
    // which `determine_failed_from_properties` still counts as a panic.
    assert_maps("unreachable", "unreachable", "unreachable code");

    // The BMC unwinding assertion must NOT land in the panic family: its class
    // gates concrete playback and the should_panic accounting, and its
    // description carries the "unwinding assertion loop" prefix that
    // `has_unwinding_assertion_failures` looks for.
    let (unwind_class, unwind_desc) = classify_violation("unwind_assert");
    assert_eq!(unwind_class, "unwind", "unwind_assert must not be classified as a panic");
    assert!(
        unwind_desc.starts_with("unwinding assertion loop"),
        "the raise-the-bound tip keys off this prefix: {unwind_desc}"
    );
    assert!(unwind_desc.contains("--unwind"), "the description must name the flag to raise");

    assert_maps("bigint_div_by_zero", "division-by-zero", "division by zero");
    assert_maps("bigint_mod_by_zero", "division-by-zero", "division by zero");

    assert_maps("simd_extract", "undefined-behavior", "simd_extract: SIMD index out of bounds");
    assert_maps("simd_insert", "undefined-behavior", "simd_insert: SIMD index out of bounds");

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
    // Part of #2740: Heap deallocation safety labels. The base-pointer check
    // renders CBMC's wording, which the corpus pins (dealloc/stack).
    assert_maps(
        "dealloc_base_pointer_check",
        "pointer_dereference",
        "free argument must be dynamic object",
    );

    // Kani-identical raw-pointer deref texts (zst, issue-3571, ptr_to_ref_cast).
    assert_maps("raw_ptr_deref_null", "safety_check", "null pointer dereference occurred");
    assert_maps(
        "raw_ptr_deref_misaligned",
        "safety_check",
        "misaligned pointer dereference: address must be a multiple of its type's alignment",
    );

    // Kani-identical INT_MIN / -1 overflow wordings for `/` and `%`.
    assert_maps("overflow_check_div", "overflow", "attempt to divide with overflow");
    assert_maps(
        "overflow_check_rem",
        "overflow",
        "attempt to calculate the remainder with overflow",
    );
    // SIMD lane checks keep Kani's `arithmetic_overflow` class: wrapping
    // simd_add/sub/mul and UB simd_div/rem `MIN / -1` are never a Rust panic.
    assert_maps(
        "overflow_check_simd_arith",
        "arithmetic_overflow",
        "SIMD lane arithmetic overflow",
    );
    assert_maps(
        "overflow_check_simd_div_rem",
        "arithmetic_overflow",
        "SIMD lane signed division overflow",
    );
    assert_maps(
        "dealloc_size_mismatch",
        "pointer_dereference",
        "dereference failure: dealloc size mismatch",
    );
    assert_maps("double_free_check", "pointer_dereference", "dereference failure: double free");

    assert_maps("unsupported_check", "unsupported_construct", "unsupported construct");
    assert_maps(
        "unsupported_loop_decreases",
        "loop_decreases",
        "loop `decreases` ranking not proven (termination measure)",
    );
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
    assert_maps(
        "unsound_raw_ptr_cached_read",
        "unsoundness",
        "raw pointer read through a cached value that byte memory contradicts",
    );

    // Part of #3404: div_euclid/rem_euclid violation labels.
    assert_maps("div_euclid_zero", "division-by-zero", "euclidean division by zero");
    assert_maps("rem_euclid_zero", "division-by-zero", "euclidean division by zero");
    assert_maps("div_euclid_overflow", "overflow", "euclidean division signed overflow");
    assert_maps("rem_euclid_overflow", "overflow", "euclidean division signed overflow");

    // Part of #3406: Step unchecked overflow label.
    assert_maps("step_unchecked_overflow", "undefined-behavior", "step unchecked overflow");

    // simd_div/simd_rem zero lane divisor: UB, not the scalar panic class.
    assert_maps("simd_div_by_zero_check", "undefined-behavior", "division by zero");
    // The intercepted integer methods' zero-divisor checks: wrapping_,
    // saturating_ and overflowing_ div/rem panic on a zero divisor, and the
    // unchecked_ intrinsic makes it UB.
    assert_maps("wrapping_div_by_zero", "division-by-zero", "division by zero");
    assert_maps("saturating_div_by_zero", "division-by-zero", "division by zero");
    assert_maps("overflowing_div_by_zero", "division-by-zero", "division by zero");
    assert_maps("unchecked_div_by_zero", "undefined-behavior", "division by zero");
    // `unchecked_add`/`sub`/`mul` overflow: UB, Kani's `arithmetic_overflow`
    // class and text (tests/ui/Property-Class-UI/arithmetic_overflow), never the
    // safe operators' `overflow` panic class.
    for (label, op) in [
        ("unchecked_add_overflow", "unchecked_add"),
        ("unchecked_sub_overflow", "unchecked_sub"),
        ("unchecked_mul_overflow", "unchecked_mul"),
    ] {
        let (class, description) = classify_violation(label);
        assert_eq!(class, "arithmetic_overflow", "{label}");
        assert_eq!(
            description,
            format!("attempt to compute `{op}` which would overflow"),
            "{label}"
        );
        assert!(!super::class_is_rust_panic(class), "{label} must NOT be a Rust panic");
    }
    // `unchecked_shl`/`unchecked_shr` distance: UB, Kani's `arithmetic_overflow`
    // class and texts, never the MIR `Assert`'s or CBMC's shift classes.
    for (label, description) in [
        ("unchecked_shift_distance_check", "attempt to shift by excessive shift distance"),
        ("unchecked_shift_distance_check_negative", "attempt to shift by negative distance"),
    ] {
        assert_maps(label, "arithmetic_overflow", description);
        assert!(!super::class_is_rust_panic("arithmetic_overflow"), "{label}");
    }
    // The safe operators keep their panic labels and Kani's rustc texts.
    assert_maps("overflow_check_add", "overflow", "attempt to add with overflow");
    assert_maps("overflow_check_sub", "overflow", "attempt to subtract with overflow");
    assert_maps("overflow_check_mul", "overflow", "attempt to multiply with overflow");
    // Operator-level integer Div/Rem checks (statement/rvalue.rs): Kani's
    // `check_div_overflow` class and texts, never the MIR Assert's panic class.
    assert_maps("binop_div_by_zero", "arithmetic_overflow", "attempt to divide by zero");
    assert_maps(
        "binop_rem_by_zero",
        "arithmetic_overflow",
        "attempt to calculate the remainder with a divisor of zero",
    );
    assert_maps("binop_div_overflow", "arithmetic_overflow", "attempt to divide with overflow");
    assert_maps(
        "binop_rem_overflow",
        "arithmetic_overflow",
        "attempt to calculate the remainder with overflow",
    );

    // Native BMC Box validity (048c5fabb): UB, so it must stay out of the panic
    // family a `#[kani::should_panic]` harness may bank.
    assert_maps(
        "box_deref_validity",
        "undefined-behavior",
        "Box pointer validity: non-null, aligned, inhabited pointee; live and in bounds unless zero-sized",
    );
    assert!(!super::class_is_rust_panic(classify_violation("box_deref_validity").0));

    // Labels emitted only through `record_violation_guarded_with_message`, a
    // `let label` binding or codegen_function.rs, which the drift guard did not
    // scan: each fell to the panic-family `assertion` default.
    assert_maps(
        "float_to_int_unchecked_non_finite",
        "undefined-behavior",
        "float_to_int_unchecked: attempt to convert a non-finite value to an integer",
    );
    assert_maps(
        "float_to_int_unchecked_out_of_range",
        "undefined-behavior",
        "float_to_int_unchecked: attempt to convert a value out of range of the target integer",
    );
    assert_maps(
        "copy_byte_count_overflow",
        "undefined-behavior",
        "attempt to compute number in bytes which would overflow",
    );
    assert_maps("copy_overlap_check", "pointer_dereference", "memcpy src/dst overlap");
    assert_maps(
        "simd_shuffle_index_check",
        "undefined-behavior",
        "index out of bounds: the length is less than or equal to the given index",
    );
    assert_maps(
        "unstable_vtable_comparison",
        "safety_check",
        "unstable vtable comparison must not be reached: vtable identity is unspecified",
    );
    assert_maps(
        "unsupported_foreign_function",
        "unsupported_construct",
        "unsupported construct: call to a foreign function with no model or --c-lib definition",
    );
    assert_maps(
        "unsupported_loop_contract",
        "unsupported_construct",
        "unsupported construct: loop invariant captures a dereference the loop-contract encoding does not support",
    );
    assert_maps(
        "bmc_codegen_panic",
        "unsupported_construct",
        "unsupported construct: BMC codegen panic while encoding this function",
    );

    // `exact_div` is an unsafe intrinsic: Kani gives all three obligations its
    // own `exact_div` class (tests/ui/Property-Class-UI/exact_div/expected), and
    // keeping them there is what stops `class_is_rust_panic` banking UB as the
    // panic a `#[kani::should_panic]` harness asked for.
    assert_maps("exact_div_not_exact", "exact_div", "exact_div arguments divide exactly");
    assert_maps("exact_div_zero", "exact_div", "exact_div divisor is nonzero");
    assert_maps("exact_div_overflow", "exact_div", "exact_div division does not overflow");

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

#[test]
fn test_classify_violation_nan_check_labels() {
    // `--nan-check` obligations carry Kani's `NaN` class and "NaN on <op>" text;
    // the soundness-dual gate keys the `nan` property off this wording.
    assert_maps("nan_check_add", "NaN", "NaN on +");
    assert_maps("nan_check_sub", "NaN", "NaN on -");
    assert_maps("nan_check_mul", "NaN", "NaN on *");
    assert_maps("nan_check_div", "NaN", "NaN on /");
    assert_maps("nan_check_rem", "NaN", "NaN on %");
}
