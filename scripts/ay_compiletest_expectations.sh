#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Expectation/outcome helper module for ay-compiletest.sh (Part of #3892).
# Sourced by scripts/ay-compiletest.sh — do not run standalone.

# Provenance tracking (Part of #1058)
# Count verification result types from [AY:*] markers
harness_proof=0       # [AY:PROOF] - proven safe
harness_ctrex=0       # [AY:CTREX] - counterexample found
harness_unknown=0     # [AY:UNKNOWN] - solver inconclusive
harness_error=0       # [AY:ERROR] - verification error

# Harnesses known to hang with AY backend - skip to prevent resource exhaustion.
# Format: "<relative-test-file>|<harness>|<issue>"
KNOWN_HANG_HARNESS=(
    # Entries removed: #2247 atomic harnesses now pass (resolved by atomic intrinsic codegen)
)

normalize_known_hang_file() {
    local file="$1"
    local file_dir file_name

    # Canonicalize existing paths so equivalent path spellings map to one key.
    if [[ -e "$file" ]]; then
        file_name=$(basename "$file")
        file_dir=$(cd "$(dirname "$file")" >/dev/null 2>&1 && pwd) || file_dir=""
        if [[ -n "$file_dir" ]]; then
            file="$file_dir/$file_name"
        fi
    else
        # Keep lightweight normalization for synthetic/non-existent paths.
        while [[ "$file" == ./* ]]; do
            file="${file#./}"
        done
    fi

    if [[ "$file" == "$TRUST_MC_DIR/tests/trust-mc/"* ]]; then
        file="${file#$TRUST_MC_DIR/tests/trust-mc/}"
    elif [[ "$file" == "$TRUST_MC_DIR/tests/"* ]]; then
        file="${file#$TRUST_MC_DIR/tests/}"
    elif [[ "$file" == tests/trust-mc/* ]]; then
        file="${file#tests/trust-mc/}"
    elif [[ "$file" == tests/* ]]; then
        file="${file#tests/}"
    fi
    printf '%s\n' "$file"
}

known_hang_issue_for_harness() {
    local file="$1"
    local harness="$2"
    local normalized_file
    normalized_file=$(normalize_known_hang_file "$file")

    [[ ${#KNOWN_HANG_HARNESS[@]} -eq 0 ]] && return 1

    local entry entry_file entry_harness entry_issue rest
    for entry in "${KNOWN_HANG_HARNESS[@]}"; do
        entry_file="${entry%%|*}"
        rest="${entry#*|}"
        entry_harness="${rest%%|*}"
        entry_issue="${rest##*|}"
        if [[ "$normalized_file" == "$entry_file" && "$harness" == "$entry_harness" ]]; then
            printf '%s\n' "$entry_issue"
            return 0
        fi
    done
    return 1
}

# Harnesses known to produce false proofs (expected CTREX, got PROOF).
# These are tracked separately and do NOT count as test failures.
# Format: "<relative-test-file>|<harness>|<issue>"
# Part of #3350: systematic tracking of known false proofs.
KNOWN_FALSE_PROOF_HARNESS=(
    # Conflict analysis harnesses: resolved (#3348). 5 harnesses moved to
    # ay_self_verify_conflict_analysis_pass.rs with kani-expect: PROOF.
    # Entries removed — no longer false proofs.
)

# Counter for known false proofs (skipped).
harness_known_false_proof=0

known_false_proof_issue_for_harness() {
    local file="$1"
    local harness="$2"
    local normalized_file
    normalized_file=$(normalize_known_hang_file "$file")

    [[ ${#KNOWN_FALSE_PROOF_HARNESS[@]} -eq 0 ]] && return 1

    local entry entry_file entry_harness entry_issue rest
    for entry in "${KNOWN_FALSE_PROOF_HARNESS[@]}"; do
        entry_file="${entry%%|*}"
        rest="${entry#*|}"
        entry_harness="${rest%%|*}"
        entry_issue="${rest##*|}"
        if [[ "$normalized_file" == "$entry_file" && "$harness" == "$entry_harness" ]]; then
            printf '%s\n' "$entry_issue"
            return 0
        fi
    done
    return 1
}

# Parse provenance markers from kani output and increment counters (Part of #1058)
# Called after each harness run to track verification result types.
# Uses the final marker emitted by the harness output to avoid double counting
# when ay-chc retries with alternative engines (#2052).
# Part of #4099: $4 = effective_success_reason. When a should_panic harness
# gets CTREX with effective_success=should_panic_panics_only, the CTREX
# *is* the proof (finding the panic proves should_panic is satisfied).
# Count it as PROOF for verified rate.
parse_provenance() {
    local output="$1"
    local file="${2:-}"
    local harness="${3:-}"
    local effective_success_reason="${4:-}"
    local verdict
    verdict=$(get_actual_outcome "$output" "$file" "$harness")
    # Part of #4099: should_panic + CTREX = PROOF (finding the counterexample
    # proves the panic is reachable, which is the verification goal).
    if [[ "$verdict" == "CTREX" && "$effective_success_reason" == "should_panic_panics_only" ]]; then
        verdict="PROOF"
    fi
    case "$verdict" in
        PROOF)
            ((harness_proof++))
            ;;
        CTREX)
            ((harness_ctrex++))
            ;;
        UNKNOWN)
            ((harness_unknown++))
            ;;
        ERROR)
            ((harness_error++))
            ;;
    esac
}

# Extract reason-coded translation-drop markers for the current harness.
# Output format: "reason=count,reason2=count2" or empty.
collect_translation_drop_reasons_for_harness() {
    local output="$1" harness="$2"
    # Bash-3-compatible: pipe through awk instead of using local -A (bash 4).
    # Part of #3799: macOS ships bash 3.2 which lacks associative arrays.
    # Awk aggregates reason counts, emits one "reason\tcount" per line, then
    # sort + awk reformats into the "reason=count,reason2=count2" string.
    # Part of #3814: In single-harness mode (compiletest), aggregate all reason
    # tags from the run without fn_name filtering. The compiler processes the
    # entire file, so fn_names are internal function names (e.g., LinearRow::add_term),
    # not the harness name (e.g., proof_add_term_cancellation). The fn_name filter
    # dropped ALL tags, producing null translation_drop_reasons despite nonzero
    # chc_translation_drop counts.
    printf '%s\n' "$output" \
        | grep -oE '\[AY:TRANSLATION_DROP_REASON:[^]]+\]' \
        | awk '
    {
        s = $0
        sub(/^\[AY:TRANSLATION_DROP_REASON:/, "", s)
        sub(/\]$/, "", s)
        eq = index(s, "=")
        if (eq == 0) next
        lhs = substr(s, 1, eq - 1)
        cnt = substr(s, eq + 1)
        if (cnt + 0 != cnt) next
        n = split(lhs, parts, ":")
        if (n < 2) next
        reason = parts[n]
        if (reason == "") next
        reasons[reason] += cnt
    }
    END {
        for (r in reasons) print r "\t" reasons[r]
    }' \
        | sort \
        | awk -F'\t' '{ if (NR > 1) printf ","; printf "%s=%s", $1, $2 }'
}

# Part of #4078: collect inferable-summary markers from driver output.
# Parses [AY:INFERABLE_SUMMARY:<fn_name>:<summary_name>=<count>] markers.
# Returns sorted "summary_name=count,..." CSV (Bash-3-compatible).
# Unlike translation-drop reasons where the reason is a simple identifier,
# summary_name contains "::" (e.g., P_inf_Foo::bar), so we cannot use the
# "take last :-split segment" approach. Instead we find the boundary between
# fn_name and summary_name by matching on the single-colon separator between
# two non-colon characters (Rust :: uses two colons, the fn:summary boundary
# uses one).
collect_inferable_summaries_for_harness() {
    local output="$1"
    # Aggregate all INFERABLE_SUMMARY markers from the run (no fn_name filter,
    # same reasoning as #3814 for translation-drop).
    printf '%s\n' "$output" \
        | grep -oE '\[AY:INFERABLE_SUMMARY:[^]]+\]' \
        | awk '
    {
        s = $0
        sub(/^\[AY:INFERABLE_SUMMARY:/, "", s)
        sub(/\]$/, "", s)
        # s is now "fn_name:summary_name=count"
        eq = index(s, "=")
        if (eq == 0) next
        cnt = substr(s, eq + 1)
        if (cnt + 0 != cnt) next
        lhs = substr(s, 1, eq - 1)
        # lhs is "fn_name:summary_name" — both may contain "::"
        # Find the boundary: scan for a single ":" between two non-":" chars.
        # In "mod::fn:P_inf_X::y", the boundary ":" is between "fn" and "P".
        summary = ""
        prev = ""
        for (i = 1; i <= length(lhs); i++) {
            c = substr(lhs, i, 1)
            if (c == ":" && prev != ":" && i < length(lhs) && substr(lhs, i+1, 1) != ":") {
                summary = substr(lhs, i + 1)
            }
            prev = c
        }
        if (summary == "") next
        summaries[summary] += cnt
    }
    END {
        for (r in summaries) print r "\t" summaries[r]
    }' \
        | sort \
        | awk -F'\t' '{ if (NR > 1) printf ","; printf "%s=%s", $1, $2 }'
}

EXPECTED_FAIL_HARNESS=(
    # Raw pointer safety tests (#711, #712, #713) — REMOVED: already in
    # test_raw_ptr_safety_fail.rs with kani-verify-fail (split per #2292, cleanup #3194).
    # Alignment tests (#2080) — REMOVED: split to test_alignment_safety_fail.rs (Part of #3194)
    # Loop address stability — REMOVED: split to test_addressof_stability_fail.rs (Part of #3194)
    test_heap_size_mismatch_should_fail  # (#1174) CTREX for wrong dealloc size
    # Arithmetic overflow: wrapping_neg was missing CHC stub (#3114).
    # check_neg_overflow — REMOVED P1:1309: now passes (AY bump 3348639a)
    # Enum variant ref deref: Datatype encoding gap (#2876).
    # Historical Z3 error (Z3 eliminated): "unknown function Val" — Val constructor not declared.
    # check_enum_variant_ref_deref — REMOVED: XFAIL hides PROOF-expected failure.
    # Genuine encoding gap; should show as FAIL, not XFAIL. Part of #3529.
    # ay_for_symbolic_range — REMOVED W1:TIC: now passes via Template-Directed
    # Inductive Checking (TIC). Part of #3258.
    # ay_unbounded_countdown_accum — REMOVED W1:TIC: now passes via TIC. Part of #3258.
    # test_alloc_zeroed — REMOVED W2:3436b: now passes with concrete_size
    # resolution through MIR inlining + ITE safety cap. Part of #3273.
    # Realloc: CHC encoding now generated (no longer OOMs) but CTREX due to
    # 2 translation drops in realloc copy semantics. Part of #3273.
    # test_realloc_grow — REMOVED: XFAIL hides PROOF-expected failure.
    # chc_translation_drop=2; should show as FAIL. Part of #3529.
    # AY self-verify: Vec encoding gap — CHC codegen over-approximates Vec
    # state, producing spurious CTREX. Part of #3289, tracked under #3186.
    # proof_non_empty_clause_not_empty — REMOVED: XFAIL hides PROOF-expected
    # failure. Vec encoding gap; should show as FAIL. Part of #3529.
    # proof_dependency_mark_union_associative — REMOVED W1:3348a: now passes
    # via UNKNOWN→retry extended-timeout strategy (#3298). Was: passes at
    # 120s timeout, UNKNOWN at default 30s. Retry doubles timeout to 120s.
    # AY self-verify: BTreeMap encoding gap — CHC codegen doesn't model
    # BTreeMap insert/get/clone. Part of #3289, tracked under #3186.
    # array_read_over_write_hit — REMOVED: now PROOF, moved to _pass.rs. Part of #3348.
    # array_read_over_write_miss — REMOVED: now PROOF, moved to _pass.rs. Part of #3348.
    # array_store_overwrites — REMOVED: now PROOF, moved to _pass.rs. Part of #3348.
    # array_store_commutative_different_indices — REMOVED: source file carries
    # kani-expect: UNKNOWN, so a matching UNKNOWN should report PASS rather
    # than legacy XFAIL noise.
    # array_default_value — REMOVED: now PROOF, moved to _pass.rs. Part of #3348.
    # array_store_isolation — REMOVED: now PROOF, moved to _pass.rs. Part of #3348.
    # AY self-verify: Vec<bool> encoding gap — bitblast operations use
    # iter/map/collect which CHC codegen doesn't model. Part of #3289.
    bv_and_preserves_width
    bv_or_preserves_width
    bv_xor_preserves_width
    # bv_not_preserves_width — REMOVED: now PROOF (unary, no heap gap). Part of #3381.
    bv_add_preserves_width
    bv_concat_width_sum
    bv_extract_width
    # bv_not_involutive — REMOVED: now PROOF (unary, no heap gap). Part of #3381.
    # bv_xor_self_is_zero — REMOVED: now PROOF (binary, no heap gap). Part of #3381.
    bv_concat_extract_roundtrip
    # AY self-verify: Vec<bool>/Vec<usize> encoding gap — conflict analysis
    # uses Vec indexing, mutation, and sparse-clear. Part of #3289.
    # conflict_clear_all_resets — REMOVED: still CTREX (for-loop iteration gap).
    # conflict_clear_then_remark — REMOVED: still CTREX (for-loop iteration gap).
    # Both remain in ay_self_verify_conflict_analysis.rs (kani-expect: CTREX).
    # conflict_mark_then_check — REMOVED: now PROOF (Part of #3348).
    # conflict_mark_idempotent — REMOVED: now PROOF (Part of #3348).
    # conflict_mark_isolation — REMOVED: now PROOF (Part of #3348).
    # conflict_grow_preserves_marks — REMOVED: now PROOF after VecResize stub,
    # moved to ay_self_verify_conflict_analysis_pass.rs (Part of #3348 W4:3614).
    # conflict_oob_mark_safe — REMOVED: now PROOF, moved to _pass.rs (Part of #3647).
    # conflict_count_consistent — REMOVED: now PROOF, moved to _pass.rs (Part of #3647).
)

# Per-harness expected-outcome override (Part of #134).
# These harnesses live in files with a file-level kani-expect: that doesn't
# match their individual verdict. Use format: "harness_name=OUTCOME".
# Example: "bv_to_u64_roundtrip=PROOF" overrides a file-level CTREX expectation.
EXPECTED_OUTCOME_OVERRIDE=(
    # bv_to_u64_roundtrip in ay_self_verify_bv_bitblast.rs: file expects CTREX.
    # Was PROOF at AY pin 496ab1b (Part of P1:1369, P1:1371).
    # Regressed to UNKNOWN after AY bump 2c693f1→3325ffb (P1:1405).
    # REMOVED: bv_to_u64_roundtrip=PROOF (now UNKNOWN)
    # bv_not_preserves_width, bv_not_involutive, bv_xor_self_is_zero:
    # AY-version-sensitive. Were PROOF at pin baeaef490f (Part of #3381),
    # regressed to UNKNOWN/CTREX after AY bump 2c693f1→3325ffb (P1:1405).
    # File-level kani-expect: CTREX matches current AY behavior.
    # REMOVED: bv_not_preserves_width=PROOF (now UNKNOWN)
    # REMOVED: bv_not_involutive=PROOF (now UNKNOWN)
    # REMOVED: bv_xor_self_is_zero=PROOF (now CTREX)
    # conflict_clear_then_remark and conflict_clear_all_resets: still CTREX in
    # ay_self_verify_conflict_analysis.rs (for-loop iteration encoding gap).
    # conflict_analysis harness split (Part of #3647):
    #   _pass.rs (kani-expect: PROOF): oob_mark_safe, count_consistent,
    #     mark_then_check, mark_idempotent, mark_isolation, grow_preserves_marks
    #   _analysis.rs (kani-expect: CTREX): clear_all_resets, clear_then_remark
    # REMOVED: conflict_mark_idempotent=PROOF (now CTREX, AY regression)
    # REMOVED: conflict_mark_isolation=PROOF (now CTREX, AY regression)
    # REMOVED: conflict_mark_then_check=PROOF (now CTREX, AY regression)
    # conflict_grow_preserves_marks: was CTREX override (AY regression P1:1405).
    # REMOVED: all 4 mark/grow harnesses moved to _pass.rs (kani-expect: PROOF)
    # after encoding improvements made them genuinely provable. Part of #3647.
    # two_vec_struct_mark, two_vec_struct_push_len_only, two_vec_struct_write_push_read:
    # Fixed by #3084 — skip sidecar len_var path when field_projections indicate
    # struct-embedded Vec. Now achieves PROOF. Override removed.
    # array_default_value — REMOVED: moved to _pass.rs (kani-expect: PROOF). Part of #3348.
    # array_read_over_write_hit — REMOVED: moved to _pass.rs (kani-expect: PROOF). Part of #3348.
    # copy_raw_ptr_constant: was UNKNOWN due to ub_checks::maybe_is_aligned
    # function rename in Rust nightly 2025-12-03 (dropped _and_not_null suffix).
    # Fixed by adding short-name variants to stub lookup. Part of #3665.
    # Removed override: now PROOF.
    # check_packed_deref, check_packed_read_unaligned: file-level kani-expect: CTREX.
    # Were PROOF after #3470 packed-struct alignment override, but reverted to
    # CTREX(Genuine) after #3930 fixed the RangeBounds::contains overapprox
    # dispatch. The overapprox is gone (kani_mem_overapprox=0), but there's a
    # genuine encoding gap in can_dereference whole-struct char validity.
    # REMOVED: check_packed_deref=PROOF (now CTREX, genuine encoding gap)
    # REMOVED: check_packed_read_unaligned=PROOF (now CTREX, genuine encoding gap)
    # MemPredicates same_allocation.rs + foreign_type.rs: expectations moved to
    # source files (Part of #3859). See same_allocation.rs kani-expect headers.
    # ay_self_verify_bootstrap_tier2_xor_dpll.rs: 4 former CTREX overrides
    # removed — all achieve PROOF as of AY@11adbbb5 (W3:3968 verification).
    # Part of #3766.
    # ay_self_verify_bv_bitblast.rs: file-level kani-expect: UNKNOWN.
    # bv_pop_empty_is_safe still achieves PROOF (simple struct/counter op).
    # bv_clauses_monotonic, bv_fresh_var_monotonic, bv_reset_clears_state now
    # produce sound trivial-safe PROOF (no kani::any, no error rules emitted).
    # See reports/bv-bitblast-investigation-2026-04-19.md and #4284.
    bv_clauses_monotonic=PROOF
    bv_fresh_var_monotonic=PROOF
    bv_pop_empty_is_safe=PROOF
    bv_push_pop_stack_depth=UNKNOWN
    bv_reset_clears_state=PROOF
    # bv_not_involutive, bv_xor_self_is_zero: AY-version-sensitive.
    # Were PROOF at pin baeaef490f, regressed to UNKNOWN (P1:1405).
    # File-level CTREX doesn't match UNKNOWN. Part of #3766.
    bv_not_involutive=UNKNOWN
    bv_xor_self_is_zero=UNKNOWN
)

# Look up per-harness expected-outcome override.
# Returns the overridden outcome on stdout, or empty if no override.
get_harness_outcome_override() {
    local harness="$1"
    local entry
    for entry in "${EXPECTED_OUTCOME_OVERRIDE[@]}"; do
        local name="${entry%%=*}"
        local outcome="${entry##*=}"
        if [[ "$harness" == "$name" ]]; then
            echo "$outcome"
            return 0
        fi
    done
    return 1
}

is_expected_fail_harness() {
    local harness="$1"
    local expected
    for expected in "${EXPECTED_FAIL_HARNESS[@]}"; do
        if [[ "$harness" == "$expected" ]]; then
            return 0
        fi
    done
    return 1
}

# Check if file has kani-verify-fail annotation in header.
# Matches: // kani-verify-fail (in first 20 lines)
is_expected_fail_file() {
    local file="$1"
    head -20 "$file" 2>/dev/null | grep -q "^// *kani-verify-fail"
}

# Extract kani-flags from file header (Part of #1455).
# Matches: // kani-flags: <flags> (in first 20 lines)
# Returns flags as space-separated string, empty if none found.
extract_kani_flags() {
    local file="$1"
    local flags_line
    flags_line=$(head -20 "$file" 2>/dev/null | grep -m1 "^// *kani-flags:")
    if [[ -n "$flags_line" ]]; then
        # Extract everything after "kani-flags:" and trim leading/trailing whitespace
        echo "$flags_line" | sed 's|.*kani-flags:||' | tr -s ' ' | sed 's/^ *//;s/ *$//'
    fi
}

# Extract compile-flags from file header (Part of #3766).
# Matches: // compile-flags: <flags> (in first 20 lines)
# These are rustc flags (e.g., --edition 2018) that must be passed via RUSTFLAGS.
extract_compile_flags() {
    local file="$1"
    local flags_line
    flags_line=$(head -20 "$file" 2>/dev/null | grep -m1 "^// *compile-flags:")
    if [[ -n "$flags_line" ]]; then
        echo "$flags_line" | sed 's|.*compile-flags:||' | tr -s ' ' | sed 's/^ *//;s/ *$//'
    fi
}

# Extract expected verification outcome from file header (Part of #1755).
# Matches file-level directives like:
#   // kani-expect: PROOF|CTREX|UNKNOWN|BMC_SAFE
# and harness-scoped directives like:
#   // kani-expect: some_harness=PROOF
# in the first 50 lines. Returns expected outcome or empty if not specified.
# - PROOF: Require CHC proof (verified safe via CHC induction)
# - CTREX: Expect counterexample to be found
# - UNKNOWN: Solver may return unknown (acceptable for complex tests)
# - BMC_SAFE: Accept BMC "no counterexample found" as sufficient
extract_expected_outcome() {
    local file="$1"
    local harness="${2:-}"
    local harness_upper expect_line directive

    harness_upper=$(printf '%s' "$harness" | tr '[:lower:]' '[:upper:]')

    if [[ -n "$harness" ]]; then
        while IFS= read -r expect_line; do
            directive=$(echo "$expect_line" | sed 's|.*kani-expect:||' | tr -s ' ' | sed 's/^ *//;s/ *$//' | tr '[:lower:]' '[:upper:]')
            if [[ "$directive" == "${harness_upper}="* ]]; then
                echo "${directive#*=}"
                return 0
            fi
        done < <(head -50 "$file" 2>/dev/null | grep "^// *kani-expect:")
    fi

    while IFS= read -r expect_line; do
        directive=$(echo "$expect_line" | sed 's|.*kani-expect:||' | tr -s ' ' | sed 's/^ *//;s/ *$//' | tr '[:lower:]' '[:upper:]')
        if [[ "$directive" != *=* ]]; then
            echo "$directive"
            return 0
        fi
    done < <(head -50 "$file" 2>/dev/null | grep "^// *kani-expect:")
}

# Detect rustc compilation errors in output (Part of #1739, Cluster H D1).
# Returns 0 (true) if the output contains rustc error patterns that indicate
# the compiler failed before the verifier could run.
has_rustc_errors() {
    local output="$1"
    printf '%s\n' "$output" | grep -qE '^error(\[[A-Z0-9]+\])?:|^error: aborting due to'
}

# Detect artifact/path lookup failures that abort before any final verifier
# marker is emitted. Keep these distinct from generic rustc errors so report
# consumers can route them to infra instead of semantic compiler queues.
has_artifact_path_errors() {
    local output="$1"
    printf '%s\n' "$output" | grep -qE \
        'No such file or directory \(os error 2\)|Failed to process |Failed to read CHC SMT file:|\.symtab\.(out|smt2)'
}

extract_final_verification_outcome() {
    local output="$1"
    local final_marker
    final_marker=$(printf '%s\n' "$output" | grep -oE '\[AY:(PROOF|CTREX|UNKNOWN|ERROR)\]' | tail -n1)
    case "$final_marker" in
        "[AY:PROOF]") echo "PROOF" ;;
        "[AY:CTREX]") echo "CTREX" ;;
        "[AY:UNKNOWN]") echo "UNKNOWN" ;;
        "[AY:ERROR]") echo "ERROR" ;;
        *) echo "" ;;
    esac
}

has_unknown_result_markers() {
    local output="$1"
    printf '%s\n' "$output" | grep -qE '\[AY:UNKNOWN_(QUALITY|REASON):|\[AY:CTREX_CAT:Unknown\]'
}

unknown_result_details() {
    local output="$1"
    local reason
    reason=$(printf '%s\n' "$output" | grep -oE '\[AY:UNKNOWN_REASON:[^]]+\]' | tail -n1 | sed 's/\[AY:UNKNOWN_REASON://;s/\]//')
    if [[ -n "$reason" ]]; then
        printf 'unknown_marker=%s\n' "$reason"
    else
        printf 'unknown_marker\n'
    fi
}

has_memory_pressure_cleanup() {
    local output="$1"
    printf '%s\n' "$output" | grep -Fq "[trust-mc] Memory pressure cleanup:"
}

is_trusted_bmc_completion() {
    local output="$1"
    local file="${2:-}"
    local harness="${3:-}"

    [[ -z "$file" ]] && return 1
    if [[ -n "$(extract_final_verification_outcome "$output")" ]]; then
        return 1
    fi
    has_memory_pressure_cleanup "$output" && return 1
    has_artifact_path_errors "$output" && return 1
    has_rustc_errors "$output" && return 1
    if ! requires_bmc_mode "$file" "$harness"; then
        return 1
    fi
    return 0
}

has_bmc_failed_checks() {
    local output="$1"
    printf '%s\n' "$output" | grep -Fq "VERIFICATION:- FAILED" || return 1
    printf '%s\n' "$output" | grep -qE 'Status: FAILURE|^Failed Checks:'
}

is_trusted_bmc_counterexample() {
    local output="$1"
    local file="${2:-}"
    local harness="${3:-}"

    [[ -z "$file" ]] && return 1
    if [[ -n "$(extract_final_verification_outcome "$output")" ]]; then
        return 1
    fi
    has_memory_pressure_cleanup "$output" && return 1
    has_artifact_path_errors "$output" && return 1
    has_rustc_errors "$output" && return 1
    if ! requires_bmc_mode "$file" "$harness"; then
        return 1
    fi
    has_bmc_failed_checks "$output"
}

get_execution_provenance() {
    local output="$1"
    local file="${2:-}"
    local harness="${3:-}"
    local final_outcome
    final_outcome=$(extract_final_verification_outcome "$output")
    if [[ -n "$final_outcome" ]]; then
        printf 'complete\tfinal_marker=%s\n' "$final_outcome"
        return
    fi
    if has_memory_pressure_cleanup "$output"; then
        printf 'watchdog_cleanup\tmemory_pressure_cleanup\n'
        return
    fi
    if has_artifact_path_errors "$output"; then
        printf 'missing_verdict\tartifact_path_error\n'
        return
    fi
    if has_rustc_errors "$output"; then
        printf 'missing_verdict\trustc_error\n'
        return
    fi
    if has_unknown_result_markers "$output"; then
        printf 'complete\t%s\n' "$(unknown_result_details "$output")"
        return
    fi
    if is_trusted_bmc_completion "$output" "$file" "$harness"; then
        printf 'complete\texplicit_bmc_lane\n'
        return
    fi
    printf 'missing_verdict\tno_final_marker\n'
}

# Get actual verification outcome from test output (Part of #1755, #2054).
# Uses final-marker strategy (matching parse_provenance) to avoid misclassification
# when ay-chc retries with alternative engines (#2052).
# Returns: PROOF, CTREX, UNKNOWN, ERROR, or BMC (explicit bounded-safe lane only).
get_actual_outcome() {
    local output="$1"
    local file="${2:-}"
    local harness="${3:-}"
    local final_outcome
    final_outcome=$(extract_final_verification_outcome "$output")
    if [[ -n "$final_outcome" ]]; then
        echo "$final_outcome"
    elif has_rustc_errors "$output"; then
        echo "ERROR"
    elif has_artifact_path_errors "$output"; then
        echo "ERROR"
    elif has_memory_pressure_cleanup "$output"; then
        echo "ERROR"
    elif has_unknown_result_markers "$output"; then
        echo "UNKNOWN"
    elif is_trusted_bmc_counterexample "$output" "$file" "$harness"; then
        echo "CTREX"
    elif is_trusted_bmc_completion "$output" "$file" "$harness"; then
        echo "BMC"
    else
        echo "ERROR"
    fi
}

# Check if actual outcome matches expected (Part of #1755, #2054).
# Returns 0 if matches, 1 if mismatch.
# - BMC_SAFE expectation accepts both BMC and PROOF
# - PROOF expectation requires actual PROOF (not BMC)
# - ERROR never matches any positive expectation
check_outcome_matches() {
    local expected="$1"
    local actual="$2"
    local execution_state="${3:-complete}"
    local effective_success_reason="${4:-}"

    # ERROR is always a mismatch against any positive expectation
    if [[ "$actual" == "ERROR" && "$expected" != "ERROR" ]]; then
        return 1
    fi

    # Part of #3315: execution-gated or no-marker runs never satisfy positive
    # proof or bounded-safe expectations.
    if [[ "$execution_state" != "complete" && "$expected" != "ERROR" ]]; then
        return 1
    fi

    case "$expected" in
        PROOF)
            # Accept BMC as equivalent to PROOF: BMC verified-safe is proof.
            # Part of #3688: BMC lane files produce BMC verdicts, not PROOF.
            [[ "$actual" == "PROOF" || "$actual" == "BMC" ]] && return 0
            [[ "$actual" == "CTREX" && -n "$effective_success_reason" ]]
            ;;
        CTREX)
            [[ "$actual" == "CTREX" ]]
            ;;
        UNKNOWN)
            [[ "$actual" == "UNKNOWN" ]]
            ;;
        ERROR)
            [[ "$actual" == "ERROR" ]]
            ;;
        BMC_SAFE)
            # BMC_SAFE accepts BMC pass or actual PROOF
            [[ "$actual" == "BMC" || "$actual" == "PROOF" ]]
            ;;
        *)
            # No expectation set, accept anything
            return 0
            ;;
    esac
}

harness_default_expectation() {
    local file="$1"
    local harness="${2:-}"
    lane_policy_default_expectation "$file" "$harness"
}

# Counters for proof requirement tracking (Part of #1755)
harness_outcome_mismatch=0
harness_missing_expectation=0

# CHC is default; BMC routing comes from tests/ay/lane_policy.toml.
requires_chc_mode() {
    local file="$1"
    local harness="${2:-}"
    if requires_bmc_mode "$file" "$harness"; then
        return 1  # Use BMC, not CHC
    fi
    return 0  # Default: use CHC for proofs
}

requires_bmc_mode() {
    local file="$1"
    local harness="${2:-}"
    if ! resolve_lane_policy "$file" "$harness"; then
        return 1
    fi
    [[ "$CURRENT_LANE" == "bmc" ]]
}

# Check if a harness in a file is expected to fail.
# Returns 0 (true) if harness-level OR file-level expected failure.
is_expected_fail() {
    local file="$1"
    local harness="$2"
    is_expected_fail_harness "$harness" || is_expected_fail_file "$file"
}

extract_proof_harnesses() {
    local file="$1"
    "${AY_PYTHON_BIN:-python3}" "$SCRIPT_DIR/extract_proof_harnesses.py" "$file"
}
