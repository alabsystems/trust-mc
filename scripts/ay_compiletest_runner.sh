#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Execution/scheduling helper module for ay-compiletest.sh (Part of #3892).
# Sourced by scripts/ay-compiletest.sh — do not run standalone.


# Run a single harness within a test file and update global counters.
# Consolidates the per-harness logic that was duplicated across run_all_trust-mc_categories,
# run_ay_dir_tests, and single-file mode (~100 lines each, 3 copies → 1).
# Part of #2209
#
# Args:
#   $1 - test file path
#   $2 - harness name
#   $3 - display label (e.g., "Assert/test.rs" or "test.rs")
#   $4 - category name (optional; if set, update_category is called)

lane_policy_filter_chc_flags() {
    local lane="$1"
    shift

    local flag
    for flag in "$@"; do
        if [[ "$lane" == "bmc" && "$flag" == --ay-chc* ]]; then
            continue
        fi
        printf '%s\n' "$flag"
    done
}

run_single_harness() {
    local file="$1"
    local harness="$2"
    local display_label="$3"
    local category="${4:-}"

    # Check total wall-clock timeout before each harness
    check_total_timeout

    local now_epoch
    now_epoch=$(date +%s)
    local elapsed=$((now_epoch - SCRIPT_START_EPOCH))
    if [[ $elapsed -gt 0 && $((elapsed % 60)) -lt 5 ]]; then
        echo "ay-compiletest: progress ${harness_passed}/${harness_total} passed, ${elapsed}s elapsed, limit ${AY_TOTAL_TIMEOUT}s"
    fi

    local known_hang_issue
    if known_hang_issue=$(known_hang_issue_for_harness "$file" "$harness"); then
        echo -e "Testing: ${display_label}::$harness ... ${YELLOW}SKIP${NC} (known hang #${known_hang_issue})"
        ((harness_skipped++))
        [[ -n "$category" ]] && update_category "$category" skip
        record_harness_verdict_v2 "$file" "$harness" "SKIP" "SKIP" "" '{}' || exit 1
        return
    fi

    ((total++))
    ((harness_total++))
    [[ -n "$category" ]] && update_category "$category" total
    echo -n "Testing: ${display_label}::$harness ... "

    local expected_fail=0
    if is_expected_fail "$file" "$harness"; then
        expected_fail=1
        ((harness_expected_fail++))
    fi

    local file_flags; file_flags=$(extract_kani_flags "$file")
    local compile_flags; compile_flags=$(extract_compile_flags "$file")
    local saved_rustflags="${RUSTFLAGS-}"
    local had_rustflags=0
    if [[ -n "${RUSTFLAGS+x}" ]]; then
        had_rustflags=1
    fi
    if [[ -n "$compile_flags" ]]; then
        # Part of #3766: Pass compile-flags as RUSTFLAGS so the driver forwards
        # them to rustc (see call_single_file.rs:310). Without this, directives
        # like --edition 2018 are silently dropped, causing compilation failures
        # (e.g., AsyncAwait tests fail with "async fn not permitted in Rust 2015").
        export RUSTFLAGS="${RUSTFLAGS:+$RUSTFLAGS }$compile_flags"
        [[ "${VERBOSE:-}" == "1" ]] && echo "  compile-flags: $compile_flags (RUSTFLAGS=$RUSTFLAGS)"
    fi
    if ! prepare_lane_policy_flags "$file" "$harness" "$file_flags"; then
        echo -e "${RED}FAIL${NC} (invalid lane policy)"; ((failed++)); ((harness_failed++))
        [[ -n "$category" ]] && update_category "$category" fail
        record_harness_verdict_v2 "$file" "$harness" "ERROR" "FAIL" "" '{}' || exit 1
        restore_rustflags "$had_rustflags" "$saved_rustflags"
        return
    fi

    # Part of #129: BMC lane must exclude --ay-chc* flags to use direct BMC
    # solver instead of the CHC portfolio.
    local test_flags=()
    local _flag
    while IFS= read -r _flag; do
        test_flags+=("$_flag")
    done < <(lane_policy_filter_chc_flags "$CURRENT_LANE" "${AY_FLAGS[@]}")
    test_flags+=("--harness-timeout=${AY_TEST_TIMEOUT}s" "${LANE_POLICY_EXTRA_FLAGS[@]}")
    if [[ -n "$file_flags" ]]; then
        # shellcheck disable=SC2206
        local parsed_file_flags=($file_flags)
        local file_flag
        while IFS= read -r file_flag; do
            test_flags+=("$file_flag")
        done < <(lane_policy_filter_chc_flags "$CURRENT_LANE" "${parsed_file_flags[@]}")
        [[ "${VERBOSE:-}" == "1" ]] && echo "  kani-flags: $file_flags"
    fi
    [[ "${VERBOSE:-}" == "1" ]] && echo "  $(lane_policy_verbose_note "$file")"

    local expected_outcome missing_expectation=0
    local harness_override
    harness_override=$(get_harness_outcome_override "$harness" 2>/dev/null) || true
    if [[ -n "$harness_override" ]]; then
        # Per-harness override takes precedence over file-level expectation
        expected_outcome="$harness_override"
        # Part of #3360: When override specifies a non-failure outcome (e.g., PROOF),
        # clear expected_fail so the pass/fail logic treats this harness normally.
        # Without this, file-level kani-expect: CTREX sets expected_fail=1,
        # causing overridden PROOF harnesses to be counted as "unexpected success".
        if [[ "$harness_override" != "CTREX" ]]; then
            expected_fail=0
        fi
    else
        expected_outcome=$(extract_expected_outcome "$file" "$harness")
        if [[ -z "$expected_outcome" ]]; then
            expected_outcome=$(harness_default_expectation "$file" "$harness")
            missing_expectation=1
            ((harness_missing_expectation++))
        fi
    fi

    if ! file_flags_specify_harness "$file_flags"; then
        # Part of #3337: Module-qualified names (containing ::) use substring
        # matching because the driver's pretty_name includes the crate prefix
        # (e.g., "anon_static::example_1::main"). With --exact, only full
        # pretty_name or bare function name matches, so "example_1::main"
        # would fail to match either. Substring matching correctly identifies
        # the unique harness.
        if [[ "$harness" == *"::"* ]]; then
            test_flags+=("--harness" "$harness")
        else
            test_flags+=("--harness" "$harness" "--exact")
        fi
    fi

    local kani_output _h_status="FAIL"
    local kani_succeeded=0
    local actual_outcome actual_execution_state actual_execution_details actual_execution_suffix=""
    local actual_effective_success_reason=""
    local harness_start_epoch harness_end_epoch harness_runtime_seconds
    harness_start_epoch="${EPOCHREALTIME:-$(date +%s)}"
    if kani_output=$(run_with_timeout "$(shell_timeout_seconds)" env TRUST_MC_EMIT_EFFECTIVE_SUCCESS_MARKERS=1 "$TRUST_MC_TEST_BIN" "${test_flags[@]}" "$file" 2>&1); then
        kani_succeeded=1
    fi
    harness_end_epoch="${EPOCHREALTIME:-$(date +%s)}"
    harness_runtime_seconds=$(format_runtime_seconds "$harness_start_epoch" "$harness_end_epoch")
    actual_outcome=$(get_actual_outcome "$kani_output" "$file" "$harness")
    IFS=$'\t' read -r actual_execution_state actual_execution_details <<< "$(get_execution_provenance "$kani_output" "$file" "$harness")"
    actual_effective_success_reason=$(extract_effective_success_reason "$kani_output")
    if [[ -n "${actual_execution_state:-}" && "$actual_execution_state" != "complete" ]]; then
        actual_execution_suffix="; execution_state=${actual_execution_state}"
        if [[ -n "${actual_execution_details:-}" ]]; then
            actual_execution_suffix="${actual_execution_suffix} (${actual_execution_details})"
        fi
    fi

    if [[ "$kani_succeeded" -eq 1 ]]; then
        if [[ $expected_fail -eq 1 ]]; then
            # Check if this is a false proof (expected CTREX but got PROOF).
            # Part of #2292: distinguish false proofs from other unexpected successes.
            if [[ "$expected_outcome" == "CTREX" && "$actual_outcome" == "PROOF" ]]; then
                # Part of #3350: Check if this is a known false proof before counting as failure.
                local _fp_issue
                if _fp_issue=$(known_false_proof_issue_for_harness "$file" "$harness"); then
                    echo -e "${YELLOW}KNOWN_FP${NC} (known false proof — $_fp_issue)"
                    ((harness_known_false_proof++))
                    _h_status="KNOWN_FP"
                else
                    echo -e "${RED}FAIL${NC} (false proof — expected CTREX, got PROOF)"
                    ((failed++)); ((harness_failed++)); ((harness_unexpected_pass++))
                    [[ -n "$category" ]] && update_category "$category" fail
                    echo "  FALSE PROOF: solver claims safe but test has known counterexample"
                fi
            else
                echo -e "${RED}FAIL${NC} (unexpected success — XFAIL harness passed)"
                ((failed++)); ((harness_failed++)); ((harness_unexpected_pass++))
                [[ -n "$category" ]] && update_category "$category" fail
                echo "$kani_output" | head -50
            fi
        else
            if [[ $missing_expectation -eq 1 && "${AY_REQUIRE_EXPECT}" == "1" ]]; then
                echo -e "${RED}FAIL${NC} (missing kani-expect)"
                ((failed++)); ((harness_failed++))
                [[ -n "$category" ]] && update_category "$category" fail
                echo "  Missing // kani-expect: annotation in $file"
            else
                if ! check_outcome_matches "$expected_outcome" "$actual_outcome" "$actual_execution_state" "$actual_effective_success_reason"; then
                    echo -e "${RED}FAIL${NC} (expected $expected_outcome, got $actual_outcome${actual_execution_suffix})"
                    ((failed++)); ((harness_failed++)); ((harness_outcome_mismatch++))
                    [[ -n "$category" ]] && update_category "$category" fail
                    echo "  Expected verification outcome: $expected_outcome"
                    echo "  Actual verification outcome: $actual_outcome"
                    if [[ -n "$actual_execution_suffix" ]]; then
                        echo "  Execution provenance: ${actual_execution_state} (${actual_execution_details})"
                    fi
                else
                    echo -e "${GREEN}PASS${NC}"
                    ((passed++)); ((harness_passed++))
                    [[ -n "$category" ]] && update_category "$category" pass
                    [[ "${VERBOSE:-}" == "1" ]] && echo "$kani_output"
                    _h_status="PASS"
                fi
            fi
        fi
    else
        if [[ $expected_fail -eq 1 ]]; then
            if expected_fail_output_matches_harness "$kani_output" "$harness"; then
                echo -e "${GREEN}XFAIL${NC}"
                ((passed++)); ((harness_passed++))
                [[ -n "$category" ]] && update_category "$category" pass
                [[ "${VERBOSE:-}" == "1" ]] && echo "$kani_output"
                _h_status="XFAIL"
            else
                echo -e "${RED}FAIL${NC} (unexpected error)"
                ((failed++)); ((harness_failed++))
                [[ -n "$category" ]] && update_category "$category" fail
                echo "$kani_output" | head -50
            fi
        else
            # Part of #1739: Non-zero exit code with non-XFAIL expectation.
            # The driver exits non-zero for both CTREX and UNKNOWN verdicts,
            # so we must check expected_outcome here too (not just in the
            # exit-code-0 branch). This enables kani-expect: UNKNOWN to pass
            # when the solver returns UNKNOWN and kani-expect: CTREX to pass when
            # the solver finds a counterexample.
            if check_outcome_matches "$expected_outcome" "$actual_outcome" "$actual_execution_state" "$actual_effective_success_reason"; then
                echo -e "${GREEN}PASS${NC}"
                ((passed++)); ((harness_passed++))
                [[ -n "$category" ]] && update_category "$category" pass
                [[ "${VERBOSE:-}" == "1" ]] && echo "$kani_output"
                _h_status="PASS"
            else
                echo -e "${RED}FAIL${NC} (expected $expected_outcome, got $actual_outcome${actual_execution_suffix})"
                ((failed++)); ((harness_failed++))
                [[ -n "$category" ]] && update_category "$category" fail
                echo "$kani_output" | head -50
            fi
        fi
    fi
    parse_provenance "$kani_output" "$file" "$harness" "$actual_effective_success_reason"
    # Record per-harness verdict (Part of #3863).
    local _h_verdict _h_retried _h_ctrex_cat _h_sound_fallback _h_unknown_quality _h_unknown_reason _h_proof_qualifiers _h_demotion_reasons _h_translation_drop_reasons _h_inferable_summaries _h_retry_attempts _h_retry_resolved_by _h_retry_final _h_retry_recursive _h_retry_relation_count _h_retry_metadata_fields _h_metadata_json
    _h_verdict="$actual_outcome"
    # Part of #4099: should_panic + CTREX = PROOF for per-harness records.
    # The CTREX proves the panic is reachable, satisfying the should_panic contract.
    if [[ "$_h_verdict" == "CTREX" && "$actual_effective_success_reason" == "should_panic_panics_only" ]]; then
        _h_verdict="PROOF"
    fi
    # Part of #4041: prefer final retry markers, fall back to incremental
    # progress markers for execution-gated runs, and keep legacy text parsing
    # only as the last compatibility fallback.
    _h_retry_metadata_fields=$(extract_retry_metadata_fields "$kani_output")
    IFS='|' read -r _h_retried _h_retry_attempts _h_retry_resolved_by _h_retry_final _h_retry_recursive _h_retry_relation_count <<< "$_h_retry_metadata_fields"
    # Part of #3314: extract CTREX classification from driver output
    _h_ctrex_cat=$(printf '%s\n' "$kani_output" | grep -oE '\[AY:CTREX_CAT:[^]]+\]' | tail -n1 | sed 's/\[AY:CTREX_CAT://;s/\]//')
    # Part of #3476: extract sound fallback count from driver output
    _h_sound_fallback=$(printf '%s\n' "$kani_output" | grep -oE '\[AY:SOUND_FALLBACK:[0-9]+\]' | tail -n1 | sed 's/\[AY:SOUND_FALLBACK://;s/\]//')
    # Part of #2985: extract UNKNOWN-quality classification from driver output
    _h_unknown_quality=$(printf '%s\n' "$kani_output" | grep -oE '\[AY:UNKNOWN_QUALITY:[^]]+\]' | tail -n1 | sed 's/\[AY:UNKNOWN_QUALITY://;s/\]//')
    _h_unknown_reason=$(printf '%s\n' "$kani_output" | grep -oE '\[AY:UNKNOWN_REASON:[^]]+\]' | tail -n1 | sed 's/\[AY:UNKNOWN_REASON://;s/\]//')
    # Part of #2574: extract proof qualifiers from driver output
    _h_proof_qualifiers=$(printf '%s\n' "$kani_output" | grep -oE '\[AY:PROOF_QUALIFIERS:[^]]+\]' | tail -n1 | sed 's/\[AY:PROOF_QUALIFIERS://;s/\]//')
    # Part of #4099: when should_panic promotes CTREX→PROOF, set proof_qualifiers
    # to "should_panic" so the JSON report shows this was a should_panic proof.
    if [[ "$_h_verdict" == "PROOF" && "$actual_effective_success_reason" == "should_panic_panics_only" ]]; then
        _h_proof_qualifiers="should_panic"
    fi
    _h_demotion_reasons=$(printf '%s\n' "$kani_output" | grep -oE '\[AY:DEMOTION_REASONS:[^]]+\]' | tail -n1 | sed 's/\[AY:DEMOTION_REASONS://;s/\]//')
    _h_translation_drop_reasons=$(collect_translation_drop_reasons_for_harness "$kani_output" "$harness")
    # Part of #4078: collect inferable-summary provenance markers
    _h_inferable_summaries=$(collect_inferable_summaries_for_harness "$kani_output")
    if ! _h_metadata_json=$(build_harness_metadata_json "$_h_retried" "$_h_ctrex_cat" "$_h_sound_fallback" "$_h_unknown_quality" "$_h_unknown_reason" "$_h_proof_qualifiers" "$_h_demotion_reasons" "$_h_translation_drop_reasons" "$actual_execution_state" "$actual_execution_details" "$_h_retry_attempts" "$_h_retry_resolved_by" "$_h_retry_final" "$harness_runtime_seconds" "$_h_retry_recursive" "$_h_retry_relation_count" "$_h_inferable_summaries"); then
        echo -e "${RED}ERROR${NC}: failed to build harness metadata for ${file}::${harness}" >&2
        restore_rustflags "$had_rustflags" "$saved_rustflags"
        exit 1
    fi
    if ! record_harness_verdict_v2 "$file" "$harness" "$_h_verdict" "$_h_status" "$expected_outcome" "$_h_metadata_json"; then
        restore_rustflags "$had_rustflags" "$saved_rustflags"
        exit 1
    fi
    [[ -z "${AY_NO_CLEANUP:-}" ]] && check_artifact_sizes || true

    # Restore RUSTFLAGS after harness run to prevent compile-flags leaking
    # between harness invocations (Part of #3766).
    restore_rustflags "$had_rustflags" "$saved_rustflags"
}

run_compiletest() {
    local suite="$1"
    local mode="$2"
    echo "=== AY compiletest: suite=$suite mode=$mode ==="
    if [[ "${AY_REQUIRE_EXPECT}" == "1" || -n "$AY_MIN_PROOF_RATE" ]]; then
        echo "Note: AY_REQUIRE_EXPECT/AY_MIN_PROOF_RATE apply only to per-harness runs."
    fi

    local verbose_flag=""
    if [[ "${VERBOSE:-}" == "1" ]]; then
        verbose_flag="--verbose"
    fi

    # Run compiletest binary directly to avoid cargo wrapper argument parsing issues.
    # Part of #811: Using cargo run -p compiletest mangles --trust-mc-flag arguments.
    local compiletest_bin
    compiletest_bin="$(target_dir_path)/release/compiletest"
    if [[ ! -x "$compiletest_bin" ]]; then
        echo -e "${RED}ERROR${NC}: compiletest not found at $compiletest_bin"
        if [[ "$SKIP_BUILD" -eq 1 ]]; then
            echo "Run without --skip-build (or set AY_SKIP_BUILD=0) to build compiletest first."
        fi
        ((failed++))
        ((total++))
        ((suite_failed++))
        ((suite_total++))
        return
    fi

    # shellcheck disable=SC2086
    # TRUST_MC_FLAG_ARGS and verbose_flag are intentionally unquoted for word-splitting
    if "$compiletest_bin" \
        --suite "$suite" \
        --mode "$mode" \
        --timeout "$AY_TEST_TIMEOUT" \
        --force-rerun \
        $TRUST_MC_FLAG_ARGS \
        --no-fail-fast \
        ${verbose_flag:+"$verbose_flag"}; then
        echo -e "${GREEN}PASS${NC}: compiletest suite=$suite"
        ((passed++))
        ((suite_passed++))
    else
        echo -e "${RED}FAIL${NC}: compiletest suite=$suite"
        ((failed++))
        ((suite_failed++))
    fi
    ((total++))
    ((suite_total++))
}

# Run all tests in trust-mc categories with per-category tracking (Part of #1599)
run_all_trust-mc_categories() {
    local base_dir="${1:-$TRUST_MC_DIR/tests/trust-mc}"
    echo "=== Running all trust-mc categories ($base_dir/*/) ==="

    if [[ ! -d "$base_dir" ]]; then
        echo -e "${RED}ERROR: Directory not found: $base_dir${NC}"
        return 1
    fi

    local category_count=0
    for category_dir in "$base_dir"/*/; do
        [[ ! -d "$category_dir" ]] && continue

        local category
        category=$(basename "$category_dir")
        ((category_count++))

        echo ""
        echo "=== Category: $category ==="

        while IFS= read -r f; do
            [[ ! -f "$f" ]] && continue

            # Relative path from category dir for disambiguation (e.g., "Atomic/test.rs")
            local rel_path="${f#"$category_dir"}"
            local harnesses=()
            while IFS= read -r h; do
                [[ -n "$h" ]] && harnesses+=("$h")
            done < <(select_proof_harnesses_for_file "$f")

            [[ ${#harnesses[@]} -eq 0 ]] && continue

            for harness in "${harnesses[@]}"; do
                run_single_harness "$f" "$harness" "$category/$rel_path" "$category"
            done
        done < <(find "$category_dir" -name "*.rs" -type f | sort)
    done
    echo "Processed $category_count categories"
}

run_ay_dir_tests() {
    local dir="$1"
    echo "=== AY smoke tests ($dir/*.rs) ==="
    if [[ ! -d "$dir" ]]; then
        echo -e "${RED}WARNING: $dir directory not found${NC}"
        return
    fi

    for f in "$dir"/*.rs; do
        [[ ! -f "$f" ]] && continue

        local test_name
        test_name=$(basename "$f")
        local harnesses=()
        while IFS= read -r harness; do
            [[ -n "$harness" ]] && harnesses+=("$harness")
        done < <(select_proof_harnesses_for_file "$f")

        if [[ ${#harnesses[@]} -eq 0 ]]; then
            echo -e "${RED}WARNING${NC}: No proof harnesses found in $test_name"
            continue
        fi

        for harness in "${harnesses[@]}"; do
            run_single_harness "$f" "$harness" "$test_name"
        done
    done
}
