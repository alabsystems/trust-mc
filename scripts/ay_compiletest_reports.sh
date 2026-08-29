#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Report/schema helper module for ay-compiletest.sh (Part of #3892).
# Sourced by scripts/ay-compiletest.sh — do not run standalone.

_ay_compiletest_reports_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
source "$_ay_compiletest_reports_dir/ay_compiletest_report_authority.sh"

ay_compiletest_report_dir() {
    if [[ -n "${AY_REPORT_DIR:-}" ]]; then
        if [[ "$AY_REPORT_DIR" = /* ]]; then
            printf '%s\n' "$AY_REPORT_DIR"
        else
            printf '%s\n' "$TRUST_MC_DIR/$AY_REPORT_DIR"
        fi
    else
        printf '%s\n' "$TRUST_MC_DIR/reports"
    fi
}

ay_compiletest_report_path() {
    local report_name="$1"
    printf '%s/%s\n' "$(ay_compiletest_report_dir)" "$report_name"
}

ay_compiletest_report_display_path() {
    local report_path="$1"
    if [[ "$report_path" == "$TRUST_MC_DIR/"* ]]; then
        printf '%s\n' "${report_path#"$TRUST_MC_DIR"/}"
    else
        printf '%s\n' "$report_path"
    fi
}

normalize_harness_record_file() {
    local file="$1"
    local rel_file="$file"
    if [[ "$rel_file" == "$TRUST_MC_DIR/tests/"* ]]; then
        rel_file="${rel_file#"$TRUST_MC_DIR"/tests/}"
    elif [[ "$rel_file" == "tests/"* ]]; then
        rel_file="${rel_file#tests/}"
    fi
    printf '%s\n' "$rel_file"
}

harness_record_path_exists_in_worktree_or_head() {
    local rel_file="$1"
    [[ -n "$rel_file" ]] || return 1
    [[ -f "$TRUST_MC_DIR/tests/$rel_file" ]] && return 0
    git -C "$TRUST_MC_DIR" cat-file -e "HEAD:tests/$rel_file" 2>/dev/null
}

validate_rendered_harness_report_liveness() {
    local report_file="$1"
    local rel_file paths_file missing=0
    paths_file=$(mktemp "${TMPDIR:-/tmp}/harness_report_paths.XXXXXX")
    if ! jq -r '.harnesses[]?.file // empty' "$report_file" | sort -u > "$paths_file"; then
        rm -f "$paths_file"
        echo -e "${RED}ERROR${NC}: failed to enumerate harness report paths for liveness validation" >&2
        return 1
    fi

    while IFS= read -r rel_file; do
        [[ -n "$rel_file" ]] || continue
        if ! harness_record_path_exists_in_worktree_or_head "$rel_file"; then
            echo -e "${RED}ERROR${NC}: harness report references missing live test path tests/$rel_file" >&2
            missing=1
        fi
    done < "$paths_file"

    rm -f "$paths_file"
    [[ $missing -eq 0 ]]
}

validate_report_commit() {
    local commit="$1"
    [[ "$commit" =~ ^[0-9a-fA-F]{40}$ ]]
}

report_marked_non_replacement() {
    case "${AY_REPORT_NON_REPLACEMENT:-}" in
        1|true|TRUE|yes|YES)
            return 0
            ;;
        *)
            return 1
            ;;
    esac
}

ay_pin_marked_non_replacement() {
    local ay_pin="$1"
    [[ "$ay_pin" =~ ^[0-9a-fA-F]{40}-(dirty|local|dirty-local)$ ]]
}

report_is_non_replacement() {
    local ay_pin="$1"
    report_marked_non_replacement || ay_pin_marked_non_replacement "$ay_pin"
}

validate_report_ay_pin() {
    local ay_pin="$1"
    [[ "$ay_pin" =~ ^[0-9a-fA-F]{40}$ ]] && return 0
    report_is_non_replacement "$ay_pin"
}

build_translation_drop_reasons_json() {
    local translation_drop_reasons="${1:-}"
    jq -cn --arg csv "$translation_drop_reasons" '
        reduce ($csv | split(",")[]?) as $pair
            ({};
                if $pair == "" then
                    .
                else
                    ($pair | split("=")) as $parts
                    | if ($parts | length) == 2 and $parts[0] != "" and ($parts[1] | test("^[0-9]+$")) then
                        . + { ($parts[0]): ($parts[1] | tonumber) }
                      else
                        .
                      end
                end
            )
    '
}

build_csv_string_array_json() {
    local csv="${1:-}"
    jq -cn --arg csv "$csv" '[$csv | split(",")[]? | select(. != "")]'
}

format_runtime_seconds() {
    local start="${1:-}" end="${2:-}"
    if [[ -z "$start" || -z "$end" ]]; then
        printf '0'
        return
    fi
    awk -v start="$start" -v end="$end" 'BEGIN {
        delta = end - start;
        if (delta < 0) {
            delta = 0;
        }
        printf "%.3f", delta;
    }'
}

build_harness_metadata_json() {
    local retried="${1:-false}" ctrex_cat="${2:-}" sound_fallback="${3:-}" unknown_quality="${4:-}" unknown_reason="${5:-}" proof_qualifiers="${6:-}" demotion_reasons="${7:-}" translation_drop_reasons="${8:-}" execution_state="${9:-}" execution_details="${10:-}" retry_attempts="${11:-}" retry_resolved_by="${12:-}" retry_final="${13:-}" runtime_seconds="${14:-}" retry_recursive="${15:-}" retry_relation_count="${16:-}" inferable_summaries="${17:-}"
    local ctrex_label="$ctrex_cat" ctrex_details=""
    local quality_label="$unknown_quality" quality_details=""
    local sound_fallback_num=0
    local demotion_reasons_json="[]"
    local translation_drop_json="{}"
    local inferable_summaries_json="{}"

    if [[ -n "$retry_recursive" && "$retry_recursive" != "true" && "$retry_recursive" != "false" ]]; then
        echo "invalid retry_recursive: $retry_recursive" >&2
        return 1
    fi

    if [[ -n "$ctrex_cat" ]]; then
        ctrex_label="${ctrex_cat%%:*}"
        ctrex_details="${ctrex_cat#*:}"
        if [[ "$ctrex_details" == "$ctrex_label" ]]; then
            ctrex_details=""
        fi
    fi

    if [[ -n "$unknown_quality" ]]; then
        quality_label="${unknown_quality%%:*}"
        quality_details="${unknown_quality#*:}"
        if [[ "$quality_details" == "$quality_label" ]]; then
            quality_details=""
        fi
    fi

    if [[ -n "$sound_fallback" && "$sound_fallback" =~ ^[0-9]+$ && "$sound_fallback" -gt 0 ]]; then
        sound_fallback_num="$sound_fallback"
    fi

    if ! demotion_reasons_json=$(build_csv_string_array_json "$demotion_reasons"); then
        return 1
    fi

    if ! translation_drop_json=$(build_translation_drop_reasons_json "$translation_drop_reasons"); then
        return 1
    fi

    # Part of #4078: reuse the same CSV→JSON converter for inferable summaries.
    if ! inferable_summaries_json=$(build_translation_drop_reasons_json "$inferable_summaries"); then
        return 1
    fi

    jq -cn \
        --arg retried "$retried" \
        --arg ctrex_label "$ctrex_label" \
        --arg ctrex_details "$ctrex_details" \
        --arg quality_label "$quality_label" \
        --arg quality_details "$quality_details" \
        --arg unknown_reason "$unknown_reason" \
        --arg proof_qualifiers "$proof_qualifiers" \
        --argjson demotion_reasons_json "$demotion_reasons_json" \
        --arg execution_state "$execution_state" \
        --arg execution_details "$execution_details" \
        --arg retry_attempts "$retry_attempts" \
        --arg retry_resolved_by "$retry_resolved_by" \
        --arg retry_final "$retry_final" \
        --arg runtime_seconds "$runtime_seconds" \
        --arg retry_recursive "$retry_recursive" \
        --arg retry_relation_count "$retry_relation_count" \
        --argjson sound_fallback_num "$sound_fallback_num" \
        --argjson translation_drop_json "$translation_drop_json" \
        --argjson inferable_summaries_json "$inferable_summaries_json" '
            {}
            + (if $retried == "true" then {retried: true} else {} end)
            + (if $ctrex_label != "" then {
                ctrex: (
                    {category: $ctrex_label}
                    + (if $ctrex_details != "" then {details: $ctrex_details} else {} end)
                )
            } else {} end)
            + (if $sound_fallback_num > 0 then {sound_fallback_count: $sound_fallback_num} else {} end)
            + (if $quality_label != "" then {
                unknown: (
                    {quality: $quality_label}
                    + (if $quality_details != "" then {details: $quality_details} else {} end)
                    + (if $unknown_reason != "" then {reason: $unknown_reason} else {} end)
                )
            } elif $unknown_reason != "" then {
                unknown: {reason: $unknown_reason}
            } else {} end)
            + (if $proof_qualifiers != "" then {proof_qualifiers: $proof_qualifiers} else {} end)
            + (if ($demotion_reasons_json | length) > 0 then {demotion: {reasons: $demotion_reasons_json}} else {} end)
            + (if ($translation_drop_json | length) > 0 then {translation_drop_reasons: $translation_drop_json} else {} end)
            + (if ($inferable_summaries_json | length) > 0 then {inferable_summaries: $inferable_summaries_json} else {} end)
            + (if $execution_state != "" then {
                execution: (
                    {state: $execution_state}
                    + (if $execution_details != "" then {details: $execution_details} else {} end)
                )
            } else {} end)
            + (if ($retry_attempts != "" or $retry_resolved_by != "" or $retry_final != "" or $retry_recursive != "" or $retry_relation_count != "") then {
                retry: (
                    {}
                    + (if $retry_attempts != "" then {attempts: $retry_attempts} else {} end)
                    + (if $retry_resolved_by != "" then {resolved_by: $retry_resolved_by} else {} end)
                    + (if $retry_final != "" then {final_outcome: $retry_final} else {} end)
                    + (if $retry_recursive != "" then {recursive: ($retry_recursive == "true")} else {} end)
                    + (if $retry_relation_count != "" then {relation_count: ($retry_relation_count | tonumber)} else {} end)
                )
            } else {} end)
            + (if $runtime_seconds != "" then {
                runtime: {seconds: ($runtime_seconds | tonumber)}
            } else {} end)
        '
}

legacy_retry_attempted() {
    local output="${1:-}"
    printf '%s\n' "$output" | grep -Eq '\[AY:RETRY\] (Trying strategy [0-9]+/[0-9]+|Non-recursive CHC system detected\.|CHC solver (failed|crashed on retry)\. Trying BMC engine as last resort\.\.\.|BMC-on-crash resolved)'
}

extract_retry_progress_attempts() {
    local output="${1:-}"
    printf '%s\n' "$output" \
        | grep -oE '\[AY:RETRY_ATTEMPT:[^]]+\]' \
        | sed 's/\[AY:RETRY_ATTEMPT://;s/\]//' \
        | paste -sd, -
}

extract_retry_context_fields() {
    local output="${1:-}" retry_context retry_recursive="" retry_relation_count=""
    retry_context=$(printf '%s\n' "$output" | grep -oE '\[AY:RETRY_CONTEXT:[^]]+\]' | tail -n1 | sed 's/\[AY:RETRY_CONTEXT://;s/\]//')
    if [[ "$retry_context" =~ (^|,)recursive=(true|false)($|,) ]]; then
        retry_recursive="${BASH_REMATCH[2]}"
    fi
    if [[ "$retry_context" =~ (^|,)relations=([0-9]+)($|,) ]]; then
        retry_relation_count="${BASH_REMATCH[2]}"
    fi
    printf '%s|%s\n' "$retry_recursive" "$retry_relation_count"
}

extract_retry_metadata_fields() {
    local output="${1:-}" final_retry_attempts progress_retry_attempts retry_attempts retry_resolved_by retry_final retry_recursive retry_relation_count retry_context_fields retried="false"
    final_retry_attempts=$(printf '%s\n' "$output" | grep -oE '\[AY:RETRY_ATTEMPTS:[^]]+\]' | tail -n1 | sed 's/\[AY:RETRY_ATTEMPTS://;s/\]//')
    progress_retry_attempts=$(extract_retry_progress_attempts "$output")
    if [[ -n "$final_retry_attempts" ]]; then
        retry_attempts="$final_retry_attempts"
    else
        retry_attempts="$progress_retry_attempts"
    fi
    retry_resolved_by=$(printf '%s\n' "$output" | grep -oE '\[AY:RETRY_RESOLVED_BY:[^]]+\]' | tail -n1 | sed 's/\[AY:RETRY_RESOLVED_BY://;s/\]//')
    retry_final=$(printf '%s\n' "$output" | grep -oE '\[AY:RETRY_FINAL:[^]]+\]' | tail -n1 | sed 's/\[AY:RETRY_FINAL://;s/\]//')
    retry_context_fields=$(extract_retry_context_fields "$output")
    retry_recursive="${retry_context_fields%%|*}"
    retry_relation_count="${retry_context_fields#*|}"
    if [[ -n "$retry_attempts" || -n "$retry_resolved_by" || -n "$retry_final" || -n "$retry_recursive" || -n "$retry_relation_count" ]] || legacy_retry_attempted "$output"; then
        retried="true"
    fi
    # Use a non-whitespace delimiter so empty middle fields survive `read`.
    printf '%s|%s|%s|%s|%s|%s\n' "$retried" "$retry_attempts" "$retry_resolved_by" "$retry_final" "$retry_recursive" "$retry_relation_count"
}

extract_effective_success_reason() {
    local output="${1:-}"
    printf '%s\n' "$output" | grep -oE '\[AY:EFFECTIVE_SUCCESS:[^]]+\]' | tail -n1 | sed 's/\[AY:EFFECTIVE_SUCCESS://;s/\]//'
}

harness_record_jq_prelude() {
    cat <<'JQ'
def is_known_fp:
  .status == "KNOWN_FP";
def is_trusted_proof:
  .verdict == "PROOF" and ((.status // "PASS") == "PASS");
def valid_unknown_quality($q):
  $q == "Clean" or $q == "EncodingGap" or $q == "OverApproximation" or $q == "Mixed";
def valid_unknown_reason($r):
  $r == "Timeout" or $r == "RoundingModeBlock" or $r == "SolverError" or $r == "Unclassified";
def valid_demotion_reason($r):
  ($r | type) == "string" and ($r | test("^[^=]+=[0-9]+$"));
def valid_retry_resolved_by($r):
  $r == "bmc_first_non_recursive" or $r == "no_global" or $r == "extended_timeout" or $r == "bmc_engine" or $r == "exhausted";
def valid_retry_final($r):
  $r == "PROOF" or $r == "CTREX" or $r == "UNKNOWN";
def allows_unknown_quality:
  .metadata.ctrex.category? == "Unknown" and (.verdict == "CTREX" or .verdict == "UNKNOWN");
def sanitize_record:
  # Strip metadata fields incompatible with the current verdict.
  # This handles cases where the driver emits demotion/unknown metadata
  # but the verdict changes (e.g., contention causes PROOF->UNKNOWN).
  (if .metadata.demotion? != null and (.verdict != "PROOF" or .status != "FAIL") then
    .metadata |= del(.demotion)
  else . end)
  | (if (.metadata.unknown.quality? != null or .metadata.unknown.details? != null or .metadata.unknown.reason? != null) and (allows_unknown_quality | not) then
    .metadata |= del(.unknown)
  else . end)
  | (if .metadata.proof_qualifiers? != null and .verdict != "PROOF" then
    .metadata |= del(.proof_qualifiers)
  else . end);
def validate_record($schema):
  if (.schema_version // null) != $schema then
    error("schema_version mismatch for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif ((.metadata // null) | type) != "object" then
    error("metadata must be an object for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.proof_qualifiers? != null and .verdict != "PROOF") then
    error("proof_qualifiers present on non-PROOF row: " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.demotion? != null and (.metadata.demotion | type) != "object") then
    error("demotion metadata must be an object for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.demotion.reasons? != null and (.metadata.demotion.reasons | type) != "array") then
    error("demotion.reasons must be an array for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.demotion? != null and (.verdict != "PROOF" or .status != "FAIL")) then
    error("demotion metadata present outside demoted PROOF row: " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif any(.metadata.demotion.reasons[]?; valid_demotion_reason(.) | not) then
    error("invalid demotion.reasons entry for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.unknown.details? != null and .metadata.unknown.quality? == null) then
    error("unknown_details present without unknown_quality for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif ((.metadata.unknown.quality? != null or .metadata.unknown.details? != null or .metadata.unknown.reason? != null) and (allows_unknown_quality | not)) then
    error("unknown metadata present outside Unknown ctrex lane: " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif ((.metadata.execution.state? // "") | startswith("final_marker=")) then
    error("execution.state misrouted final marker for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.unknown.quality? != null and (valid_unknown_quality(.metadata.unknown.quality) | not)) then
    error("invalid unknown_quality label for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring) + ": " + ((.metadata.unknown.quality // "?") | tostring))
  elif (.metadata.unknown.reason? != null and (valid_unknown_reason(.metadata.unknown.reason) | not)) then
    error("invalid unknown_reason label for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring) + ": " + ((.metadata.unknown.reason // "?") | tostring))
  elif (.metadata.retry? != null and .metadata.retried != true) then
    error("retry metadata present without retried=true for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.retry.resolved_by? != null and (valid_retry_resolved_by(.metadata.retry.resolved_by) | not)) then
    error("invalid retry.resolved_by label for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring) + ": " + ((.metadata.retry.resolved_by // "?") | tostring))
  elif (.metadata.retry.final_outcome? != null and (valid_retry_final(.metadata.retry.final_outcome) | not)) then
    error("invalid retry.final_outcome label for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring) + ": " + ((.metadata.retry.final_outcome // "?") | tostring))
  elif (.metadata.retry.recursive? != null and ((.metadata.retry.recursive | type) != "boolean")) then
    error("invalid retry.recursive for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.retry.relation_count? != null and (((.metadata.retry.relation_count | type) != "number") or .metadata.retry.relation_count < 0 or ((.metadata.retry.relation_count | floor) != .metadata.retry.relation_count))) then
    error("invalid retry.relation_count for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  elif (.metadata.runtime.seconds? != null and (((.metadata.runtime.seconds | type) != "number") or .metadata.runtime.seconds < 0)) then
    error("invalid runtime.seconds for " + ((.file // "?") | tostring) + "::" + ((.harness // "?") | tostring))
  else
    .
  end;
def harness_row:
  {
    file,
    harness,
    verdict,
    status,
    expected,
    sound_fallback_count: (.metadata.sound_fallback_count? // 0)
  }
  + (if is_known_fp then {known_fp: true} else {} end)
  + (if is_trusted_proof then {trusted_proof: true} else {} end)
  + (if .metadata.retried == true then {retried: true} else {} end)
  + (if .metadata.ctrex.category? != null then {ctrex_category: .metadata.ctrex.category} else {} end)
  + (if .metadata.ctrex.details? != null then {ctrex_details: .metadata.ctrex.details} else {} end)
  + (if .metadata.unknown.quality? != null then {unknown_quality: .metadata.unknown.quality} else {} end)
  + (if .metadata.unknown.details? != null then {unknown_details: .metadata.unknown.details} else {} end)
  + (if .metadata.unknown.reason? != null then {unknown_reason: .metadata.unknown.reason} else {} end)
  + (if .metadata.proof_qualifiers? != null then {proof_qualifiers: .metadata.proof_qualifiers} else {} end)
  + (if (.metadata.demotion.reasons? // []) | length > 0 then {demotion_reasons: .metadata.demotion.reasons} else {} end)
  + {translation_drop_reasons: (.metadata.translation_drop_reasons? // {})}
  + (if .metadata.execution.state? != null then {execution_state: .metadata.execution.state} else {} end)
  + (if .metadata.execution.details? != null then {execution_details: .metadata.execution.details} else {} end)
  + (if .metadata.retry.attempts? != null then {retry_attempts: .metadata.retry.attempts} else {} end)
  + (if .metadata.retry.resolved_by? != null then {retry_resolved_by: .metadata.retry.resolved_by} else {} end)
  + (if .metadata.retry.final_outcome? != null then {retry_final: .metadata.retry.final_outcome} else {} end)
  + (if .metadata.retry.recursive? != null then {retry_recursive: .metadata.retry.recursive} else {} end)
  + (if .metadata.retry.relation_count? != null then {retry_relation_count: .metadata.retry.relation_count} else {} end)
  + (if .metadata.runtime.seconds? != null then {time_sec: .metadata.runtime.seconds} else {} end);
JQ
}

validate_harness_records_file() {
    local records_file="${1:-$HARNESS_RECORDS_FILE}"
    local jq_lib
    jq_lib="$(harness_record_jq_prelude)"
    jq -e --argjson schema "$HARNESS_RECORD_SCHEMA_VERSION" "${jq_lib}
validate_record(\$schema) | true
" "$records_file" >/dev/null
}

render_per_harness_json_report() {
    local output_file="$1"
    local trust_mc_commit ay_pin replacement_evidence run_date jq_lib jq_filter tmp_output_file report_tree_state report_tree_fingerprint solver_binary_attestation
    trust_mc_commit=$(git -C "$TRUST_MC_DIR" rev-parse HEAD 2>/dev/null || echo "unknown")
    if ! validate_report_commit "$trust_mc_commit"; then
        echo -e "${RED}ERROR${NC}: failed to resolve full 40-character git commit for per-harness JSON report (got '$trust_mc_commit')" >&2
        return 1
    fi
    ay_pin=$(get_ay_commit)
    if report_is_non_replacement "$ay_pin"; then
        replacement_evidence="false"
    else
        replacement_evidence="true"
    fi
    if ! validate_report_ay_pin "$ay_pin"; then
        echo -e "${RED}ERROR${NC}: refusing to write replacement-quality per-harness JSON with malformed ay_pin '$ay_pin'; set AY_REPORT_NON_REPLACEMENT=true for non-replacement evidence" >&2
        return 1
    fi
    run_date=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    report_tree_state="$(detect_report_tree_state)"
    report_tree_fingerprint="$(detect_report_tree_fingerprint)"
    if ! solver_binary_attestation="$(build_solver_binary_attestation_json "$AY_SOLVER")"; then
        echo -e "${RED}ERROR${NC}: failed to build solver binary attestation for '$AY_SOLVER'" >&2
        return 1
    fi
    jq_lib="$(harness_record_jq_prelude)"
    jq_filter="$(cat <<'JQ'
map(sanitize_record | validate_record($schema)) as $records
| {
    schema_version: $schema,
    report_status: "current",
    commit: $commit,
    tree_state: $tree_state,
    tree_fingerprint: $tree_fingerprint,
    date: $date,
    ay_pin: $ay_pin,
    replacement_evidence: $replacement_evidence,
    solver: $solver,
    solver_binary: $solver_binary,
    summary: {
      total: ($records | length),
      pass: ([$records[] | select(.status == "PASS")] | length),
      proof: ([$records[] | select(.verdict == "PROOF")] | length),
      known_fp: ([$records[] | select(is_known_fp)] | length),
      trusted_proof: ([$records[] | select(is_trusted_proof)] | length),
      ctrex: ([$records[] | select(.verdict == "CTREX")] | length),
      fail: ([$records[] | select(.status == "FAIL")] | length),
      unknown: ([$records[] | select(.verdict == "UNKNOWN")] | length),
      error: ([$records[] | select(.verdict == "ERROR")] | length),
      bmc: ([$records[] | select(.verdict == "BMC")] | length),
      xfail: ([$records[] | select(.status == "XFAIL")] | length),
      skip: ([$records[] | select(.verdict == "SKIP")] | length),
      ctrex_breakdown: {
        encoding_gap: ([$records[] | select(.metadata.ctrex.category? == "EncodingGap")] | length),
        over_approximation: ([$records[] | select(.metadata.ctrex.category? == "OverApproximation")] | length),
        genuine: ([$records[] | select(.metadata.ctrex.category? == "Genuine")] | length),
        unknown: ([$records[] | select(.metadata.ctrex.category? == "Unknown")] | length)
      },
      proof_breakdown: {
        clean: ([$records[] | select(.metadata.proof_qualifiers? == "clean")] | length),
        should_panic: ([$records[] | select(.metadata.proof_qualifiers? == "should_panic")] | length),
        crosschecked: ([$records[] | select((.metadata.proof_qualifiers? // "") | test("crosschecked="))] | length),
        sound_qualified: ([$records[] | select((.metadata.proof_qualifiers? // "") | test("sound_fallback="))] | length),
        mem_overapprox_qualified: ([$records[] | select((.metadata.proof_qualifiers? // "") | test("kani_mem_overapprox="))] | length)
      },
      execution_complete: ([$records[] | select(.metadata.execution.state? == "complete")] | length),
      execution_gated: ([$records[] | select(.metadata.execution.state? != null and .metadata.execution.state != "complete")] | length),
      execution_breakdown: (
        reduce ($records[] | .metadata.execution.state? // empty) as $state
          ({};
            .[$state] = ((.[$state] // 0) + 1)
          )
      )
    },
    harnesses: ($records | sort_by(.file, .harness) | map(harness_row))
  }
JQ
)"
    tmp_output_file=$(mktemp "${TMPDIR:-/tmp}/harness_report_render.XXXXXX")
    if ! jq -s \
        --arg commit "$trust_mc_commit" \
        --arg tree_state "$report_tree_state" \
        --arg tree_fingerprint "$report_tree_fingerprint" \
        --arg date "$run_date" \
        --arg ay_pin "$ay_pin" \
        --argjson replacement_evidence "$replacement_evidence" \
        --arg solver "$AY_SOLVER" \
        --argjson solver_binary "$solver_binary_attestation" \
        --argjson schema "$HARNESS_RECORD_SCHEMA_VERSION" \
        "${jq_lib}
${jq_filter}
" "$HARNESS_RECORDS_FILE" > "$tmp_output_file"; then
        rm -f "$tmp_output_file"
        echo -e "${RED}ERROR${NC}: failed to write per-harness JSON report from schema-v${HARNESS_RECORD_SCHEMA_VERSION} records" >&2
        return 1
    fi

    if ! validate_rendered_harness_report_liveness "$tmp_output_file"; then
        rm -f "$tmp_output_file"
        return 1
    fi

    mv "$tmp_output_file" "$output_file"
}

render_per_harness_verdict_log() {
    local records_file="${1:-$HARNESS_RECORDS_FILE}"
    local jq_lib
    jq_lib="$(harness_record_jq_prelude)"
    jq -sr --argjson schema "$HARNESS_RECORD_SCHEMA_VERSION" "${jq_lib}
map(sanitize_record | validate_record(\$schema))
| sort_by(.file, .harness)
| .[]
| [
    (.file + \"::\" + .harness),
    .verdict,
    ((((.metadata.runtime.seconds? // 0) * 1000) | round) / 1000 | tostring),
    (.expected // \"\"),
    .status
  ]
| @tsv
" "$records_file"
}

write_per_harness_verdict_log() {
    local default_name="compiletest-per-harness-latest.tsv"
    if [[ -n "${RUN_SCOPE:-}" ]]; then
        default_name="compiletest-per-harness-latest-${RUN_SCOPE}.tsv"
    fi
    local default_file
    default_file="$(ay_compiletest_report_path "$default_name")"
    local output_file="${1:-$default_file}"
    local tmp_output_file
    mkdir -p "$(dirname "$output_file")"
    tmp_output_file=$(mktemp "${TMPDIR:-/tmp}/harness_verdict_log_render.XXXXXX")
    if ! render_per_harness_verdict_log "$HARNESS_RECORDS_FILE" > "$tmp_output_file"; then
        rm -f "$tmp_output_file"
        echo -e "${RED}ERROR${NC}: failed to write per-harness verdict log from schema-v${HARNESS_RECORD_SCHEMA_VERSION} records" >&2
        return 1
    fi
    mv "$tmp_output_file" "$output_file"
}

# Record a per-harness verdict to the schema-versioned JSONL harness record file (Part of #3863).
# Args: $1=file, $2=harness, $3=verdict, $4=status, $5=expected outcome, $6=metadata_json object
record_harness_verdict_v2() {
    local file="$1" harness="$2" verdict="$3" status="$4" expected="${5:-}" metadata_json="${6:-}"
    local rel_file record_json
    if [[ -z "$metadata_json" ]]; then
        metadata_json='{}'
    fi
    rel_file="$(normalize_harness_record_file "$file")"
    if ! record_json=$(jq -cn \
        --argjson schema "$HARNESS_RECORD_SCHEMA_VERSION" \
        --arg file "$rel_file" \
        --arg harness "$harness" \
        --arg verdict "$verdict" \
        --arg status "$status" \
        --arg expected "$expected" \
        --argjson metadata "$metadata_json" \
        '{
            schema_version: $schema,
            file: $file,
            harness: $harness,
            verdict: $verdict,
            status: $status,
            expected: $expected,
            metadata: $metadata
        }'); then
        echo -e "${RED}ERROR${NC}: failed to construct harness record for ${rel_file}::${harness}" >&2
        return 1
    fi
    printf '%s\n' "$record_json" >> "$HARNESS_RECORDS_FILE"
}


# Write per-category JSON results (Part of #1599)
write_category_json() {
    # Part of #3197: Filtered runs use qualified filename (same as per-harness JSON).
    local default_name="compiletest-category-results.json"
    if [[ -n "${RUN_SCOPE:-}" ]]; then
        default_name="compiletest-category-results-${RUN_SCOPE}.json"
    fi
    local default_file
    default_file="$(ay_compiletest_report_path "$default_name")"
    local output_file="${1:-$default_file}" tmp_output_file
    mkdir -p "$(dirname "$output_file")"
    tmp_output_file=$(mktemp "${TMPDIR:-/tmp}/category_results_render.XXXXXX")
    {
        echo "{"
        local first=true
        for category in $(get_all_categories); do
            if [[ "$first" != "true" ]]; then
                echo ","
            fi
            first=false
            local pass fail skip cat_total
            pass=$(get_category_count "$category" pass)
            fail=$(get_category_count "$category" fail)
            skip=$(get_category_count "$category" skip)
            cat_total=$(get_category_count "$category" total)
            printf '  "%s": {"pass": %d, "fail": %d, "skip": %d, "total": %d}' \
                "$category" "$pass" "$fail" "$skip" "$cat_total"
        done
        echo ""
        echo "}"
    } > "$tmp_output_file"

    if ! jq -e '.' "$tmp_output_file" >/dev/null; then
        rm -f "$tmp_output_file"
        echo -e "${RED}ERROR${NC}: failed to write valid category JSON report" >&2
        return 1
    fi

    mv "$tmp_output_file" "$output_file"
}

# Write per-harness verdict JSON (Part of #3181, #3863).
# Reads schema-versioned JSONL records from HARNESS_RECORDS_FILE and emits the
# stable per-harness JSON report used by regressions and tracker tooling.
write_per_harness_json() {
    # Part of #3197: Filtered runs use qualified filename to prevent overwriting
    # full-suite data. RUN_SCOPE is set when CLI args are provided.
    local default_name="compiletest-per-harness-latest.json"
    if [[ -n "${RUN_SCOPE:-}" ]]; then
        default_name="compiletest-per-harness-latest-${RUN_SCOPE}.json"
    fi
    local default_file
    default_file="$(ay_compiletest_report_path "$default_name")"
    local output_file="${1:-$default_file}"
    mkdir -p "$(dirname "$output_file")"
    render_per_harness_json_report "$output_file"
}
