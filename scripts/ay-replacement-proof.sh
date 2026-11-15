#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
#
# Fail-closed proof runner for a completed AY-only replacement report.

set -euo pipefail

usage() {
    cat <<'EOF'
Usage:
  scripts/ay-replacement-proof.sh \
    --expected-ay-pin <40-hex> \
    --expected-commit <40-hex> \
    --expected-tree-fingerprint <64-hex> \
    --expected-harnesses <N> \
    --expected-inventory-sha <64-hex> \
    [--inventory tests/trust-mc/replacement-harness-inventory.proof.json] \
    [--closure-inventory tests/trust-mc/replacement-harness-inventory.json] \
    [--non-proof-closure reports/non-proof-closure-latest-trust-mc.json] \
    [--expected-non-proof-closure-sha <64-hex>] \
    [--report reports/compiletest-per-harness-proof-latest-trust-mc.json]

This script audits an existing clean, current, AY-only proof report with
tools/replacement-audit and independently checks the proof-only frozen harness
inventory. It does not generate a report. Expected commit, AY pin, denominator,
tree fingerprint, and inventory row digest are always explicit. The live ay
binary and the report's solver_binary attestation must identify a commit
matching --expected-ay-pin. The report's exact TrustMC driver path, binary
digest, current clean commit, and linked-AY authority are re-attested live.
The replacement audit is always run with
--summary-mode kani-compatible. When --non-proof-closure is provided,
--expected-non-proof-closure-sha is required and must match the closure JSON
SHA-256 digest. Source-bound inactive proof rows receive zero credit. Rows UPSTREAM KANI
disabled because CBMC could not run them are outside the replacement bar and
reported as supersession candidates; any row WE disable is local_inactive and
still blocks the strict proof until it is activated and proved.

--expected-harnesses and --expected-inventory-sha name the FROZEN historical
PROOF denominator (the whole proof authority). The proof REPORT is checked
against the BAR instead: the active PROOF rows of the checked source
disposition, whose count and row digest are derived here and printed on the
authority line. The two differ by exactly the upstream-inactive rows.
EOF
}

die() {
    echo "ay-replacement-proof: ERROR: $*" >&2
    exit 1
}

require_command() {
    command -v "$1" >/dev/null 2>&1 || die "required command not found: $1"
}

is_full_hex_pin() {
    [[ "$1" =~ ^[0-9a-fA-F]{40}$ ]]
}

is_positive_integer() {
    [[ "$1" =~ ^[1-9][0-9]*$ ]]
}

is_sha256_hex() {
    [[ "$1" =~ ^[0-9a-fA-F]{64}$ ]]
}

is_solver_commit_hex() {
    [[ "$1" =~ ^[0-9a-fA-F]{7,40}$ ]]
}

solver_commit_matches_expected_pin() {
    local solver_commit="$1"
    local expected_pin="$2"
    solver_commit="$(printf '%s' "$solver_commit" | tr '[:upper:]' '[:lower:]')"
    expected_pin="$(printf '%s' "$expected_pin" | tr '[:upper:]' '[:lower:]')"
    is_solver_commit_hex "$solver_commit" && [[ "$expected_pin" == "$solver_commit"* ]]
}

extract_solver_binary_commit_from_version() {
    local version_output="${1:-}"
    local commit
    commit=$(printf '%s\n' "$version_output" | sed -n 's/^build\.commit=\([0-9a-fA-F]\{7,40\}\).*$/\1/p' | head -n 1)
    if [[ -n "$commit" ]]; then
        printf '%s\n' "$commit"
        return 0
    fi
    printf '%s\n' "$version_output" | sed -n 's/.*[.+]\([0-9a-fA-F]\{7,40\}\)@.*/\1/p' | head -n 1
}

require_solver_commit_matches_expected_pin() {
    local source="$1"
    local solver_commit="$2"
    [[ -n "$solver_commit" ]] \
        || die "$source solver binary commit attestation is missing"
    solver_commit_matches_expected_pin "$solver_commit" "$EXPECTED_AY_PIN" \
        || die "$source solver binary commit $solver_commit does not match expected AY pin $EXPECTED_AY_PIN"
}

require_live_solver_binary_attestation() {
    local solver_binary_path solver_version solver_commit
    # The driver runs $TRUST_MC_AY_BIN in preference to PATH; attest that one.
    solver_binary_path="${TRUST_MC_AY_BIN:-$(command -v ay 2>/dev/null || true)}"
    [[ -n "$solver_binary_path" ]] || die "ay solver binary not found in PATH (TRUST_MC_AY_BIN unset)"

    if ! solver_version="$("$solver_binary_path" --version 2>&1)"; then
        die "unable to read ay solver binary version from $solver_binary_path"
    fi
    [[ -n "$solver_version" ]] \
        || die "unable to read ay solver binary version from $solver_binary_path"

    solver_commit="$(extract_solver_binary_commit_from_version "$solver_version")"
    require_solver_commit_matches_expected_pin "live ay at $solver_binary_path" "$solver_commit"
}

require_report_solver_binary_attestation() {
    local solver_binary_name solver_binary_path solver_binary_version solver_binary_commit
    solver_binary_name="$(jq -r '.solver_binary.name // empty' "$REPORT")"
    solver_binary_path="$(jq -r '.solver_binary.path // empty' "$REPORT")"
    solver_binary_version="$(jq -r '.solver_binary.version // empty' "$REPORT")"
    solver_binary_commit="$(jq -r '.solver_binary.commit // empty' "$REPORT")"

    [[ "$solver_binary_name" == "ay" ]] \
        || die "report solver_binary.name $solver_binary_name does not identify ay"
    [[ -n "$solver_binary_path" ]] \
        || die "report solver_binary.path attestation is missing"
    [[ -n "$solver_binary_version" ]] \
        || die "report solver_binary.version attestation is missing"
    require_solver_commit_matches_expected_pin "report" "$solver_binary_commit"
}

require_report_driver_binary_attestation() {
    if ! env \
        PYTHONPATH="$TRUST_MC_DIR/scripts" \
        REPORT="$REPORT" \
        EXPECTED_COMMIT="$EXPECTED_COMMIT" \
        EXPECTED_AY_PIN="$EXPECTED_AY_PIN" \
        "${AY_PYTHON_BIN:-python3}" - <<'PY'
import json
import os
from pathlib import Path

from driver_binary_attestation import attest_driver_binary

report = json.loads(Path(os.environ["REPORT"]).read_text(encoding="utf-8"))
recorded = report.get("driver_binary")
if not isinstance(recorded, dict):
    raise SystemExit("report driver_binary attestation is missing")
path = recorded.get("path")
if not isinstance(path, str) or not path:
    raise SystemExit("report driver_binary.path is missing")
live = attest_driver_binary(
    Path(path),
    expected_trust_mc_sha=os.environ["EXPECTED_COMMIT"].lower(),
    expected_ay_pin=os.environ["EXPECTED_AY_PIN"].lower(),
)
if live != recorded:
    raise SystemExit("live TrustMC driver attestation differs from report")
PY
    then
        die "report TrustMC driver binary cannot be re-attested live"
    fi
}

require_canonical_public_inventories() {
    local generator canonical_non_proof disposition_generator disposition_report
    local local_inactive_rows active_rows active_sha
    generator="$TRUST_MC_DIR/tools/replacement-inventory/generate_inventory.py"
    canonical_non_proof="$TRUST_MC_DIR/tests/trust-mc/non-proof-closure.json"
    disposition_generator="$TRUST_MC_DIR/scripts/replacement_harness_dispositions.py"
    disposition_report="$TRUST_MC_DIR/tests/trust-mc/replacement-harness-dispositions.json"
    [[ -f "$generator" ]] || die "missing canonical inventory generator: $generator"
    [[ -f "$disposition_generator" ]] \
        || die "missing source-bound disposition generator: $disposition_generator"
    [[ -f "$disposition_report" ]] \
        || die "missing source-bound disposition report: $disposition_report"
    if ! "${AY_PYTHON_BIN:-python3}" "$generator" \
        --check \
        --output "$CLOSURE_INVENTORY" \
        --proof-output "$INVENTORY" \
        --non-proof-output "$canonical_non_proof"; then
        die "replacement inventories do not match the committed public-corpus authority"
    fi
    ACTIVE_PROOF_INVENTORY="$(mktemp "${TMPDIR:-/tmp}/trust-mc-active-proof-inventory.XXXXXX")"
    if ! "${AY_PYTHON_BIN:-python3}" "$disposition_generator" \
        --check \
        --inventory "$CLOSURE_INVENTORY" \
        --proof-inventory "$INVENTORY" \
        --non-proof-closure "$canonical_non_proof" \
        --output "$disposition_report" \
        --emit-active-proof-inventory "$ACTIVE_PROOF_INVENTORY"; then
        die "replacement source dispositions do not match source or canonical inventories"
    fi
    # The replacement BAR is what the INCUMBENT DOES. A PROOF row upstream Kani
    # itself disabled — because CBMC could not run it — is not something Kani
    # does, so it cannot block a REPLACEMENT claim; it stays in the 818-row
    # historical denominator and is reported as a supersession candidate.
    # Anything WE disable is `local_inactive` and still blocks, which is the
    # anti-cheat: the bar must never shrink because we switched a row off.
    local_inactive_rows="$(jq -er '.summary.proof.local_inactive' "$disposition_report")"
    if [[ "$local_inactive_rows" != "0" ]]; then
        jq -r '.rows[]
               | select(.expected == "PROOF" and .disposition == "inactive"
                        and (.inactive_origin // "local") != "upstream")
               | "  locally disabled: \(.file)::\(.harness)"' \
            "$disposition_report" >&2 || true
        die "strict replacement proof is blocked by $local_inactive_rows LOCALLY-disabled PROOF rows; upstream-disabled rows are excluded from the bar, ours are not"
    fi
    UPSTREAM_INACTIVE_ROWS="$(jq -er '.summary.proof.upstream_inactive' "$disposition_report")"
    PROOF_BAR="$(jq -er '.summary.proof.bar' "$disposition_report")"
    is_positive_integer "$PROOF_BAR" \
        || die "source dispositions do not report a usable PROOF bar"
    # The audit denominator is the BAR, so its inventory must be the ACTIVE
    # PROOF subset. It is re-derived from the artifact just checked against
    # source, and its digest must equal the digest that artifact recorded.
    ACTIVE_PROOF_INVENTORY_SHA="$(jq -er '.summary.proof.active_inventory_row_sha256' "$disposition_report")"
    is_sha256_hex "$ACTIVE_PROOF_INVENTORY_SHA" \
        || die "source dispositions do not report an active PROOF row digest"
    active_sha="$(jq -er '.row_sha256' "$ACTIVE_PROOF_INVENTORY")"
    [[ "$active_sha" == "$ACTIVE_PROOF_INVENTORY_SHA" ]] \
        || die "derived active PROOF inventory digest $active_sha does not match the checked plan $ACTIVE_PROOF_INVENTORY_SHA"
    active_rows="$(jq -er '.denominator' "$ACTIVE_PROOF_INVENTORY")"
    [[ "$active_rows" == "$PROOF_BAR" ]] \
        || die "derived active PROOF inventory has $active_rows rows; the bar is $PROOF_BAR"
    printf 'replacement bar: %s PROOF rows of %s historical (%s upstream-disabled rows excluded as supersession candidates, zero credit)\n' \
        "$PROOF_BAR" "$EXPECTED_HARNESSES" "$UPSTREAM_INACTIVE_ROWS"
}

report_bar_field() {
    jq -er ".replacement_bar | $1" "$REPORT" \
        || die "proof report has no usable replacement_bar $1; re-run scripts/extract_replacement_proof_report.py"
}

require_report_replacement_bar() {
    # The proof report must declare the SAME narrowing this gate just derived,
    # so a packet extracted against a different plan cannot be audited here.
    local historical bar upstream local_inactive active_sha named
    historical="$(report_bar_field '.historical')"
    bar="$(report_bar_field '.bar')"
    upstream="$(report_bar_field '.upstream_inactive_zero_credit')"
    local_inactive="$(report_bar_field '.local_inactive')"
    active_sha="$(report_bar_field '.active_inventory_row_sha256')"
    named="$(report_bar_field '.upstream_inactive_rows | length')"
    [[ "$historical" == "$EXPECTED_HARNESSES" ]] \
        || die "report replacement_bar.historical $historical does not match expected $EXPECTED_HARNESSES"
    [[ "$bar" == "$PROOF_BAR" ]] \
        || die "report replacement_bar.bar $bar does not match the checked bar $PROOF_BAR"
    [[ "$upstream" == "$UPSTREAM_INACTIVE_ROWS" ]] \
        || die "report replacement_bar.upstream_inactive_zero_credit $upstream does not match the checked $UPSTREAM_INACTIVE_ROWS"
    [[ "$named" == "$UPSTREAM_INACTIVE_ROWS" ]] \
        || die "report names $named upstream-inactive rows; the checked plan has $UPSTREAM_INACTIVE_ROWS"
    [[ "$local_inactive" == "0" ]] \
        || die "report replacement_bar.local_inactive is $local_inactive; locally disabled rows stay inside the bar"
    [[ "$active_sha" == "$ACTIVE_PROOF_INVENTORY_SHA" ]] \
        || die "report replacement_bar.active_inventory_row_sha256 $active_sha does not match the checked $ACTIVE_PROOF_INVENTORY_SHA"
    (( bar + upstream == historical )) \
        || die "report replacement_bar arithmetic is not $historical = $bar + $upstream"
}

run_replacement_closure_check() {
    local output
    if ! output="$(
        "$TRUST_MC_TARGO" --unverified run --manifest-path "$TRUST_MC_DIR/tools/replacement-audit/Cargo.toml" --locked --quiet \
            --bin replacement-closure-check -- \
            --inventory "$CLOSURE_INVENTORY" \
            --non-proof-closure "$NON_PROOF_CLOSURE" \
            --expected-non-proof-closure-sha "$EXPECTED_NON_PROOF_CLOSURE_SHA"
    )"; then
        die "replacement closure check rejected non-proof closure"
    fi

    ACTUAL_NON_PROOF_CLOSURE_SHA="$(
        printf '%s\n' "$output" \
            | sed -n 's/.*non_proof_closure_sha=\([0-9a-fA-F]\{64\}\).*/\1/p' \
            | head -n 1 \
            | tr '[:upper:]' '[:lower:]'
    )"
    [[ -n "$ACTUAL_NON_PROOF_CLOSURE_SHA" ]] \
        || die "replacement closure check did not report non-proof closure sha256"
}

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
TRUST_MC_DIR="$(cd "$SCRIPT_DIR/.." >/dev/null 2>&1 && pwd)"

REPORT="$TRUST_MC_DIR/reports/compiletest-per-harness-proof-latest-trust-mc.json"
INVENTORY="$TRUST_MC_DIR/tests/trust-mc/replacement-harness-inventory.proof.json"
CLOSURE_INVENTORY="$TRUST_MC_DIR/tests/trust-mc/replacement-harness-inventory.json"
NON_PROOF_CLOSURE=""
EXPECTED_NON_PROOF_CLOSURE_SHA=""
EXPECTED_COMMIT=""
EXPECTED_AY_PIN=""
EXPECTED_TREE_FINGERPRINT=""
EXPECTED_HARNESSES=""
EXPECTED_INVENTORY_SHA=""
PROOF_BAR=""
UPSTREAM_INACTIVE_ROWS=""
ACTIVE_PROOF_INVENTORY=""
ACTIVE_PROOF_INVENTORY_SHA=""

cleanup() {
    if [[ -n "${ACTIVE_PROOF_INVENTORY:-}" ]]; then
        rm -f "$ACTIVE_PROOF_INVENTORY"
    fi
}
trap cleanup EXIT

while [[ $# -gt 0 ]]; do
    case "$1" in
        --report)
            [[ $# -ge 2 ]] || die "--report requires a path"
            REPORT="$2"
            shift 2
            ;;
        --expected-commit)
            [[ $# -ge 2 ]] || die "--expected-commit requires a value"
            EXPECTED_COMMIT="$2"
            shift 2
            ;;
        --expected-ay-pin)
            [[ $# -ge 2 ]] || die "--expected-ay-pin requires a value"
            EXPECTED_AY_PIN="$2"
            shift 2
            ;;
        --expected-tree-fingerprint)
            [[ $# -ge 2 ]] || die "--expected-tree-fingerprint requires a value"
            EXPECTED_TREE_FINGERPRINT="$2"
            shift 2
            ;;
        --expected-harnesses)
            [[ $# -ge 2 ]] || die "--expected-harnesses requires a value"
            EXPECTED_HARNESSES="$2"
            shift 2
            ;;
        --expected-inventory-sha)
            [[ $# -ge 2 ]] || die "--expected-inventory-sha requires a value"
            EXPECTED_INVENTORY_SHA="$2"
            shift 2
            ;;
        --inventory)
            [[ $# -ge 2 ]] || die "--inventory requires a path"
            INVENTORY="$2"
            shift 2
            ;;
        --closure-inventory)
            [[ $# -ge 2 ]] || die "--closure-inventory requires a path"
            CLOSURE_INVENTORY="$2"
            shift 2
            ;;
        --non-proof-closure)
            [[ $# -ge 2 ]] || die "--non-proof-closure requires a path"
            NON_PROOF_CLOSURE="$2"
            shift 2
            ;;
        --expected-non-proof-closure-sha)
            [[ $# -ge 2 ]] || die "--expected-non-proof-closure-sha requires a value"
            EXPECTED_NON_PROOF_CLOSURE_SHA="$2"
            shift 2
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        *)
            usage >&2
            die "unknown argument: $1"
            ;;
    esac
done

# Help is repository documentation and must not require a provisioned Python
# or Trust toolchain. Resolve executing-mode prerequisites only after parsing.
source "$SCRIPT_DIR/ay_python.sh"

case "${AY_REPORT_NON_REPLACEMENT:-}" in
    1|true|TRUE|yes|YES)
        die "AY_REPORT_NON_REPLACEMENT is set; replacement proof must use replacement evidence"
        ;;
esac

case "${AY_REQUIRE_EXPECT:-1}" in
    0|false|FALSE|no|NO)
        die "AY_REQUIRE_EXPECT disables explicit expectations"
        ;;
esac

TRUST_MC_TARGO="$("$SCRIPT_DIR/resolve-trust-tool.sh" targo)"
require_command git
require_command jq
require_command python3
require_command ay

[[ -f "$REPORT" ]] || die "report does not exist: $REPORT"
[[ -f "$INVENTORY" ]] || die "inventory does not exist: $INVENTORY"
if [[ -n "$NON_PROOF_CLOSURE" ]]; then
    [[ -f "$NON_PROOF_CLOSURE" ]] || die "non-proof closure does not exist: $NON_PROOF_CLOSURE"
    [[ -f "$CLOSURE_INVENTORY" ]] || die "closure inventory does not exist: $CLOSURE_INVENTORY"
elif [[ -n "$EXPECTED_NON_PROOF_CLOSURE_SHA" ]]; then
    die "--expected-non-proof-closure-sha requires --non-proof-closure"
fi
[[ -f "$TRUST_MC_DIR/tools/replacement-audit/Cargo.toml" ]] \
    || die "missing tools/replacement-audit/Cargo.toml"

[[ -n "$EXPECTED_COMMIT" ]] || die "missing --expected-commit"
[[ -n "$EXPECTED_AY_PIN" ]] || die "missing --expected-ay-pin"
[[ -n "$EXPECTED_TREE_FINGERPRINT" ]] || die "missing --expected-tree-fingerprint"
[[ -n "$EXPECTED_HARNESSES" ]] || die "missing --expected-harnesses"
[[ -n "$EXPECTED_INVENTORY_SHA" ]] || die "missing --expected-inventory-sha"

is_full_hex_pin "$EXPECTED_COMMIT" \
    || die "--expected-commit must be a 40-character hex commit"
is_full_hex_pin "$EXPECTED_AY_PIN" \
    || die "--expected-ay-pin must be a 40-character hex pin"
is_sha256_hex "$EXPECTED_TREE_FINGERPRINT" \
    || die "--expected-tree-fingerprint must be a 64-character hex digest"
is_positive_integer "$EXPECTED_HARNESSES" \
    || die "--expected-harnesses must be a positive integer"
is_sha256_hex "$EXPECTED_INVENTORY_SHA" \
    || die "--expected-inventory-sha must be a 64-character hex digest"

ACTUAL_NON_PROOF_CLOSURE_SHA=""
if [[ -n "$NON_PROOF_CLOSURE" ]]; then
    [[ -n "$EXPECTED_NON_PROOF_CLOSURE_SHA" ]] \
        || die "missing --expected-non-proof-closure-sha for --non-proof-closure"
    is_sha256_hex "$EXPECTED_NON_PROOF_CLOSURE_SHA" \
        || die "--expected-non-proof-closure-sha must be a 64-character hex digest"
    EXPECTED_NON_PROOF_CLOSURE_SHA="$(printf '%s' "$EXPECTED_NON_PROOF_CLOSURE_SHA" | tr '[:upper:]' '[:lower:]')"
fi

ACTUAL_HEAD="$(git -C "$TRUST_MC_DIR" rev-parse HEAD)"
[[ "$ACTUAL_HEAD" == "$EXPECTED_COMMIT" ]] \
    || die "--expected-commit $EXPECTED_COMMIT does not match current HEAD $ACTUAL_HEAD"

ACTUAL_CARGO_AY_PIN="$(
    env PYTHONPATH="$TRUST_MC_DIR/scripts" TRUST_MC_DIR="$TRUST_MC_DIR" "${AY_PYTHON_BIN:-python3}" - <<'PY'
import os
import sys
from pathlib import Path
from ay_manifest_pin import expected_ay_pin_from_cargo_toml
sys.stdout.write(expected_ay_pin_from_cargo_toml(Path(os.environ["TRUST_MC_DIR"])))
PY
)"
[[ "$ACTUAL_CARGO_AY_PIN" == "$EXPECTED_AY_PIN" ]] \
    || die "--expected-ay-pin $EXPECTED_AY_PIN does not match Cargo.toml pin $ACTUAL_CARGO_AY_PIN"

if ! env PYTHONPATH="$TRUST_MC_DIR/scripts" REPORT="$REPORT" TRUST_MC_DIR="$TRUST_MC_DIR" "${AY_PYTHON_BIN:-python3}" - <<'PY'
import os
from pathlib import Path
from compiletest_report_contract import load_schema_v2_report
load_schema_v2_report(
    Path(os.environ["REPORT"]),
    repo_root=Path(os.environ["TRUST_MC_DIR"]),
    require_current_head=True,
)
PY
then
    die "report is not current clean replacement evidence for this checkout"
fi

require_live_solver_binary_attestation
require_report_solver_binary_attestation
require_report_driver_binary_attestation

require_canonical_public_inventories
if [[ -n "$NON_PROOF_CLOSURE" ]]; then
    run_replacement_closure_check
fi

# The frozen historical PROOF authority: unchanged by the narrowing.
ACTUAL_INVENTORY_HARNESSES="$(jq -er '.denominator' "$INVENTORY")"
[[ "$ACTUAL_INVENTORY_HARNESSES" == "$EXPECTED_HARNESSES" ]] \
    || die "inventory denominator $ACTUAL_INVENTORY_HARNESSES does not match expected $EXPECTED_HARNESSES"

ACTUAL_INVENTORY_SHA="$(jq -er '.row_sha256' "$INVENTORY")"
[[ "$ACTUAL_INVENTORY_SHA" == "$EXPECTED_INVENTORY_SHA" ]] \
    || die "inventory row_sha256 $ACTUAL_INVENTORY_SHA does not match expected $EXPECTED_INVENTORY_SHA"

# The proof report carries the BAR. The excluded rows are not missing evidence:
# they are accounted in the 818-row report with zero credit, and the extractor
# refuses to drop one that is absent or credited there.
ACTUAL_HARNESSES="$(jq -er '.harnesses | length' "$REPORT")"
is_positive_integer "$ACTUAL_HARNESSES" \
    || die "report harness count is missing or zero"

if [[ "$ACTUAL_HARNESSES" != "$PROOF_BAR" ]]; then
    die "harness denominator mismatch: proof report has $ACTUAL_HARNESSES, replacement bar is $PROOF_BAR ($EXPECTED_HARNESSES historical PROOF rows less $UPSTREAM_INACTIVE_ROWS upstream-disabled)"
fi

require_report_replacement_bar

"${AY_PYTHON_BIN:-python3}" "$TRUST_MC_DIR/scripts/zero_fallback_proof_gate.py" \
    --expected-ay-pin "$EXPECTED_AY_PIN" \
    --expected-harnesses "$PROOF_BAR" \
    "$REPORT" \
    || die "zero-fallback proof gate rejected replacement proof report"

AUTHORITY_LINE="ay-replacement-proof: authority report=$REPORT inventory=$INVENTORY commit=$EXPECTED_COMMIT ay_pin=$EXPECTED_AY_PIN tree_fingerprint=$EXPECTED_TREE_FINGERPRINT harnesses=$EXPECTED_HARNESSES inventory_sha=$EXPECTED_INVENTORY_SHA proof_bar=$PROOF_BAR upstream_inactive=$UPSTREAM_INACTIVE_ROWS active_inventory_sha=$ACTIVE_PROOF_INVENTORY_SHA"
if [[ -n "$NON_PROOF_CLOSURE" ]]; then
    AUTHORITY_LINE="$AUTHORITY_LINE non_proof_closure=$NON_PROOF_CLOSURE non_proof_closure_sha=$ACTUAL_NON_PROOF_CLOSURE_SHA"
fi
echo "$AUTHORITY_LINE audit_summary_mode=kani-compatible"

AUDIT_ARGS=(
    --expected-commit "$EXPECTED_COMMIT" \
    --expected-ay-pin "$EXPECTED_AY_PIN" \
    --expected-tree-fingerprint "$EXPECTED_TREE_FINGERPRINT" \
    --expected-harnesses "$PROOF_BAR" \
    --expected-inventory-sha "$ACTIVE_PROOF_INVENTORY_SHA" \
    --inventory "$ACTIVE_PROOF_INVENTORY" \
    --summary-mode kani-compatible \
    "$REPORT"
)

if [[ -n "$NON_PROOF_CLOSURE" ]]; then
    AUDIT_ARGS=(
        --non-proof-closure "$NON_PROOF_CLOSURE"
        --closure-inventory "$CLOSURE_INVENTORY"
        "${AUDIT_ARGS[@]}"
    )
fi

"$TRUST_MC_TARGO" --unverified run --manifest-path "$TRUST_MC_DIR/tools/replacement-audit/Cargo.toml" --locked --quiet -- \
    "${AUDIT_ARGS[@]}"

OK_LINE="ay-replacement-proof: OK report=$REPORT inventory=$INVENTORY commit=$EXPECTED_COMMIT ay_pin=$EXPECTED_AY_PIN tree_fingerprint=$EXPECTED_TREE_FINGERPRINT harnesses=$EXPECTED_HARNESSES inventory_sha=$EXPECTED_INVENTORY_SHA proof_bar=$PROOF_BAR upstream_inactive=$UPSTREAM_INACTIVE_ROWS active_inventory_sha=$ACTIVE_PROOF_INVENTORY_SHA"
if [[ -n "$NON_PROOF_CLOSURE" ]]; then
    OK_LINE="$OK_LINE non_proof_closure=$NON_PROOF_CLOSURE non_proof_closure_sha=$ACTUAL_NON_PROOF_CLOSURE_SHA"
fi
echo "$OK_LINE audit_summary_mode=kani-compatible"
