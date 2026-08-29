#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Author: Andrew Yates <andrewyates.name@gmail.com>
# Part of #3476: Extract and document 0-fallback PROOF harnesses from compiletest reports.
#
# Usage:
#   ./scripts/zero_fallback_canary.sh [--allow-stale-report] [report.json]
#   ./scripts/zero_fallback_canary.sh --generate [--allow-stale-report]
#
# A harness is "zero-fallback" when:
#   1. verdict == "PROOF"
#   2. sound_fallback_count is absent or 0
#
# These harnesses represent the strongest verification results: exact semantics
# verified without any over-approximation. They serve as regression canaries —
# if a zero-fallback harness later develops fallbacks, encoding quality regressed.

set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$SCRIPT_DIR/ay_python.sh"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

OUTPUT="${ZERO_FALLBACK_CANARY_OUTPUT:-$REPO_ROOT/reports/zero-fallback-canary-harnesses.json}"
ALLOW_STALE_REPORT=0
GENERATE_REPORT=0
REPORT=""

usage() {
    cat <<EOF
Usage:
  ./scripts/zero_fallback_canary.sh [--allow-stale-report] [report.json]
  ./scripts/zero_fallback_canary.sh --generate [--allow-stale-report]
EOF
}

while [[ $# -gt 0 ]]; do
    case "$1" in
        --allow-stale-report)
            ALLOW_STALE_REPORT=1
            ;;
        --generate)
            GENERATE_REPORT=1
            ;;
        -h|--help)
            usage
            exit 0
            ;;
        --*)
            echo "ERROR: Unknown option: $1" >&2
            usage >&2
            exit 2
            ;;
        *)
            if [[ -n "$REPORT" ]]; then
                echo "ERROR: Unexpected extra argument: $1" >&2
                usage >&2
                exit 2
            fi
            REPORT="$1"
            ;;
    esac
    shift
done

if [[ $GENERATE_REPORT -eq 1 && -n "$REPORT" ]]; then
    echo "ERROR: --generate does not accept an explicit report path" >&2
    usage >&2
    exit 2
fi

REPORT="${REPORT:-$REPO_ROOT/reports/compiletest-per-harness-latest-trust-mc.json}"

if [[ $GENERATE_REPORT -eq 1 ]]; then
    echo "=== Generating measurement with sound_fallback_count ==="
    echo "Running full trust-mc suite..."
    AY_SOLVER=auto AY_TEST_TIMEOUT=30 AY_ALLOW_DIRTY=1 \
        "$SCRIPT_DIR/ay-compiletest.sh" trust-mc
    REPORT="$REPO_ROOT/reports/compiletest-per-harness-latest-trust-mc.json"
fi

if [[ ! -f "$REPORT" ]]; then
    echo "ERROR: Report not found: $REPORT" >&2
    exit 1
fi

"${AY_PYTHON_BIN:-python3}" - "$SCRIPT_DIR" "$REPORT" "$OUTPUT" "$ALLOW_STALE_REPORT" <<'PYTHON'
import json
import sys
from datetime import datetime, timezone
from pathlib import Path

script_dir = Path(sys.argv[1])
report_path = Path(sys.argv[2])
output_path = Path(sys.argv[3])
allow_stale_report = sys.argv[4] == "1"

sys.path.insert(0, str(script_dir))
from compiletest_report_contract import load_schema_v2_report

try:
    data = load_schema_v2_report(
        report_path,
        repo_root=script_dir.parent,
        require_current_head=not allow_stale_report,
    )
except (ValueError, json.JSONDecodeError) as exc:
    raise SystemExit(f"ERROR: {exc}") from exc

harnesses = data["harnesses"]

def is_trusted_proof(h):
    return h.get("verdict") == "PROOF" and h.get("status", "PASS") == "PASS"

# Extract zero-fallback PROOF harnesses
zero_fb = []
nonzero_fb = []
for h in harnesses:
    if not is_trusted_proof(h):
        continue
    sfb = h.get("sound_fallback_count", 0)
    entry = {
        "file": h["file"],
        "harness": h["harness"],
        "sound_fallback_count": sfb,
    }
    if sfb == 0:
        zero_fb.append(entry)
    else:
        nonzero_fb.append(entry)

# Build output document
output = {
    "description": "Zero-fallback PROOF canary harnesses — strongest verification results",
    "generated_from": str(report_path),
    "source_commit": data.get("commit", "unknown"),
    "source_tree_state": data.get("tree_state", "unknown"),
    "ay_pin": data.get("ay_pin", "unknown"),
    "generated_at": datetime.now(timezone.utc).isoformat(),
    "summary": {
        "total_proof": len(zero_fb) + len(nonzero_fb),
        "zero_fallback_proof": len(zero_fb),
        "nonzero_fallback_proof": len(nonzero_fb),
    },
    "zero_fallback_harnesses": sorted(zero_fb, key=lambda x: (x["file"], x["harness"])),
}

if nonzero_fb:
    output["nonzero_fallback_harnesses"] = sorted(
        nonzero_fb, key=lambda x: (-x["sound_fallback_count"], x["file"], x["harness"])
    )

with open(output_path, "w", encoding="utf-8") as f:
    json.dump(output, f, indent=2)
    f.write("\n")

print(f"=== Zero-Fallback PROOF Canary Report ===")
print(f"Source: {report_path}")
print(f"Commit: {data.get('commit', 'unknown')}")
print(f"Tree state: {data.get('tree_state', 'unknown')}")
print(f"AY pin: {data.get('ay_pin', 'unknown')}")
print(f"Total PROOF: {len(zero_fb) + len(nonzero_fb)}")
print(f"  Zero-fallback (strongest): {len(zero_fb)}")
print(f"  Nonzero-fallback (weaker): {len(nonzero_fb)}")
if nonzero_fb:
    print(f"\nTop 10 harnesses by fallback count:")
    for h in sorted(nonzero_fb, key=lambda x: -x["sound_fallback_count"])[:10]:
        print(f"  {h['sound_fallback_count']:3d} fallbacks: {h['harness']} ({h['file']})")
print(f"\nOutput: {output_path}")
PYTHON

echo ""
echo "Canary list written to: $OUTPUT"
echo "Use 'jq .summary' to view counts, 'jq '.zero_fallback_harnesses[] | .harness'' for the list."
