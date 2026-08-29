#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Clean test artifacts from the tests/trust-mc and tests/ay directories.
#
# The AY backend writes .symtab.smt2 and .vc.json files alongside test sources.
# These files are gitignored but can accumulate and bloat the working tree.
#
# Usage:
#   ./scripts/clean_test_artifacts.sh         # Dry run (show what would be deleted)
#   ./scripts/clean_test_artifacts.sh --force # Actually delete files

set -euo pipefail

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
TRUST_MC_DIR="$SCRIPT_DIR/.."

DRY_RUN=1
if [[ "${1:-}" == "--force" ]] || [[ "${1:-}" == "-f" ]]; then
    DRY_RUN=0
fi

cd "$TRUST_MC_DIR"

echo "=== Clean Test Artifacts ==="
echo ""

# Directories to clean (AY backend writes artifacts alongside test sources)
TEST_DIRS="tests/trust-mc tests/ay"

# Filter to existing directories
EXISTING_DIRS=""
for dir in $TEST_DIRS; do
    if [[ -d "$dir" ]]; then
        EXISTING_DIRS="$EXISTING_DIRS $dir"
    fi
done
EXISTING_DIRS=$(echo "$EXISTING_DIRS" | xargs)  # trim whitespace

if [[ -z "$EXISTING_DIRS" ]]; then
    echo "No test directories found to clean."
    exit 0
fi

# Count and size before
BEFORE_SIZE=$(du -shc $EXISTING_DIRS 2>/dev/null | tail -1 | cut -f1 || echo "0")
echo "Test directories size before: $BEFORE_SIZE"
echo "Scanning: $EXISTING_DIRS"
echo ""

# Find artifacts
# `*.alethe`: ay writes a certificate next to the input on UNSAT. The driver
# never consumes it, and the sites that used to suppress it with
# `--no-proof` no longer do (the flag stopped disabling the tracker and had
# become a net cost), so these accumulate unless swept here.
ARTIFACTS=$(find $EXISTING_DIRS \( -name "*.symtab.smt2" -o -name "*.vc.json" -o -name "*.alethe" -o -name "*.alethe.tmp-*" \) -type f 2>/dev/null || true)

if [[ -z "$ARTIFACTS" ]]; then
    echo "No artifacts to clean."
    exit 0
fi

# Count and show size
COUNT=$(echo "$ARTIFACTS" | wc -l | tr -d ' ')
# Use null delimiter for safety with special filenames
ARTIFACT_SIZE=$(echo "$ARTIFACTS" | tr '\n' '\0' | xargs -0 du -ch 2>/dev/null | tail -1 | cut -f1 || echo "0")

echo "Found $COUNT artifact files totaling $ARTIFACT_SIZE"
echo ""

# Show large files (>10MB) from the already-found artifacts
echo "Large files (>10MB):"
LARGE_FILES=$(echo "$ARTIFACTS" | while read f; do
    if [[ -f "$f" ]] && [[ $(stat -f%z "$f" 2>/dev/null || stat -c%s "$f" 2>/dev/null || echo 0) -gt 10485760 ]]; then
        ls -lh "$f"
    fi
done)
if [[ -n "$LARGE_FILES" ]]; then
    echo "$LARGE_FILES" | while read line; do echo "  $line"; done
else
    echo "  (none)"
fi
echo ""

if [[ $DRY_RUN -eq 1 ]]; then
    echo "[DRY RUN] Would delete $COUNT files."
    echo ""
    echo "Run with --force to actually delete:"
    echo "  ./scripts/clean_test_artifacts.sh --force"
else
    echo "Deleting $COUNT files..."
    # Use xargs with null delimiter for safety with special filenames
    echo "$ARTIFACTS" | tr '\n' '\0' | xargs -0 rm -f 2>/dev/null || true

    AFTER_SIZE=$(du -shc $EXISTING_DIRS 2>/dev/null | tail -1 | cut -f1 || echo "0")
    echo ""
    echo "Test directories size after: $AFTER_SIZE"
    echo "Done."
fi
