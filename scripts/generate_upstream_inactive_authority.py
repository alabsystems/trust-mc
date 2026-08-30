#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Freeze the PROOF rows that UPSTREAM KANI itself disabled.

A replacement claim is bounded by what the INCUMBENT DOES. A harness upstream
Kani switched off — because CBMC could not run it — is not something Kani does,
so it cannot sit inside the replacement bar. It is not deleted either: it stays
in the 818-row historical denominator and becomes an explicit SUPERSESSION
target, a place trust-mc may BEAT Kani.

PROVENANCE IS PROVED, NOT ASSERTED. Eligibility is decided against the initial
fork commit, never against the working tree: a row qualifies only if it was
already `#[cfg(disabled)]` in Kani's own source at that commit. Trusting whatever
is disabled today would let anyone widen the exclusion by disabling a row now,
which is the exact cheat the frozen denominator exists to prevent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]

# The commit that imported Kani's corpus into this fork. Provenance is decided
# HERE, so a later local edit cannot manufacture an exclusion.
FORK_COMMIT = "c4d858036"

CFG_DISABLED_RE = re.compile(r"#\[\s*cfg\s*\(\s*disabled\s*\)\s*\]")
PROOF_ATTR_RE = re.compile(r"#\[\s*kani\s*::\s*proof")
FN_RE = re.compile(r"^\s*(?:pub\s+)?(?:async\s+)?fn\s+([A-Za-z0-9_]+)")
REASON_RE = re.compile(r"#\[\s*cfg\s*\(\s*disabled\s*\)\s*\]\s*//\s*(.+?)\s*$")

# Only these upstream reasons describe a CBMC limitation. A row disabled for any
# other reason is NOT automatically outside the bar.
ELIGIBLE_REASONS = {
    "CBMC consumes more than 10 GB",
    "CBMC takes more than 15 minutes",
    "requires pthread_key_create",
    "requires memchr",
    "requires syscall",
    "requires write",
}


def _row_digest(rows: list[dict[str, object]]) -> str:
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def _git_show(rev: str, path: str) -> str | None:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "show", f"{rev}:{path}"],
        capture_output=True,
        text=True,
        check=False,
    )
    return proc.stdout if proc.returncode == 0 else None


def _disabled_harnesses(source: str) -> dict[str, str]:
    """Map harness name -> upstream reason, for cfg(disabled) kani proofs."""
    found: dict[str, str] = {}
    lines = source.splitlines()
    for index, line in enumerate(lines):
        match = FN_RE.match(line)
        if match is None:
            continue
        # Walk back over the contiguous attribute block above the fn.
        block: list[str] = []
        cursor = index - 1
        while cursor >= 0:
            text = lines[cursor].strip()
            if not text or text.startswith("//") or text.startswith("#["):
                block.append(lines[cursor])
                cursor -= 1
                continue
            break
        block.reverse()
        attributes = "\n".join(block)
        if PROOF_ATTR_RE.search(attributes) is None:
            continue
        if CFG_DISABLED_RE.search(attributes) is None:
            continue
        reason = ""
        for entry in block:
            hit = REASON_RE.search(entry)
            if hit:
                reason = hit.group(1)
                break
        found[match.group(1)] = reason
    return found


def build(inventory_path: Path) -> dict[str, object]:
    inventory = json.loads(inventory_path.read_text())
    rows = inventory if isinstance(inventory, list) else inventory["rows"]

    upstream: list[dict[str, object]] = []
    errors: list[str] = []
    for row in rows:
        if row.get("expected") != "PROOF":
            continue
        rel = row["file"]
        harness = row["harness"]
        bare = harness.rsplit("::", 1)[-1]

        fork_source = _git_show(FORK_COMMIT, rel)
        if fork_source is None:
            continue
        fork_disabled = _disabled_harnesses(fork_source)
        if bare not in fork_disabled:
            continue

        reason = fork_disabled[bare]
        if reason not in ELIGIBLE_REASONS:
            errors.append(
                f"{rel}::{harness}: upstream-disabled at {FORK_COMMIT} but its reason "
                f"{reason!r} is not a recognised CBMC limitation"
            )
            continue

        current = _disabled_harnesses((REPO_ROOT / rel).read_text())
        if bare not in current:
            errors.append(
                f"{rel}::{harness}: disabled upstream but ACTIVE today — it has been "
                f"activated and belongs in the bar; do not re-freeze it"
            )
            continue
        if current[bare] != reason:
            errors.append(
                f"{rel}::{harness}: reason drifted from {reason!r} to {current[bare]!r}"
            )
            continue

        upstream.append({"file": rel, "harness": harness, "reason": reason})

    if errors:
        for line in errors:
            print(f"generate_upstream_inactive_authority: error: {line}", file=sys.stderr)
        raise SystemExit(1)

    upstream.sort(key=lambda r: (r["file"], r["harness"]))
    return {
        "fork_commit": FORK_COMMIT,
        "description": (
            "PROOF rows upstream Kani disabled because CBMC could not run them. "
            "Outside the replacement BAR, inside the historical DENOMINATOR, "
            "tracked as supersession candidates."
        ),
        "rows": upstream,
        "row_sha256": _row_digest(upstream),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--inventory", type=Path,
                        default=REPO_ROOT / "tests/trust-mc/replacement-harness-inventory.json")
    parser.add_argument("--output", type=Path,
                        default=REPO_ROOT / "tests/trust-mc/replacement-upstream-inactive.json")
    parser.add_argument("--check", action="store_true",
                        help="verify the committed artifact matches a fresh generation")
    args = parser.parse_args()

    built = build(args.inventory)
    rendered = json.dumps(built, indent=2, sort_keys=True) + "\n"

    if args.check:
        if not args.output.exists():
            print(f"missing {args.output}", file=sys.stderr)
            return 1
        if args.output.read_text() != rendered:
            print(f"{args.output}: does not match a fresh generation", file=sys.stderr)
            return 1
        print(
            "generate_upstream_inactive_authority: OK "
            f"upstream_inactive={len(built['rows'])} row_sha256={built['row_sha256']}"
        )
        return 0

    args.output.write_text(rendered)
    print(
        "generate_upstream_inactive_authority: wrote "
        f"{len(built['rows'])} rows row_sha256={built['row_sha256']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
