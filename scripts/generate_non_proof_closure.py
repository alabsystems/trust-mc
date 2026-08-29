#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Generate or check the canonical replacement-audit non-PROOF closure."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
INVENTORY_PATH = REPO_ROOT / "tests/trust-mc/replacement-harness-inventory.json"
OUTPUT_PATH = REPO_ROOT / "tests/trust-mc/non-proof-closure.json"
EXPECTED_OUTCOMES = frozenset({"PROOF", "CTREX", "UNKNOWN", "ERROR", "BMC_SAFE"})
INVENTORY_FIELDS = frozenset({"file", "harness", "expected", "lane"})


def _row_digest(rows: list[dict[str, str]]) -> str:
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _canonical_json(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def build_closure(inventory: dict[str, Any], inventory_name: str) -> dict[str, object]:
    rows_value = inventory.get("rows")
    if not isinstance(rows_value, list):
        raise ValueError("inventory rows must be an array")

    inventory_rows: list[dict[str, str]] = []
    closure_rows: list[dict[str, str]] = []
    for index, row_value in enumerate(rows_value):
        if not isinstance(row_value, dict) or set(row_value) != INVENTORY_FIELDS:
            raise ValueError(
                f"inventory rows[{index}] must have exactly "
                f"{sorted(INVENTORY_FIELDS)}"
            )
        try:
            file_name = row_value["file"]
            harness = row_value["harness"]
            expected = row_value["expected"]
            lane = row_value["lane"]
        except KeyError as err:
            raise ValueError(f"inventory rows[{index}] is missing {err.args[0]}") from err
        if not all(
            isinstance(value, str)
            for value in (file_name, harness, expected, lane)
        ):
            raise ValueError(f"inventory rows[{index}] fields must be strings")
        if expected not in EXPECTED_OUTCOMES:
            raise ValueError(
                f"inventory rows[{index}] has unsupported expected outcome {expected!r}"
            )
        inventory_rows.append(
            {
                "file": file_name,
                "harness": harness,
                "expected": expected,
                "lane": lane,
            }
        )
        if expected == "PROOF":
            continue
        closure_rows.append(
            {
                "file": file_name,
                "harness": harness,
                "lane": lane,
                "expected": expected,
                "disposition": "expected-fail",
                "justification": (
                    "expected non-PROOF verdict carried by the test's `expected` "
                    f"output file (survey disposition: {expected})"
                ),
            }
        )

    closure_rows.sort(key=lambda row: (row["file"], row["harness"]))
    denominator = inventory.get("denominator")
    row_sha256 = inventory.get("row_sha256")
    suite = inventory.get("suite")
    if denominator != len(rows_value):
        raise ValueError(
            f"inventory denominator {denominator!r} does not match {len(rows_value)} rows"
        )
    if not isinstance(row_sha256, str) or len(row_sha256) != 64:
        raise ValueError("inventory row_sha256 must be a 64-character digest")
    if row_sha256 != _row_digest(inventory_rows):
        raise ValueError("inventory row_sha256 does not match rows")
    if not isinstance(suite, str) or not suite:
        raise ValueError("inventory suite must be a non-empty string")

    return {
        "schema_version": 1,
        "suite": suite,
        "denominator": len(closure_rows),
        "row_sha256": _row_digest(closure_rows),
        "rows": closure_rows,
        "source": {
            "inventory": inventory_name,
            "denominator": denominator,
            "row_sha256": row_sha256,
        },
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Generate or check the canonical non-PROOF closure artifact."
    )
    parser.add_argument(
        "--inventory",
        type=Path,
        default=INVENTORY_PATH,
        help="Mixed replacement inventory JSON path.",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=OUTPUT_PATH,
        help="Non-PROOF closure JSON path.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Compare with the regenerated closure and write nothing.",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        inventory = json.loads(args.inventory.read_text(encoding="utf-8"))
        if not isinstance(inventory, dict):
            raise ValueError("inventory must be a JSON object")
        closure = build_closure(inventory, args.inventory.name)
        rendered = _canonical_json(closure)
        if args.check:
            actual = args.output.read_text(encoding="utf-8")
            if actual != rendered:
                raise ValueError(f"closure is stale: {args.output}")
            print(
                "generate_non_proof_closure: OK "
                f"path={args.output} denominator={closure['denominator']} "
                f"row_sha256={closure['row_sha256']}"
            )
            return 0

        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
        print(
            "generate_non_proof_closure: wrote "
            f"{args.output} denominator={closure['denominator']} "
            f"row_sha256={closure['row_sha256']}"
        )
        return 0
    except (OSError, ValueError, json.JSONDecodeError) as err:
        print(f"generate_non_proof_closure: ERROR: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
