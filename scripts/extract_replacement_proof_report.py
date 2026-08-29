# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import argparse
import copy
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

EXPECTED_SCHEMA_VERSION = 2
FINAL_PROOF_MARKER = "final_marker=PROOF"
DEFAULT_INVENTORY = (
    Path(__file__).resolve().parent.parent
    / "tests"
    / "trust-mc"
    / "replacement-harness-inventory.proof.json"
)

HarnessKey = tuple[str, str]


def _read_json_object(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected JSON object, got {type(data).__name__}")
    return data


def _require_harnesses(report: dict[str, Any], *, label: str) -> list[dict[str, Any]]:
    harnesses = report.get("harnesses")
    if not isinstance(harnesses, list):
        raise ValueError(f"{label}: expected 'harnesses' to be a list")

    rows: list[dict[str, Any]] = []
    for index, row in enumerate(harnesses):
        if not isinstance(row, dict):
            raise ValueError(
                f"{label}: expected harnesses[{index}] to be an object, got {type(row).__name__}"
            )
        rows.append(row)
    return rows


def _row_key(row: dict[str, Any], *, label: str) -> HarnessKey:
    file_name = row.get("file")
    harness_name = row.get("harness")
    if not isinstance(file_name, str) or not file_name.strip():
        raise ValueError(f"{label}: row missing non-empty file")
    if not isinstance(harness_name, str) or not harness_name.strip():
        raise ValueError(f"{label}: row missing non-empty harness")
    return (file_name, harness_name)


def _load_inventory_rows(
    inventory: dict[str, Any], *, label: str
) -> list[dict[str, Any]]:
    rows = inventory.get("rows")
    if not isinstance(rows, list):
        raise ValueError(f"{label}: expected 'rows' to be a list")

    normalized: list[dict[str, Any]] = []
    seen: set[HarnessKey] = set()
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(
                f"{label}: expected rows[{index}] to be an object, got {type(row).__name__}"
            )
        if row.get("expected") != "PROOF":
            raise ValueError(
                f"{label}: inventory row {index} has expected={row.get('expected')!r}; expected 'PROOF'"
            )
        key = _row_key(row, label=f"{label}: inventory row {index}")
        if key in seen:
            raise ValueError(
                f"{label}: duplicate proof inventory harness {key[0]}::{key[1]}"
            )
        seen.add(key)
        normalized.append(row)

    denominator = inventory.get("denominator")
    if denominator is not None and denominator != len(normalized):
        raise ValueError(
            f"{label}: denominator {denominator!r} does not match {len(normalized)} inventory rows"
        )
    return normalized


def _source_rows_by_key(rows: list[dict[str, Any]]) -> dict[HarnessKey, dict[str, Any]]:
    grouped: dict[HarnessKey, list[dict[str, Any]]] = defaultdict(list)
    for index, row in enumerate(rows):
        key = _row_key(row, label=f"source report harnesses[{index}]")
        grouped[key].append(row)

    duplicates = [key for key, matches in grouped.items() if len(matches) > 1]
    if duplicates:
        key = duplicates[0]
        raise ValueError(f"source report duplicates harness {key[0]}::{key[1]}")

    return {key: matches[0] for key, matches in grouped.items()}


def _require_final_proof_row(row: dict[str, Any], *, key: HarnessKey) -> None:
    if row.get("status") != "PASS" or row.get("verdict") != "PROOF":
        raise ValueError(
            f"source report row {key[0]}::{key[1]} is not PASS/PROOF: "
            f"status={row.get('status')!r}, verdict={row.get('verdict')!r}"
        )
    if row.get("execution_details") != FINAL_PROOF_MARKER:
        raise ValueError(
            f"source report row {key[0]}::{key[1]} has execution_details="
            f"{row.get('execution_details')!r}; expected {FINAL_PROOF_MARKER!r}"
        )


def _status_count(rows: list[dict[str, Any]], status: str) -> int:
    return sum(1 for row in rows if row.get("status") == status)


def _verdict_count(rows: list[dict[str, Any]], verdict: str) -> int:
    return sum(1 for row in rows if row.get("verdict") == verdict)


def _is_known_fp(row: dict[str, Any]) -> bool:
    return row.get("status") == "KNOWN_FP" or row.get("known_fp") is True


def _is_trusted_proof(row: dict[str, Any]) -> bool:
    return row.get("verdict") == "PROOF" and row.get("status") == "PASS"


def _recompute_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    ctrex_categories = Counter(
        str(row.get("ctrex_category"))
        for row in rows
        if row.get("ctrex_category") is not None
    )
    proof_qualifiers = [str(row.get("proof_qualifiers") or "") for row in rows]
    execution_states = Counter(
        str(row.get("execution_state"))
        for row in rows
        if row.get("execution_state") is not None
    )

    return {
        "rows": len(rows),
        "total": len(rows),
        "pass": _status_count(rows, "PASS"),
        "fail": _status_count(rows, "FAIL"),
        "xfail": _status_count(rows, "XFAIL"),
        "proof": _verdict_count(rows, "PROOF"),
        "known_fp": sum(1 for row in rows if _is_known_fp(row)),
        "trusted_proof": sum(1 for row in rows if _is_trusted_proof(row)),
        "ctrex": _verdict_count(rows, "CTREX"),
        "unknown": _verdict_count(rows, "UNKNOWN"),
        "error": _verdict_count(rows, "ERROR"),
        "bmc": _verdict_count(rows, "BMC"),
        "skip": _verdict_count(rows, "SKIP"),
        "ctrex_breakdown": {
            "encoding_gap": ctrex_categories["EncodingGap"],
            "over_approximation": ctrex_categories["OverApproximation"],
            "genuine": ctrex_categories["Genuine"],
            "unknown": ctrex_categories["Unknown"],
        },
        "proof_breakdown": {
            "clean": sum(1 for qualifier in proof_qualifiers if qualifier == "clean"),
            "should_panic": sum(
                1 for qualifier in proof_qualifiers if qualifier == "should_panic"
            ),
            "crosschecked": sum(
                1 for qualifier in proof_qualifiers if "crosschecked=" in qualifier
            ),
            "sound_qualified": sum(
                1 for qualifier in proof_qualifiers if "sound_fallback=" in qualifier
            ),
            "mem_overapprox_qualified": sum(
                1
                for qualifier in proof_qualifiers
                if "kani_mem_overapprox=" in qualifier
            ),
        },
        "execution_complete": execution_states["complete"],
        "execution_gated": sum(
            count for state, count in execution_states.items() if state != "complete"
        ),
        "execution_breakdown": dict(sorted(execution_states.items())),
    }


def derive_proof_report(
    source_report: dict[str, Any],
    proof_inventory: dict[str, Any],
    *,
    source_label: str = "source report",
    inventory_label: str = "proof inventory",
) -> dict[str, Any]:
    if source_report.get("schema_version") != EXPECTED_SCHEMA_VERSION:
        raise ValueError(
            f"{source_label}: expected schema_version={EXPECTED_SCHEMA_VERSION}, "
            f"got {source_report.get('schema_version')!r}"
        )

    source_rows = _require_harnesses(source_report, label=source_label)
    rows_by_key = _source_rows_by_key(source_rows)
    inventory_rows = _load_inventory_rows(proof_inventory, label=inventory_label)

    filtered_rows: list[dict[str, Any]] = []
    for inventory_row in inventory_rows:
        key = _row_key(inventory_row, label=inventory_label)
        source_row = rows_by_key.get(key)
        if source_row is None:
            raise ValueError(
                f"{source_label}: missing proof inventory harness {key[0]}::{key[1]}"
            )
        _require_final_proof_row(source_row, key=key)
        filtered_rows.append(copy.deepcopy(source_row))

    output = copy.deepcopy(source_report)
    output["summary"] = _recompute_summary(filtered_rows)
    output["harnesses"] = filtered_rows
    return output


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Derive the canonical replacement proof-only schema-v2 report from a "
            "full schema-v2 compiletest report."
        )
    )
    parser.add_argument("source_report", type=Path, help="Full schema-v2 JSON report")
    parser.add_argument(
        "output_report", type=Path, help="Proof-only JSON report to write"
    )
    parser.add_argument(
        "--inventory",
        type=Path,
        default=DEFAULT_INVENTORY,
        help=f"Proof inventory JSON path (default: {DEFAULT_INVENTORY})",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        source_report = _read_json_object(args.source_report)
        proof_inventory = _read_json_object(args.inventory)
        proof_report = derive_proof_report(
            source_report,
            proof_inventory,
            source_label=str(args.source_report),
            inventory_label=str(args.inventory),
        )
        args.output_report.parent.mkdir(parents=True, exist_ok=True)
        args.output_report.write_text(
            json.dumps(proof_report, indent=2, sort_keys=False) + "\n",
            encoding="utf-8",
        )
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
