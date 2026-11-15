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

SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import replacement_harness_dispositions as dispositions

EXPECTED_SCHEMA_VERSION = 2
FINAL_PROOF_MARKER = "final_marker=PROOF"
INACTIVE_EXECUTION_STATE = "inactive_accounted"
ZERO_CREDIT_FORBIDDEN_FIELDS = (
    "trusted_proof",
    "proof_qualifiers",
    "known_fp",
    "demotion_reasons",
    "retried",
)
DEFAULT_INVENTORY = (
    REPO_ROOT / "tests" / "trust-mc" / "replacement-harness-inventory.proof.json"
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
    cover_error = dispositions.cover_mismatch(
        {"file": key[0], "harness": key[1], "expected": "PROOF"},
        row.get("cover_properties"), row.get("cover_error"),
    )
    if cover_error is not None:
        raise ValueError(f"source report row {key[0]}::{key[1]}: {cover_error}")


def _require_zero_credit_row(
    row: dict[str, Any], *, key: HarnessKey, reason: str, source_label: str
) -> None:
    """Require an upstream-inactive row to be tracked with no credit at all.

    Outside the BAR is not the same as absent. Every upstream-inactive row must
    still appear in the full schema-v2 report, bound to its frozen source
    reason, carrying `SKIP`/`inactive_accounted` and no proof metadata. A row
    that went missing, or that acquired any credit, is a broken packet.
    """

    label = f"{source_label} row {key[0]}::{key[1]}"
    if row.get("verdict") != "SKIP" or row.get("status") != "SKIP":
        raise ValueError(
            f"{label} is upstream-inactive but not zero credit: "
            f"status={row.get('status')!r}, verdict={row.get('verdict')!r}"
        )
    if row.get("execution_state") != INACTIVE_EXECUTION_STATE:
        raise ValueError(
            f"{label} has execution_state {row.get('execution_state')!r}; "
            f"expected {INACTIVE_EXECUTION_STATE!r}"
        )
    if row.get("execution_details") != reason:
        raise ValueError(
            f"{label} has execution_details {row.get('execution_details')!r}; "
            f"expected the source-bound reason {reason!r}"
        )
    credited = [field for field in ZERO_CREDIT_FORBIDDEN_FIELDS if row.get(field)]
    if credited or row.get("sound_fallback_count"):
        raise ValueError(
            f"{label} is upstream-inactive but carries credit metadata: "
            f"{sorted(credited + (['sound_fallback_count'] if row.get('sound_fallback_count') else []))}"
        )


def _partition_proof_inventory(
    inventory_rows: list[dict[str, Any]],
    disposition_report: dict[str, Any],
    *,
    inventory_label: str,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Split the frozen PROOF authority into the bar and its zero-credit rest.

    A `PROOF` row is demanded unless the checked source disposition says
    upstream Kani had already switched it off. Un-gating one of those moves it
    back to `active` here with no edit to this tool, and a row WE disabled is
    never exempt: it stays in the demanded set and fails.
    """

    plan_by_key = {
        (row["file"], row["harness"]): row for row in disposition_report["rows"]
    }
    demanded: list[dict[str, Any]] = []
    upstream_inactive: list[dict[str, Any]] = []
    local_inactive: list[HarnessKey] = []
    for index, inventory_row in enumerate(inventory_rows):
        key = _row_key(inventory_row, label=f"{inventory_label}: inventory row {index}")
        plan_row = plan_by_key.get(key)
        if plan_row is None or plan_row.get("expected") != "PROOF":
            raise ValueError(
                f"{inventory_label}: {key[0]}::{key[1]} has no source-bound PROOF disposition"
            )
        if plan_row["disposition"] == "active":
            demanded.append(inventory_row)
        elif plan_row.get("inactive_origin") == "upstream":
            upstream_inactive.append(plan_row)
        else:
            local_inactive.append(key)

    if local_inactive:
        listed = ", ".join(f"{file}::{harness}" for file, harness in local_inactive[:5])
        raise ValueError(
            f"{inventory_label}: {len(local_inactive)} LOCALLY-disabled PROOF row(s) "
            f"remain inside the replacement bar: {listed}"
        )

    summary = disposition_report["summary"]["proof"]
    if len(demanded) != summary["bar"] or len(upstream_inactive) != summary["upstream_inactive"]:
        raise ValueError(
            f"{inventory_label}: partition ({len(demanded)} active, "
            f"{len(upstream_inactive)} upstream-inactive) does not match the checked "
            f"plan ({summary['bar']} bar, {summary['upstream_inactive']} upstream-inactive)"
        )
    return demanded, upstream_inactive


def _replacement_bar(
    disposition_report: dict[str, Any], upstream_inactive: list[dict[str, Any]]
) -> dict[str, Any]:
    """Record the narrowing in the packet, so nothing is dropped silently."""

    summary = disposition_report["summary"]["proof"]
    return {
        "historical": summary["historical"],
        "bar": summary["bar"],
        "upstream_inactive_zero_credit": summary["upstream_inactive"],
        "local_inactive": summary["local_inactive"],
        "supersession_candidates": summary["supersession_candidates"],
        "authority": disposition_report["authority"],
        "authority_row_sha256": summary["authority_row_sha256"],
        "active_inventory_row_sha256": summary["active_inventory_row_sha256"],
        "inactive_inventory_row_sha256": summary["inactive_inventory_row_sha256"],
        "upstream_inactive_rows": [
            {
                "file": row["file"],
                "harness": row["harness"],
                "reason": row["reason"],
                "upstream_reason": row.get("upstream_reason"),
                "source_line": row.get("source_line"),
            }
            for row in upstream_inactive
        ],
    }


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


def checked_dispositions() -> dict[str, Any]:
    """Re-derive the source-bound plan; a stale committed artifact is an error."""

    report = dispositions.build_dispositions(
        dispositions.DEFAULT_INVENTORY,
        dispositions.DEFAULT_PROOF_INVENTORY,
        dispositions.DEFAULT_NON_PROOF,
    )
    expected = json.dumps(report, indent=2, sort_keys=True) + "\n"
    actual = dispositions.DEFAULT_OUTPUT.read_text(encoding="utf-8")
    if actual != expected:
        raise ValueError(f"{dispositions.DEFAULT_OUTPUT}: source dispositions are stale")
    return report


def derive_proof_report(
    source_report: dict[str, Any],
    proof_inventory: dict[str, Any],
    disposition_report: dict[str, Any],
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

    authority = disposition_report["authority"]
    if proof_inventory.get("row_sha256") != authority["proof_row_sha256"]:
        raise ValueError(
            f"{inventory_label}: row_sha256 {proof_inventory.get('row_sha256')!r} is not "
            f"the source-bound proof authority {authority['proof_row_sha256']!r}"
        )

    demanded, upstream_inactive = _partition_proof_inventory(
        inventory_rows, disposition_report, inventory_label=inventory_label
    )

    # Excluded rows are checked BEFORE anything is credited: outside the bar
    # still means present, source-bound, and holding zero credit.
    for plan_row in upstream_inactive:
        key = (plan_row["file"], plan_row["harness"])
        source_row = rows_by_key.get(key)
        if source_row is None:
            raise ValueError(
                f"{source_label}: missing upstream-inactive harness {key[0]}::{key[1]}; "
                "the narrowed bar does not narrow the denominator"
            )
        _require_zero_credit_row(
            source_row, key=key, reason=plan_row["reason"], source_label=source_label
        )

    filtered_rows: list[dict[str, Any]] = []
    for inventory_row in demanded:
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
    output["replacement_bar"] = _replacement_bar(disposition_report, upstream_inactive)
    output["harnesses"] = filtered_rows
    return output


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Derive the canonical replacement proof-only schema-v2 report from a "
            "full schema-v2 compiletest report. The output holds the active "
            "PROOF bar; rows upstream Kani disabled because CBMC could not run "
            "them must be present in the source report with zero credit and are "
            "recorded in the output's replacement_bar block."
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
            checked_dispositions(),
            source_label=str(args.source_report),
            inventory_label=str(args.inventory),
        )
        args.output_report.parent.mkdir(parents=True, exist_ok=True)
        args.output_report.write_text(
            json.dumps(proof_report, indent=2, sort_keys=False) + "\n",
            encoding="utf-8",
        )
        bar = proof_report["replacement_bar"]
        print(
            f"replacement proof report: {args.output_report} "
            f"bar={bar['bar']} historical={bar['historical']} "
            f"upstream_inactive_zero_credit={bar['upstream_inactive_zero_credit']}"
        )
    except (ValueError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
