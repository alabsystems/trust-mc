# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations


def _require_harness_list(
    report: dict[str, object],
    *,
    label: str,
) -> list[dict[str, object]]:
    harnesses = report.get("harnesses")
    if not isinstance(harnesses, list):
        raise ValueError(f"{label}: expected 'harnesses' to be a list")

    normalized: list[dict[str, object]] = []
    for index, entry in enumerate(harnesses):
        if not isinstance(entry, dict):
            raise ValueError(
                f"{label}: expected harnesses[{index}] to be an object, got {type(entry).__name__}"
            )
        normalized.append(entry)
    return normalized


def _is_known_fp_row(entry: dict[str, object]) -> bool:
    return entry.get("status") == "KNOWN_FP"


def _is_trusted_proof_row(entry: dict[str, object]) -> bool:
    return entry.get("verdict") == "PROOF" and entry.get("status", "PASS") == "PASS"


def _summary_count_matches(actual: object, expected: int) -> bool:
    return type(actual) is int and actual == expected


def _append_summary_gap(
    gaps: list[dict[str, object]],
    summary: dict[str, object],
    field: str,
    expected: int,
) -> None:
    actual = summary.get(field)
    if not _summary_count_matches(actual, expected):
        gaps.append({
            "scope": "summary",
            "field": field,
            "expected": expected,
            "actual": actual,
        })


def _append_row_flag_gap(
    gaps: list[dict[str, object]],
    entry: dict[str, object],
    field: str,
    expected: bool,
) -> None:
    actual = entry.get(field)
    if actual is expected or (not expected and actual is None):
        return
    gaps.append({
        "scope": "harness",
        "file": entry.get("file", "<unknown>"),
        "harness": entry.get("harness", "<unknown>"),
        "field": field,
        "expected": expected,
        "actual": actual,
    })


def find_proof_accounting_gaps(
    report: dict[str, object],
) -> list[dict[str, object]]:
    """Return gaps in additive known-false-positive proof accounting."""
    harnesses = _require_harness_list(report, label="report")
    expected_known_fp = sum(1 for entry in harnesses if _is_known_fp_row(entry))
    expected_trusted_proof = sum(1 for entry in harnesses if _is_trusted_proof_row(entry))

    gaps: list[dict[str, object]] = []
    summary = report.get("summary")
    if not isinstance(summary, dict):
        gaps.append({
            "scope": "summary",
            "field": "summary",
            "expected": "object",
            "actual": type(summary).__name__,
        })
    else:
        _append_summary_gap(gaps, summary, "known_fp", expected_known_fp)
        _append_summary_gap(gaps, summary, "trusted_proof", expected_trusted_proof)

    for entry in harnesses:
        _append_row_flag_gap(gaps, entry, "known_fp", _is_known_fp_row(entry))
        _append_row_flag_gap(gaps, entry, "trusted_proof", _is_trusted_proof_row(entry))
    return gaps


def require_valid_proof_accounting(report: dict[str, object]) -> None:
    """Reject reports with stale/missing additive proof accounting fields."""
    gaps = find_proof_accounting_gaps(report)
    if not gaps:
        return

    gap = gaps[0]
    if gap.get("scope") == "harness":
        location = f"{gap.get('file', '<unknown>')}::{gap.get('harness', '<unknown>')}"
    else:
        location = "summary"
    raise ValueError(
        f"invalid proof accounting for {location}: {gap['field']} "
        f"expected {gap['expected']!r}, got {gap['actual']!r}"
    )
