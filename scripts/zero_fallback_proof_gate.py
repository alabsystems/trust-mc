#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

"""Hard gate for replacement-quality TrustMC compiletest reports.

This gate is intentionally stricter than ``zero_fallback_canary.sh``. It rejects
any passing harness that is not a clean AY PROOF with no fallback, demotion,
translation-drop, retry, or BMC-reroute metadata.
"""

from __future__ import annotations

import argparse
import logging
import re
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_REPORT = REPO_ROOT / "reports" / "compiletest-per-harness-latest-trust-mc.json"
AY_PIN_LENGTH = 40
LOGGER = logging.getLogger("zero_fallback_proof_gate")
_SOLVER_COMMIT_RE = re.compile(r"^[0-9a-fA-F]{7,40}$")
_ZERO_SUMMARY_BUCKETS = (
    "ctrex",
    "unknown",
    "error",
    "bmc",
    "xfail",
    "skip",
    "execution_gated",
)
_ZERO_PROOF_BREAKDOWN_BUCKETS = (
    "should_panic",
    "crosschecked",
    "sound_qualified",
    "mem_overapprox_qualified",
)
_REQUIRED_ROW_FIELDS = (
    "execution_state",
    "execution_details",
    "sound_fallback_count",
    "proof_qualifiers",
)
_FORBIDDEN_RETRY_FIELDS = (
    "retry_attempts",
    "retry_resolved_by",
    "retry_final",
    "retry_recursive",
    "retry_relation_count",
)
_FORBIDDEN_NONEMPTY_ROW_FIELDS = (
    "demotion_reasons",
    "translation_drop_reasons",
    "ctrex_category",
    "ctrex_details",
    "unknown_details",
    "unknown_quality",
    "unknown_reason",
)


def _ensure_scripts_path() -> None:
    scripts_path = str(REPO_ROOT / "scripts")
    if scripts_path not in sys.path:
        sys.path.insert(0, scripts_path)


def _load_contract():
    _ensure_scripts_path()
    from compiletest_report_contract import load_schema_v2_report

    return load_schema_v2_report


def _validate_driver_attestation(
    report: dict[str, Any], *, expected_ay_pin: str
) -> list[str]:
    _ensure_scripts_path()
    from driver_binary_attestation import validate_attestation

    commit = report.get("commit")
    if not isinstance(commit, str):
        return [f"report commit {commit!r} is not a string"]
    return validate_attestation(
        report.get("driver_binary"),
        expected_trust_mc_sha=commit.lower(),
        expected_ay_pin=expected_ay_pin.lower(),
    )


def _default_expected_ay_pin() -> str:
    _ensure_scripts_path()
    from compiletest_report_contract import expected_ay_pin_from_cargo_toml

    return expected_ay_pin_from_cargo_toml(REPO_ROOT)


def _as_int(value: Any, *, default: int = 0) -> int:
    if value is None:
        return default
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, str) and value.strip().isdigit():
        return int(value)
    raise ValueError(f"expected integer-like value, got {value!r}")


def _non_empty(value: Any) -> bool:
    if value is None:
        return False
    if value in ("", [], {}, 0, False):
        return False
    return True


def _row_label(row: dict[str, Any]) -> str:
    return f"{row.get('file', '<unknown>')}::{row.get('harness', '<unknown>')}"


def _is_full_hex_pin(value: Any) -> bool:
    if not isinstance(value, str) or len(value) != AY_PIN_LENGTH:
        return False
    return all(char in "0123456789abcdefABCDEF" for char in value)


def _commit_prefix_matches_pin(commit: str, expected_ay_pin: str) -> bool:
    return bool(
        _SOLVER_COMMIT_RE.fullmatch(commit)
    ) and expected_ay_pin.lower().startswith(commit.lower())


def _append_int_mismatch(
    failures: list[str],
    *,
    label: str,
    value: Any,
    expected: int,
) -> None:
    try:
        actual = _as_int(value, default=expected - 1)
    except ValueError as err:
        failures.append(f"{label}: {err}")
        return

    if actual != expected:
        failures.append(f"{label} is {actual}; expected {expected}")


def _check_solver_binary_attestation(
    report: dict[str, Any],
    *,
    expected_ay_pin: str,
) -> list[str]:
    failures: list[str] = []
    solver_binary = report.get("solver_binary")
    if not isinstance(solver_binary, dict):
        return ["report solver_binary attestation is missing or not an object"]

    name = solver_binary.get("name")
    if name != "ay":
        failures.append(f"solver_binary.name {name!r} != 'ay'")

    path = solver_binary.get("path")
    if not isinstance(path, str) or not path.strip():
        failures.append("solver_binary.path is missing or empty")

    version = solver_binary.get("version")
    if not isinstance(version, str) or not version.strip():
        failures.append("solver_binary.version is missing or empty")

    commit = solver_binary.get("commit")
    if not isinstance(commit, str) or not _SOLVER_COMMIT_RE.fullmatch(commit):
        failures.append(
            f"solver_binary.commit {commit!r} is not a 7- to 40-character hex commit"
        )
    elif _is_full_hex_pin(expected_ay_pin) and not _commit_prefix_matches_pin(
        commit,
        expected_ay_pin,
    ):
        failures.append(
            f"solver_binary.commit {commit!r} does not match expected ay pin {expected_ay_pin!r}"
        )

    return failures


def _check_report_metadata(
    report: dict[str, Any],
    *,
    expected_ay_pin: str,
    expected_harnesses: int | None,
) -> tuple[list[str], list[Any]]:
    failures: list[str] = []
    if expected_harnesses is None:
        failures.append(
            "--expected-harnesses is required for replacement-quality proof"
        )
    elif expected_harnesses <= 0:
        failures.append("--expected-harnesses must be greater than 0")

    solver = report.get("solver")
    if solver != "ay":
        failures.append(f"report solver {solver!r} != 'ay'")

    replacement_evidence = report.get("replacement_evidence")
    if replacement_evidence is not True:
        failures.append(
            f"report replacement_evidence {replacement_evidence!r} is not true"
        )

    if not _is_full_hex_pin(expected_ay_pin):
        failures.append(
            f"expected ay pin {expected_ay_pin!r} is not a 40-character hex pin"
        )

    ay_pin = report.get("ay_pin")
    if not _is_full_hex_pin(ay_pin):
        failures.append(f"report ay_pin {ay_pin!r} is not a 40-character hex pin")
    elif ay_pin != expected_ay_pin:
        failures.append(f"report ay_pin {ay_pin!r} != expected {expected_ay_pin!r}")

    failures.extend(
        _check_solver_binary_attestation(report, expected_ay_pin=expected_ay_pin)
    )
    failures.extend(
        _validate_driver_attestation(report, expected_ay_pin=expected_ay_pin)
    )

    tree_state = report.get("tree_state")
    if tree_state != "clean":
        failures.append(f"report tree_state {tree_state!r} != 'clean'")

    tree_fingerprint = report.get("tree_fingerprint")
    if not isinstance(tree_fingerprint, str) or not tree_fingerprint.strip():
        failures.append("report missing usable tree_fingerprint")

    harnesses = report.get("harnesses")
    if not isinstance(harnesses, list):
        failures.append("report harnesses is not a list")
        return failures, []

    if expected_harnesses is not None and len(harnesses) != expected_harnesses:
        failures.append(
            f"report has {len(harnesses)} harnesses; expected {expected_harnesses}"
        )

    return failures, harnesses


def _check_proof_breakdown(
    summary: dict[str, Any], expected_harnesses: int | None
) -> list[str]:
    failures: list[str] = []
    proof_breakdown = summary.get("proof_breakdown")
    if not isinstance(proof_breakdown, dict):
        return ["summary.proof_breakdown is not an object"]

    if expected_harnesses is not None:
        _append_int_mismatch(
            failures,
            label="summary.proof_breakdown.clean",
            value=proof_breakdown.get("clean"),
            expected=expected_harnesses,
        )

    for field in _ZERO_PROOF_BREAKDOWN_BUCKETS:
        _append_int_mismatch(
            failures,
            label=f"summary.proof_breakdown.{field}",
            value=proof_breakdown.get(field),
            expected=0,
        )
    return failures


def _check_summary(report: dict[str, Any], expected_harnesses: int | None) -> list[str]:
    failures: list[str] = []
    summary = report.get("summary")
    if not isinstance(summary, dict):
        return ["report summary is not an object"]

    if expected_harnesses is not None:
        for field in ("total", "proof", "execution_complete"):
            _append_int_mismatch(
                failures,
                label=f"summary.{field}",
                value=summary.get(field),
                expected=expected_harnesses,
            )

    for field in _ZERO_SUMMARY_BUCKETS:
        _append_int_mismatch(
            failures,
            label=f"summary.{field}",
            value=summary.get(field),
            expected=0,
        )

    failures.extend(_check_proof_breakdown(summary, expected_harnesses))
    return failures


def _check_harness_identity(
    row: dict[str, Any],
    *,
    label: str,
    seen_harness_keys: set[tuple[str, str]],
) -> list[str]:
    failures: list[str] = []
    file_name = row.get("file")
    harness_name = row.get("harness")
    if not isinstance(file_name, str) or not file_name.strip():
        failures.append(f"{label}: missing usable file")
    if not isinstance(harness_name, str) or not harness_name.strip():
        failures.append(f"{label}: missing usable harness")

    has_file = isinstance(file_name, str) and file_name.strip()
    has_harness = isinstance(harness_name, str) and harness_name.strip()
    if has_file and has_harness:
        key = (file_name, harness_name)
        if key in seen_harness_keys:
            failures.append(f"{label}: duplicate harness row")
        seen_harness_keys.add(key)
    return failures


def _check_harness_classification(row: dict[str, Any], *, label: str) -> list[str]:
    failures: list[str] = []
    if row.get("status") != "PASS":
        failures.append(f"{label}: status {row.get('status')!r} is not PASS")
    if row.get("expected") != "PROOF":
        failures.append(
            f"{label}: expected {row.get('expected')!r} is not replacement-quality"
        )
    if row.get("verdict") != "PROOF":
        failures.append(f"{label}: verdict {row.get('verdict')!r} is not PROOF")
    return failures


def _check_required_harness_fields(row: dict[str, Any], *, label: str) -> list[str]:
    failures = [
        f"{label}: missing required field {field}"
        for field in _REQUIRED_ROW_FIELDS
        if field not in row
    ]
    if row.get("execution_state") != "complete":
        failures.append(
            f"{label}: execution_state {row.get('execution_state')!r} is not complete"
        )
    if row.get("execution_details") != "final_marker=PROOF":
        failures.append(
            f"{label}: execution_details {row.get('execution_details')!r} is not final_marker=PROOF"
        )
    if "sound_fallback_count" in row:
        _append_int_mismatch(
            failures,
            label=f"{label}: sound_fallback_count",
            value=row.get("sound_fallback_count"),
            expected=0,
        )
    if row.get("proof_qualifiers") != "clean":
        failures.append(
            f"{label}: proof_qualifiers {row.get('proof_qualifiers')!r} is not clean"
        )
    return failures


def _check_forbidden_harness_metadata(row: dict[str, Any], *, label: str) -> list[str]:
    failures: list[str] = []
    if "retried" in row:
        failures.append(f"{label}: retried present: {row.get('retried')!r}")
    failures.extend(
        f"{label}: {field} present: {row.get(field)!r}"
        for field in _FORBIDDEN_RETRY_FIELDS
        if field in row
    )
    failures.extend(
        f"{label}: {field} present: {row.get(field)!r}"
        for field in _FORBIDDEN_NONEMPTY_ROW_FIELDS
        if _non_empty(row.get(field))
    )
    return failures


def _check_harness_row(row: Any, seen_harness_keys: set[tuple[str, str]]) -> list[str]:
    if not isinstance(row, dict):
        return [f"non-object harness row: {row!r}"]

    label = _row_label(row)
    failures = _check_harness_identity(
        row, label=label, seen_harness_keys=seen_harness_keys
    )
    failures.extend(_check_harness_classification(row, label=label))
    failures.extend(_check_required_harness_fields(row, label=label))
    failures.extend(_check_forbidden_harness_metadata(row, label=label))
    return failures


def find_gate_failures(
    report: dict[str, Any],
    *,
    expected_ay_pin: str,
    expected_harnesses: int | None,
) -> list[str]:
    failures, harnesses = _check_report_metadata(
        report,
        expected_ay_pin=expected_ay_pin,
        expected_harnesses=expected_harnesses,
    )
    failures.extend(_check_summary(report, expected_harnesses))

    seen_harness_keys: set[tuple[str, str]] = set()
    for row in harnesses:
        failures.extend(_check_harness_row(row, seen_harness_keys))
    return failures


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", nargs="?", type=Path, default=DEFAULT_REPORT)
    parser.add_argument(
        "--expected-ay-pin",
        default=None,
        help="Expected 40-character AY commit; defaults to root Cargo.toml ay-chc rev",
    )
    parser.add_argument("--expected-harnesses", type=int, required=True)
    parser.add_argument(
        "--allow-stale-report", action="store_true", help=argparse.SUPPRESS
    )
    args = parser.parse_args(argv)
    if args.expected_ay_pin is None:
        try:
            args.expected_ay_pin = _default_expected_ay_pin()
        except ValueError as err:
            parser.error(str(err))
    return args


def main(argv: list[str] | None = None) -> int:
    logging.basicConfig(format="%(message)s", level=logging.INFO)
    args = parse_args(argv)
    load_schema_v2_report = _load_contract()
    try:
        report = load_schema_v2_report(
            args.report,
            repo_root=REPO_ROOT,
            require_current_head=True,
        )
    except ValueError as err:
        LOGGER.error("zero-fallback proof gate: FAIL")
        LOGGER.error("- %s", err)
        return 1

    failures = find_gate_failures(
        report,
        expected_ay_pin=args.expected_ay_pin,
        expected_harnesses=args.expected_harnesses,
    )
    if failures:
        LOGGER.error("zero-fallback proof gate: FAIL")
        for failure in failures[:50]:
            LOGGER.error("- %s", failure)
        if len(failures) > 50:
            LOGGER.error("- ... %d more failure(s)", len(failures) - 50)
        return 1

    LOGGER.info(
        "zero-fallback proof gate: PASS (%d replacement-quality PROOF harnesses)",
        len(report.get("harnesses", [])),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
