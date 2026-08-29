# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

from compiletest_proof_accounting import (
    find_proof_accounting_gaps,
    require_valid_proof_accounting,
)
from compiletest_report_paths import MEASUREMENT_FINGERPRINT_PATHS, REPORT_TOOL_PATHS
from ay_manifest_pin import AY_PIN_RE, expected_ay_pin_from_cargo_toml
from driver_binary_attestation import validate_attestation

__all__ = (
    "find_proof_accounting_gaps",
    "require_valid_proof_accounting",
    "expected_ay_pin_from_cargo_toml",
)


EXPECTED_REPORT_SCHEMA_VERSION = 2
_CURRENT_AUTHORITY_KEYS = (
    "tree_state",
    "tree_fingerprint",
    "ay_pin",
    "solver",
    "replacement_evidence",
    "driver_binary",
)


def _current_head(repo_root: Path) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repo_root,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        stderr = result.stderr.strip()
        details = f": {stderr}" if stderr else ""
        raise ValueError(f"{repo_root}: failed to resolve current HEAD{details}")
    head = result.stdout.strip()
    if not head:
        raise ValueError(f"{repo_root}: git rev-parse HEAD returned empty output")
    return head


def _current_tree_fingerprint(repo_root: Path) -> str:
    result = subprocess.run(
        [
            "git",
            "diff",
            "--no-ext-diff",
            "--binary",
            "HEAD",
            "--",
            *MEASUREMENT_FINGERPRINT_PATHS,
        ],
        cwd=repo_root,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        stderr = result.stderr.decode("utf-8", errors="replace").strip()
        details = f": {stderr}" if stderr else ""
        raise ValueError(
            f"{repo_root}: failed to compute current tree fingerprint{details}"
        )
    return hashlib.sha256(result.stdout).hexdigest()


_TREE_STATE_DIRTY_PATH = re.compile(
    r"(\.rs$|(^|/)Cargo\.toml$|(^|/)Cargo\.lock$|(^|/)rust-toolchain\.toml$)"
)
_TREE_STATE_DIRTY_SCRIPT_PATHS = set(REPORT_TOOL_PATHS)


def _current_tree_state(repo_root: Path) -> str:
    result = subprocess.run(
        ["git", "status", "--porcelain=v1", "--untracked-files=all"],
        cwd=repo_root,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        stderr = result.stderr.strip()
        details = f": {stderr}" if stderr else ""
        raise ValueError(f"{repo_root}: failed to compute current tree state{details}")

    for line in result.stdout.splitlines():
        path = line[3:]
        if path.startswith("reports/"):
            continue
        if (
            _TREE_STATE_DIRTY_PATH.search(path)
            or path in _TREE_STATE_DIRTY_SCRIPT_PATHS
        ):
            return "dirty"
    return "clean"


def _read_schema_v2_json(path: Path) -> dict[str, object]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected JSON object, got {type(data).__name__}")
    return data


def _require_schema_v2_basics(data: dict[str, object], *, path: Path) -> None:
    schema_version = data.get("schema_version")
    if schema_version != EXPECTED_REPORT_SCHEMA_VERSION:
        raise ValueError(
            f"{path}: expected schema_version={EXPECTED_REPORT_SCHEMA_VERSION}, got {schema_version!r}; "
            "legacy per-harness reports are not accepted",
        )

    _require_harness_list(data, label=str(path))

    tree_state = data.get("tree_state")
    if tree_state is not None and tree_state not in {"clean", "dirty"}:
        raise ValueError(
            f"{path}: invalid tree_state {tree_state!r}; expected 'clean' or 'dirty'"
        )


def _require_current_commit(
    data: dict[str, object],
    *,
    path: Path,
    repo_root: Path,
) -> None:
    expected_head = _current_head(repo_root)
    report_commit = data.get("commit")
    if (
        not isinstance(report_commit, str)
        or not report_commit.strip()
        or report_commit == "unknown"
    ):
        raise ValueError(
            f"{path}: schema-v2 report missing usable embedded commit; expected current HEAD {expected_head}",
        )
    if report_commit != expected_head:
        raise ValueError(
            f"{path}: stale schema-v2 report commit {report_commit}; expected current HEAD {expected_head}",
        )


def _require_current_authority_keys(data: dict[str, object], *, path: Path) -> None:
    for key in _CURRENT_AUTHORITY_KEYS:
        if key not in data:
            raise ValueError(f"{path}: current-head schema-v2 report missing {key}")


def _require_current_tree_state(
    data: dict[str, object],
    *,
    path: Path,
    repo_root: Path,
) -> None:
    if data.get("tree_state") not in {"clean", "dirty"}:
        raise ValueError(
            f"{path}: current-head schema-v2 report has invalid tree_state {data.get('tree_state')!r}",
        )
    expected_tree_state = _current_tree_state(repo_root)
    if data.get("tree_state") != expected_tree_state:
        raise ValueError(
            f"{path}: stale schema-v2 report tree_state {data.get('tree_state')!r}; "
            f"expected current tree_state {expected_tree_state!r}",
        )


def _require_current_replacement_evidence(
    data: dict[str, object], *, path: Path
) -> None:
    ay_pin = data.get("ay_pin")
    if not isinstance(ay_pin, str) or AY_PIN_RE.fullmatch(ay_pin) is None:
        raise ValueError(
            f"{path}: current-head schema-v2 report ay_pin {ay_pin!r} "
            "is not a 40-character hex pin"
        )

    solver = data.get("solver")
    if solver != "ay":
        raise ValueError(
            f"{path}: current-head schema-v2 report solver {solver!r} != 'ay'"
        )

    if data.get("replacement_evidence") is not True:
        raise ValueError(
            f"{path}: current-head schema-v2 report replacement_evidence "
            f"{data.get('replacement_evidence')!r} is not true",
        )

    commit = data.get("commit")
    if not isinstance(commit, str):
        raise ValueError(f"{path}: current-head schema-v2 report commit is not a string")
    failures = validate_attestation(
        data.get("driver_binary"),
        expected_trust_mc_sha=commit.lower(),
        expected_ay_pin=ay_pin.lower(),
    )
    if failures:
        raise ValueError(f"{path}: " + "; ".join(failures))


def _require_current_tree_fingerprint(
    data: dict[str, object],
    *,
    path: Path,
    repo_root: Path,
) -> None:
    report_tree_fingerprint = data.get("tree_fingerprint")
    if (
        not isinstance(report_tree_fingerprint, str)
        or not report_tree_fingerprint.strip()
    ):
        raise ValueError(
            f"{path}: invalid tree_fingerprint {report_tree_fingerprint!r}"
        )
    expected_tree_fingerprint = _current_tree_fingerprint(repo_root)
    if report_tree_fingerprint != expected_tree_fingerprint:
        raise ValueError(
            f"{path}: stale schema-v2 report tree_fingerprint {report_tree_fingerprint}; "
            f"expected current tree fingerprint {expected_tree_fingerprint}",
        )


def _require_current_head_authority(
    data: dict[str, object],
    *,
    path: Path,
    repo_root: Path,
) -> None:
    _require_current_commit(data, path=path, repo_root=repo_root)
    _require_current_authority_keys(data, path=path)
    _require_current_tree_state(data, path=path, repo_root=repo_root)
    _require_current_replacement_evidence(data, path=path)
    _require_current_tree_fingerprint(data, path=path, repo_root=repo_root)


def load_schema_v2_report(
    path: Path,
    *,
    repo_root: Path,
    require_current_head: bool = True,
) -> dict[str, object]:
    data = _read_schema_v2_json(path)
    _require_schema_v2_basics(data, path=path)
    if require_current_head:
        _require_current_head_authority(data, path=path, repo_root=repo_root)
    return data


# ---------------------------------------------------------------------------
# Cross-report measurement helpers (#4080 / #4102)
# ---------------------------------------------------------------------------

_MEASUREMENT_KEYS = (
    "schema_version",
    "commit",
    "ay_pin",
    "tree_state",
    "tree_fingerprint",
    "solver",
    "replacement_evidence",
    "driver_binary",
)


def require_same_measurement(
    report_a: dict[str, object],
    report_b: dict[str, object],
    *,
    label_a: str = "report_a",
    label_b: str = "report_b",
) -> None:
    """Reject two reports unless they share the same measurement context.

    Two reports are from the same measurement when their ``schema_version``,
    ``commit``, ``ay_pin``, ``tree_state``, ``tree_fingerprint``,
    ``solver``, ``replacement_evidence``, and ``driver_binary`` all match.
    Any mismatch raises ``ValueError`` identifying the divergent field.
    """
    for key in _MEASUREMENT_KEYS:
        if key not in report_a:
            raise ValueError(f"measurement missing {key!r}: {label_a}")
        if key not in report_b:
            raise ValueError(f"measurement missing {key!r}: {label_b}")
        val_a = report_a.get(key)
        val_b = report_b.get(key)
        if val_a != val_b:
            raise ValueError(
                f"measurement mismatch on {key!r}: "
                f"{label_a}={val_a!r} vs {label_b}={val_b!r}"
            )


_CLASSIFICATION_FIELDS = (
    "verdict",
    "status",
    "execution_state",
    "translation_drop_reasons",
)

_ALIAS_PARITY_FIELDS = (
    *_CLASSIFICATION_FIELDS,
    "expected",
    "execution_details",
    "proof_qualifiers",
    "retried",
    "retry_attempts",
    "retry_resolved_by",
    "retry_final",
    "retry_recursive",
    "retry_relation_count",
    "demotion_reasons",
    "translation_drop_reasons",
    "ctrex_category",
    "ctrex_details",
    "known_fp",
    "trusted_proof",
    "sound_fallback_count",
    "unknown_details",
    "unknown_quality",
    "unknown_reason",
)


def _require_harness_list(
    report: dict[str, object],
    *,
    label: str,
) -> list[dict[str, object]]:
    harnesses = report.get("harnesses")
    if not isinstance(harnesses, list):
        raise ValueError(f"{label}: expected 'harnesses' to be a list")

    normalized: list[dict[str, object]] = []
    seen_keys: set[tuple[str, str]] = set()
    for index, entry in enumerate(harnesses):
        if not isinstance(entry, dict):
            raise ValueError(
                f"{label}: expected harnesses[{index}] to be an object, got {type(entry).__name__}"
            )
        file_name = entry.get("file")
        harness_name = entry.get("harness")
        if (
            isinstance(file_name, str)
            and file_name.strip()
            and isinstance(harness_name, str)
            and harness_name.strip()
        ):
            key = (file_name, harness_name)
            if key in seen_keys:
                raise ValueError(
                    f"{label}: duplicate harness key {file_name}::{harness_name}"
                )
            seen_keys.add(key)
        normalized.append(entry)
    return normalized


def find_missing_alias_classification_fields(
    aggregate_report: dict[str, object],
    alias_report: dict[str, object],
    *,
    label_aggregate: str = "aggregate",
    label_alias: str = "alias",
) -> list[dict[str, object]]:
    """Return same-measurement alias rows that drop aggregate classification fields.

    The aggregate report is the default current-head authority. Filtered alias
    reports are reproducer artifacts unless they match the aggregate
    measurement context and preserve any classification-bearing fields present
    on the aggregate row for the same ``(file, harness)`` key.
    """
    require_same_measurement(
        aggregate_report,
        alias_report,
        label_a=label_aggregate,
        label_b=label_alias,
    )

    aggregate_harnesses = _require_harness_list(aggregate_report, label=label_aggregate)
    alias_harnesses = _require_harness_list(alias_report, label=label_alias)

    aggregate_by_key: dict[tuple[object, object], dict[str, object]] = {}
    for entry in aggregate_harnesses:
        aggregate_by_key[(entry.get("file"), entry.get("harness"))] = entry

    gaps: list[dict[str, object]] = []
    for entry in alias_harnesses:
        key = (entry.get("file"), entry.get("harness"))
        aggregate_entry = aggregate_by_key.get(key)
        if aggregate_entry is None:
            continue

        missing = [
            field
            for field in _ALIAS_PARITY_FIELDS
            if field in aggregate_entry and field not in entry
        ]
        mismatched = [
            field
            for field in _ALIAS_PARITY_FIELDS
            if field in aggregate_entry
            and field in entry
            and aggregate_entry.get(field) != entry.get(field)
        ]
        if missing or mismatched:
            gaps.append(
                {
                    "harness": entry.get("harness", "<unknown>"),
                    "file": entry.get("file", "<unknown>"),
                    "missing": missing,
                    "mismatched": mismatched,
                }
            )

    return gaps


def require_valid_alias_authority(
    aggregate_report: dict[str, object],
    alias_report: dict[str, object],
    *,
    label_aggregate: str = "aggregate",
    label_alias: str = "alias",
) -> None:
    """Reject filtered aliases that cannot act as current-head authority.

    The aggregate schema-v2 report is the default current-head authority. A
    filtered alias only becomes authority for downstream routing when it shares
    the same measurement context and preserves the aggregate row's
    classification-bearing fields.
    """
    gaps = find_missing_alias_classification_fields(
        aggregate_report,
        alias_report,
        label_aggregate=label_aggregate,
        label_alias=label_alias,
    )
    if gaps:
        gap = gaps[0]
        missing_fields = ", ".join(str(field) for field in gap["missing"])
        mismatched_fields = ", ".join(str(field) for field in gap.get("mismatched", []))
        if missing_fields:
            raise ValueError(
                f"{label_alias} drops classification-bearing field(s) for "
                f"{gap['file']}::{gap['harness']}: {missing_fields}"
            )
        raise ValueError(
            f"{label_alias} changes classification-bearing field(s) for "
            f"{gap['file']}::{gap['harness']}: {mismatched_fields}"
        )


def find_missing_classification_fields(
    report: dict[str, object],
) -> list[dict[str, object]]:
    """Return harness entries missing one or more classification-bearing fields.

    Each returned dict has ``harness`` (str), ``file`` (str), and
    ``missing`` (list of field names).  Returns an empty list when every
    harness carries the full classification surface.
    """
    harnesses = _require_harness_list(report, label="report")

    gaps: list[dict[str, object]] = []
    for entry in harnesses:
        missing = [f for f in _CLASSIFICATION_FIELDS if f not in entry]
        if missing:
            gaps.append(
                {
                    "harness": entry.get("harness", "<unknown>"),
                    "file": entry.get("file", "<unknown>"),
                    "missing": missing,
                }
            )
    return gaps


def select_harnesses(
    report: dict[str, object],
    *,
    names: list[str],
) -> list[dict[str, object]]:
    """Return only the harness entries whose ``harness`` field is in *names*.

    Preserves original order from the report.  Returns an empty list when
    no matches are found.
    """
    harnesses = _require_harness_list(report, label="report")
    name_set = set(names)
    return [entry for entry in harnesses if entry.get("harness") in name_set]
