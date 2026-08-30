#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Bind the historical replacement inventory to executable source harnesses.

The public-corpus inventory is intentionally historical: its denominator may not
be lowered just because a source harness is currently cfg-disabled.  This tool
adds the missing source-bound execution disposition.  Active rows are mapped to
an exact driver harness; cfg-disabled rows remain in the denominator with zero
execution and proof credit.  Every other mismatch is an error.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable

from extract_proof_harnesses import extract_proof_harnesses


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_INVENTORY = REPO_ROOT / "tests/trust-mc/replacement-harness-inventory.json"
DEFAULT_PROOF_INVENTORY = (
    REPO_ROOT / "tests/trust-mc/replacement-harness-inventory.proof.json"
)
DEFAULT_NON_PROOF = REPO_ROOT / "tests/trust-mc/non-proof-closure.json"
DEFAULT_OUTPUT = (
    REPO_ROOT / "tests/trust-mc/replacement-harness-dispositions.json"
)

EXPECTED_OUTCOMES = frozenset({"PROOF", "CTREX", "UNKNOWN", "ERROR", "BMC_SAFE"})
ACTIVE_EXECUTION_STATES = frozenset(
    {"complete", "missing_verdict", "watchdog_cleanup", "watchdog_timeout"}
)
INVENTORY_FIELDS = frozenset({"file", "harness", "expected", "lane"})
CLOSURE_FIELDS = frozenset(
    {"disposition", "expected", "file", "harness", "justification", "lane"}
)
PROOF_ATTR_RE = re.compile(r"#\[\s*kani::proof(?:\s*\([^]]*\))?\s*\]")
CFG_DISABLED_RE = re.compile(r"#\[\s*cfg\s*\(\s*disabled\s*\)\s*\]")
CFG_FEATURE_RE = re.compile(
    r'#\[\s*cfg\s*\(\s*feature\s*=\s*"([A-Za-z0-9_-]+)"\s*\)\s*\]'
)
INNER_CFG_RE = re.compile(r"^\s*#!\[\s*cfg\s*\((.*)\)\s*\]\s*$", re.MULTILINE)
CFG_FEATURE_BODY_RE = re.compile(
    r'^\s*feature\s*=\s*"([A-Za-z0-9_-]+)"\s*$'
)
FN_RE = re.compile(
    r"^\s*(?:(?:pub(?:\([^)]*\))?\s+|unsafe\s+|async\s+|const\s+)*)"
    r"fn\s+([A-Za-z_][A-Za-z0-9_]*)\s*\("
)
EXTERNAL_MOD_TEMPLATE = (
    r"^\s*(?:(?:pub(?:\([^)]*\))?\s+|unsafe\s+)*)mod\s+{name}\s*;"
)


class DispositionError(ValueError):
    """The frozen inventory cannot be mapped to current source unambiguously."""


def _read_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise DispositionError(f"{path}: expected a JSON object")
    return value


UPSTREAM_INACTIVE_PATH = REPO_ROOT / "tests/trust-mc/replacement-upstream-inactive.json"

# Reason text is part of the key on purpose. Editing a comment must not be able
# to move a row out of the bar (#gate-upstream-reason-bound).
def _load_upstream_inactive() -> dict[tuple[str, str], str]:
    if not UPSTREAM_INACTIVE_PATH.exists():
        return {}
    data = json.loads(UPSTREAM_INACTIVE_PATH.read_text())
    return {(r["file"], r["harness"]): r["reason"] for r in data.get("rows", [])}


UPSTREAM_INACTIVE = _load_upstream_inactive()


def _row_digest(rows: list[dict[str, Any]]) -> str:
    payload = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(payload).hexdigest()


def _render(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True) + "\n"


def _validate_inventory(path: Path) -> tuple[dict[str, Any], list[dict[str, str]]]:
    data = _read_object(path)
    rows_value = data.get("rows")
    if data.get("schema_version") != 1 or not isinstance(rows_value, list):
        raise DispositionError(f"{path}: expected schema-version-1 inventory rows")

    rows: list[dict[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for index, value in enumerate(rows_value):
        if not isinstance(value, dict) or set(value) != INVENTORY_FIELDS:
            raise DispositionError(
                f"{path}: rows[{index}] must have exactly {sorted(INVENTORY_FIELDS)}"
            )
        if not all(isinstance(value.get(field), str) for field in INVENTORY_FIELDS):
            raise DispositionError(f"{path}: rows[{index}] fields must be strings")
        row = {field: value[field] for field in ("expected", "file", "harness", "lane")}
        if row["expected"] not in EXPECTED_OUTCOMES:
            raise DispositionError(
                f"{path}: rows[{index}] has invalid expectation {row['expected']!r}"
            )
        file_path = Path(row["file"])
        if (
            not row["file"].startswith("tests/")
            or file_path.is_absolute()
            or ".." in file_path.parts
            or not row["file"].endswith(".rs")
        ):
            raise DispositionError(f"{path}: rows[{index}] has unsafe file path")
        expected_lane = "/".join(file_path.parts[:2])
        if row["lane"] != expected_lane:
            raise DispositionError(
                f"{path}: rows[{index}] lane {row['lane']!r} != {expected_lane!r}"
            )
        key = (row["file"], row["harness"])
        if key in seen:
            raise DispositionError(f"{path}: duplicate row {key[0]}::{key[1]}")
        seen.add(key)
        rows.append(row)

    if rows != sorted(rows, key=lambda row: (row["file"], row["harness"])):
        raise DispositionError(f"{path}: rows are not canonically sorted")
    if data.get("denominator") != len(rows):
        raise DispositionError(f"{path}: denominator does not match row count")
    digest = _row_digest(rows)
    if data.get("row_sha256") != digest:
        raise DispositionError(f"{path}: row_sha256 does not match rows")
    return data, rows


def _validate_subsets(
    mixed_rows: list[dict[str, str]],
    proof_path: Path,
    closure_path: Path,
    *,
    inventory_path: Path,
    inventory_digest: str,
) -> tuple[dict[str, Any], dict[str, Any]]:
    proof, proof_rows = _validate_inventory(proof_path)
    expected_proof = [row for row in mixed_rows if row["expected"] == "PROOF"]
    if proof_rows != expected_proof:
        raise DispositionError(f"{proof_path}: not the exact PROOF subset")

    closure = _read_object(closure_path)
    if closure.get("schema_version") != 1:
        raise DispositionError(f"{closure_path}: expected schema_version 1")
    closure_rows = closure.get("rows")
    if not isinstance(closure_rows, list):
        raise DispositionError(f"{closure_path}: missing closure rows")
    closure_keys: list[tuple[str, str, str, str]] = []
    for index, row in enumerate(closure_rows):
        if not isinstance(row, dict) or set(row) != CLOSURE_FIELDS:
            raise DispositionError(
                f"{closure_path}: rows[{index}] must have exactly "
                f"{sorted(CLOSURE_FIELDS)}"
            )
        if row.get("disposition") != "expected-fail":
            raise DispositionError(
                f"{closure_path}: rows[{index}] disposition must be expected-fail"
            )
        if (
            not isinstance(row.get("justification"), str)
            or not row["justification"].strip()
        ):
            raise DispositionError(
                f"{closure_path}: rows[{index}] justification must be nonempty"
            )
        try:
            closure_keys.append(
                (row["file"], row["harness"], row["expected"], row["lane"])
            )
        except KeyError as err:
            raise DispositionError(
                f"{closure_path}: rows[{index}] missing {err.args[0]}"
            ) from err
    expected_non_proof = [
        (row["file"], row["harness"], row["expected"], row["lane"])
        for row in mixed_rows
        if row["expected"] != "PROOF"
    ]
    if closure_keys != expected_non_proof:
        raise DispositionError(f"{closure_path}: not the exact non-PROOF complement")
    if closure.get("denominator") != len(closure_rows):
        raise DispositionError(f"{closure_path}: denominator does not match rows")
    if closure.get("row_sha256") != _row_digest(closure_rows):
        raise DispositionError(f"{closure_path}: row_sha256 does not match rows")
    source = closure.get("source")
    if not isinstance(source, dict):
        raise DispositionError(f"{closure_path}: missing source authority")
    expected_source = {
        "inventory": inventory_path.name,
        "denominator": len(mixed_rows),
        "row_sha256": inventory_digest,
    }
    if source != expected_source:
        raise DispositionError(
            f"{closure_path}: source authority does not match mixed inventory"
        )
    return proof, closure


def _candidate_attribute_block(lines: list[str], fn_index: int) -> str:
    start = fn_index
    while start > 0:
        previous = lines[start - 1].strip()
        if (
            not previous
            or previous.startswith("#")
            or previous.startswith("//")
            or previous.startswith("/*")
            or previous.startswith("*")
            or previous.endswith("*/")
        ):
            start -= 1
            continue
        break
    return "\n".join(lines[start:fn_index])


def _source_candidates(path: Path, bare_harness: str) -> list[dict[str, Any]]:
    lines = path.read_text(encoding="utf-8").splitlines()
    candidates: list[dict[str, Any]] = []
    for index, line in enumerate(lines):
        match = FN_RE.match(line)
        if match is None or match.group(1) != bare_harness:
            continue
        attributes = _candidate_attribute_block(lines, index)
        if PROOF_ATTR_RE.search(attributes) is None:
            continue
        candidates.append(
            {
                "line": index + 1,
                "attributes": attributes,
                "cfg_disabled": CFG_DISABLED_RE.search(attributes) is not None,
                "cfg_disabled_reason": _cfg_disabled_reason(attributes),
                "cfg_features": sorted(set(CFG_FEATURE_RE.findall(attributes))),
            }
        )
    return candidates


CFG_DISABLED_REASON_RE = re.compile(
    r"#\[\s*cfg\s*\(\s*disabled\s*\)\s*\]\s*//\s*(.+?)\s*$", re.MULTILINE
)


def _cfg_disabled_reason(attributes: str) -> str:
    hit = CFG_DISABLED_REASON_RE.search(attributes)
    return hit.group(1) if hit else ""


def _nearest_manifest(path: Path) -> Path | None:
    tests_root = REPO_ROOT / "tests"
    for directory in (path.parent, *path.parents):
        manifest = directory / "Cargo.toml"
        if manifest.is_file():
            return manifest
        if directory == tests_root or directory == REPO_ROOT:
            break
    return None


def _default_features(manifest: Path) -> frozenset[str]:
    # Keep the evidence gate compatible with the repository's Python 3.9
    # floor.  We only need one deliberately narrow TOML field; reject every
    # shape other than a one-line string array instead of using a permissive
    # ad-hoc TOML parser.
    section = ""
    for raw_line in manifest.read_text(encoding="utf-8").splitlines():
        line = raw_line.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("[") and line.endswith("]"):
            section = line[1:-1].strip()
            continue
        if section != "features":
            continue
        match = re.fullmatch(r'default\s*=\s*\[(.*)\]\s*', line)
        if match is None:
            continue
        inner = match.group(1).strip()
        if not inner:
            return frozenset()
        values = [item.strip() for item in inner.split(",")]
        if not all(re.fullmatch(r'"[A-Za-z0-9_-]+"', item) for item in values):
            raise DispositionError(
                f"{manifest}: features.default must be a one-line string array"
            )
        return frozenset(item[1:-1] for item in values)
    return frozenset()


def _source_relative(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError as err:
        raise DispositionError(f"{path}: path is outside repository root") from err


def _module_declared(parent: Path, name: str) -> bool:
    pattern = re.compile(
        EXTERNAL_MOD_TEMPLATE.format(name=re.escape(name)),
        re.MULTILINE,
    )
    return pattern.search(parent.read_text(encoding="utf-8")) is not None


def _default_enabled_file_features(source: Path, manifest: Path) -> set[str]:
    """Validate simple crate/module file feature gates against Cargo defaults.

    A source file can be present in the conventional module graph while an
    inner ``#![cfg(...)]`` removes the entire file.  Treat only the narrow,
    deterministic feature form used by this corpus as source authority; an
    unfamiliar file-level cfg fails closed instead of being credited active.
    """

    defaults = _default_features(manifest)
    required: set[str] = set()
    source_text = source.read_text(encoding="utf-8")
    for body in INNER_CFG_RE.findall(source_text):
        match = CFG_FEATURE_BODY_RE.fullmatch(body)
        if match is None:
            raise DispositionError(
                f"{_source_relative(source)}: unsupported file-level cfg({body})"
            )
        feature = match.group(1)
        if feature not in defaults:
            raise DispositionError(
                f"{_source_relative(source)}: file-level cfg feature {feature!r} "
                f"is not enabled by default in {_source_relative(manifest)}"
            )
        required.add(feature)
    return required


def _cargo_module_binding(source: Path, manifest: Path) -> tuple[list[str], list[str]]:
    """Bind a Cargo source to its module path and default feature gates."""

    lockfile = manifest.with_name("Cargo.lock")
    if not lockfile.is_file():
        raise DispositionError(
            f"{_source_relative(manifest)}: missing Cargo.lock for locked evidence"
        )

    source_root = manifest.parent / "src"
    try:
        relative = source.relative_to(source_root)
    except ValueError as err:
        raise DispositionError(
            f"{source}: cargo source is outside {_source_relative(source_root)}"
        ) from err

    if relative.as_posix() in {"lib.rs", "main.rs"}:
        required = _default_enabled_file_features(source, manifest)
        return [], sorted(required)
    if relative.name == "mod.rs":
        modules = list(relative.parts[:-1])
    else:
        modules = [*relative.parts[:-1], relative.stem]
    if not modules or not all(
        re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", item) for item in modules
    ):
        raise DispositionError(
            f"{_source_relative(source)}: unsupported cargo module path"
        )

    roots = [
        source_root / name
        for name in ("lib.rs", "main.rs")
        if (source_root / name).is_file()
    ]
    if len(roots) != 1:
        raise DispositionError(
            f"{_source_relative(manifest)}: expected exactly one src/lib.rs or src/main.rs"
        )
    parent = roots[0]
    required = _default_enabled_file_features(parent, manifest)
    module_dir = source_root
    for index, name in enumerate(modules):
        if not _module_declared(parent, name):
            raise DispositionError(
                f"{_source_relative(source)}: module {name!r} is not declared by "
                f"{_source_relative(parent)}"
            )
        candidates = [module_dir / f"{name}.rs", module_dir / name / "mod.rs"]
        existing = [candidate for candidate in candidates if candidate.is_file()]
        if len(existing) != 1:
            raise DispositionError(
                f"{_source_relative(source)}: module {name!r} resolves to "
                f"{len(existing)} source files"
            )
        child = existing[0]
        required.update(_default_enabled_file_features(child, manifest))
        if index + 1 == len(modules):
            if child.resolve() != source.resolve():
                raise DispositionError(
                    f"{_source_relative(source)}: module path resolves to "
                    f"{_source_relative(child)}"
                )
        else:
            parent = child
            module_dir = child.parent if child.name == "mod.rs" else child.parent / child.stem
    return modules, sorted(required)


def _cargo_module_path(source: Path, manifest: Path) -> list[str]:
    """Return the source's validated, conventional reachable module path."""

    modules, _ = _cargo_module_binding(source, manifest)
    return modules


def _qualified_driver_harness(
    local_harness: str,
    *,
    execution: dict[str, Any],
    source_path: Path,
    manifest: Path | None,
) -> str:
    if execution["executor"] != "cargo":
        return local_harness
    if manifest is None:
        raise DispositionError(f"{_source_relative(source_path)}: cargo executor has no manifest")
    modules, _ = _cargo_module_binding(source_path, manifest)
    return "::".join([*modules, local_harness])


def _plan_row(row: dict[str, str]) -> dict[str, Any]:
    source_path = REPO_ROOT / row["file"]
    if not source_path.is_file():
        raise DispositionError(f"{row['file']}::{row['harness']}: source file is missing")

    manifest = _nearest_manifest(source_path)
    execution: dict[str, Any]
    if manifest is None:
        execution = {"executor": "single-file"}
    else:
        _, required_features = _cargo_module_binding(source_path, manifest)
        execution = {
            "executor": "cargo",
            "cargo_manifest": _source_relative(manifest),
            "cargo_dir": _source_relative(manifest.parent),
        }
        if required_features:
            execution["required_features"] = required_features

    active = extract_proof_harnesses(source_path)
    driver_harness: str | None = None
    resolution: str | None = None
    if row["harness"] in active:
        driver_harness = row["harness"]
        resolution = "exact"
    else:
        aliases = [name for name in active if name.rsplit("::", 1)[-1] == row["harness"]]
        if len(aliases) == 1:
            driver_harness = aliases[0]
            resolution = "unique-qualified-alias"
        elif len(aliases) > 1:
            raise DispositionError(
                f"{row['file']}::{row['harness']}: ambiguous qualified aliases {aliases}"
            )

    base = {**row, **execution}
    if driver_harness is not None:
        return {
            **base,
            "disposition": "active",
            "driver_harness": _qualified_driver_harness(
                driver_harness,
                execution=execution,
                source_path=source_path,
                manifest=manifest,
            ),
            "resolution": resolution,
        }

    candidates = _source_candidates(source_path, row["harness"])
    if len(candidates) != 1:
        raise DispositionError(
            f"{row['file']}::{row['harness']}: expected one source proof candidate, "
            f"found {len(candidates)}"
        )
    candidate = candidates[0]
    if candidate["cfg_disabled"]:
        # UPSTREAM-inactive vs LOCALLY-inactive. A row upstream Kani disabled
        # because CBMC could not run it is not something Kani DOES, so it sits
        # outside the replacement BAR (never outside the historical
        # DENOMINATOR). Anything WE disable stays inside the bar and blocks the
        # gate — that is the anti-cheat, and it is why the frozen authority is
        # keyed on the upstream reason text as well as the row identity.
        key = (row["file"], row["harness"])
        frozen_reason = UPSTREAM_INACTIVE.get(key)
        current_reason = candidate.get("cfg_disabled_reason") or ""
        upstream = frozen_reason is not None and frozen_reason == current_reason
        return {
            **base,
            "disposition": "inactive",
            "inactive_origin": "upstream" if upstream else "local",
            "execution_credit": False,
            "proof_credit": False,
            "reason": "cfg-disabled-upstream" if upstream else "cfg-disabled",
            "upstream_reason": frozen_reason if upstream else None,
            "source_line": candidate["line"],
        }

    cfg_features = candidate["cfg_features"]
    if cfg_features:
        manifest = _nearest_manifest(source_path)
        if manifest is None:
            raise DispositionError(
                f"{row['file']}::{row['harness']}: cfg(feature) has no Cargo.toml"
            )
        defaults = _default_features(manifest)
        if all(feature in defaults for feature in cfg_features):
            required_features = sorted(
                set(execution.get("required_features", [])) | set(cfg_features)
            )
            return {
                **base,
                "disposition": "active",
                "driver_harness": _qualified_driver_harness(
                    row["harness"],
                    execution=execution,
                    source_path=source_path,
                    manifest=manifest,
                ),
                "resolution": "cargo-default-feature",
                "cargo_manifest": _source_relative(manifest),
                "required_features": required_features,
                "source_line": candidate["line"],
            }
        raise DispositionError(
            f"{row['file']}::{row['harness']}: cfg features {cfg_features} are not "
            f"all enabled by default in {_source_relative(manifest)}"
        )

    raise DispositionError(
        f"{row['file']}::{row['harness']}: source proof candidate is absent from "
        "the active extractor without a recognized cfg disposition"
    )


def _subset_summary(
    rows: list[dict[str, Any]], expected_proof: bool, authority_digest: str
) -> dict[str, Any]:
    subset = [
        row
        for row in rows
        if (row["expected"] == "PROOF") is expected_proof
    ]
    active = [row for row in subset if row["disposition"] == "active"]
    inactive = [row for row in subset if row["disposition"] == "inactive"]
    upstream_inactive = [
        row for row in inactive if row.get("inactive_origin") == "upstream"
    ]
    local_inactive = [
        row for row in inactive if row.get("inactive_origin") != "upstream"
    ]
    inventory_rows = [
        {field: row[field] for field in ("expected", "file", "harness", "lane")}
        for row in subset
    ]
    active_rows = [
        {field: row[field] for field in ("expected", "file", "harness", "lane")}
        for row in active
    ]
    inactive_rows = [
        {field: row[field] for field in ("expected", "file", "harness", "lane")}
        for row in inactive
    ]
    upstream_rows = [
        {field: row[field] for field in ("expected", "file", "harness", "lane")}
        for row in upstream_inactive
    ]
    local_rows = [
        {field: row[field] for field in ("expected", "file", "harness", "lane")}
        for row in local_inactive
    ]
    supersession: dict[str, int] = {}
    for row in upstream_inactive:
        label = row.get("upstream_reason") or "unattributed"
        supersession[label] = supersession.get(label, 0) + 1
    return {
        "historical": len(subset),
        "active": len(active),
        # The replacement BAR: what the incumbent actually does.
        "bar": len(active),
        "inactive_zero_credit": len(inactive),
        "upstream_inactive": len(upstream_inactive),
        "local_inactive": len(local_inactive),
        "supersession_candidates": dict(sorted(supersession.items())),
        "upstream_inactive_row_sha256": _row_digest(upstream_rows),
        "local_inactive_row_sha256": _row_digest(local_rows),
        "authority_row_sha256": authority_digest,
        "inventory_row_sha256": _row_digest(inventory_rows),
        "active_inventory_row_sha256": _row_digest(active_rows),
        "inactive_inventory_row_sha256": _row_digest(inactive_rows),
    }


def build_dispositions(
    inventory_path: Path,
    proof_path: Path,
    closure_path: Path,
) -> dict[str, Any]:
    inventory, mixed_rows = _validate_inventory(inventory_path)
    proof, closure = _validate_subsets(
        mixed_rows,
        proof_path,
        closure_path,
        inventory_path=inventory_path,
        inventory_digest=str(inventory["row_sha256"]),
    )
    plan_rows = [_plan_row(row) for row in mixed_rows]
    resolutions = Counter(
        row.get("resolution", row.get("reason", "unknown")) for row in plan_rows
    )
    active_rows = [row for row in plan_rows if row["disposition"] == "active"]
    inactive_rows = [row for row in plan_rows if row["disposition"] == "inactive"]
    return {
        "schema_version": 1,
        "artifact_kind": "trust-mc.replacement_harness_dispositions",
        "authority": {
            "inventory": _source_relative(inventory_path),
            "denominator": inventory["denominator"],
            "row_sha256": inventory["row_sha256"],
            "proof_inventory": _source_relative(proof_path),
            "proof_row_sha256": proof["row_sha256"],
            "non_proof_closure": _source_relative(closure_path),
            "non_proof_closure_row_sha256": closure["row_sha256"],
        },
        "summary": {
            "historical_total": len(plan_rows),
            "active": len(active_rows),
            "inactive_accounted": len(inactive_rows),
            "resolution_counts": dict(sorted(resolutions.items())),
            "active_plan_row_sha256": _row_digest(active_rows),
            "inactive_plan_row_sha256": _row_digest(inactive_rows),
            "plan_row_sha256": _row_digest(plan_rows),
            "proof": _subset_summary(
                plan_rows, True, str(proof["row_sha256"])
            ),
            "non_proof": _subset_summary(
                plan_rows, False, str(closure["row_sha256"])
            ),
        },
        "rows": plan_rows,
    }


def _read_records(path: Path) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            value = json.loads(line)
        except json.JSONDecodeError as err:
            raise DispositionError(f"{path}:{line_number}: invalid JSON: {err}") from err
        if not isinstance(value, dict):
            raise DispositionError(f"{path}:{line_number}: record is not an object")
        records.append(value)
    return records


def validate_runtime_records(
    dispositions: dict[str, Any], records_path: Path
) -> dict[str, Any]:
    plan_rows = dispositions["rows"]
    records = _read_records(records_path)
    by_key: dict[tuple[str, str], dict[str, Any]] = {}
    for index, record in enumerate(records):
        if record.get("schema_version") != 2:
            raise DispositionError(
                f"{records_path}: record {index} is not schema version 2"
            )
        key = (record.get("file"), record.get("harness"))
        if not all(isinstance(item, str) and item for item in key):
            raise DispositionError(f"{records_path}: record {index} has invalid identity")
        if key in by_key:
            raise DispositionError(f"{records_path}: duplicate record {key[0]}::{key[1]}")
        by_key[key] = record

    plan_keys = {(row["file"], row["harness"]) for row in plan_rows}
    if set(by_key) != plan_keys:
        missing = sorted(plan_keys - set(by_key))
        extra = sorted(set(by_key) - plan_keys)
        raise DispositionError(
            f"{records_path}: runtime row set drift; missing={missing[:3]}, extra={extra[:3]}"
        )

    for row in plan_rows:
        key = (row["file"], row["harness"])
        record = by_key[key]
        if record.get("expected") != row["expected"]:
            raise DispositionError(f"{records_path}: expectation drift for {key[0]}::{key[1]}")
        execution = record.get("metadata", {}).get("execution", {})
        if row["disposition"] == "active":
            if (
                record.get("verdict") == "SKIP"
                or record.get("status") == "SKIP"
                or execution.get("state") not in ACTIVE_EXECUTION_STATES
            ):
                raise DispositionError(
                    f"{records_path}: active row was not executed: {key[0]}::{key[1]}"
                )
        elif (
            record.get("verdict") != "SKIP"
            or record.get("status") != "SKIP"
            or execution.get("state") != "inactive_accounted"
            or execution.get("details") != row["reason"]
        ):
            raise DispositionError(
                f"{records_path}: inactive row received execution/proof credit: {key[0]}::{key[1]}"
            )

    summary = dispositions["summary"]
    return {
        "schema_version": 1,
        "artifact_kind": "trust-mc.replacement_runtime_accounting",
        "authority": dispositions["authority"],
        "historical_total": summary["historical_total"],
        "active_executed": summary["active"],
        "inactive_accounted": summary["inactive_accounted"],
        "proof": {
            "historical": summary["proof"]["historical"],
            "active_executed": summary["proof"]["active"],
            "inactive_zero_credit": summary["proof"]["inactive_zero_credit"],
            "authority_row_sha256": summary["proof"]["authority_row_sha256"],
            "active_inventory_row_sha256": summary["proof"]["active_inventory_row_sha256"],
        },
        "non_proof": {
            "historical": summary["non_proof"]["historical"],
            "active_executed": summary["non_proof"]["active"],
            "inactive_zero_credit": summary["non_proof"]["inactive_zero_credit"],
            "authority_row_sha256": summary["non_proof"]["authority_row_sha256"],
            "active_inventory_row_sha256": summary["non_proof"]["active_inventory_row_sha256"],
        },
        "runtime_identity_row_sha256": _row_digest(
            [
                {
                    "expected": row["expected"],
                    "file": row["file"],
                    "harness": row["harness"],
                    "lane": row["lane"],
                }
                for row in plan_rows
            ]
        ),
    }


def _emit_shell_plan(rows: Iterable[dict[str, Any]]) -> None:
    # ASCII unit separator is non-whitespace to Bash IFS, so adjacent empty
    # fields (reason / cargo_dir) are not collapsed the way TSV fields are.
    for row in rows:
        values = (
            row["file"],
            row["harness"],
            row.get("driver_harness", ""),
            row["expected"],
            row["lane"],
            row["disposition"],
            row.get("reason", ""),
            row["executor"],
            row.get("cargo_dir", ""),
        )
        if any("\x1f" in value or "\r" in value or "\n" in value for value in values):
            raise DispositionError("shell-plan-unsafe disposition field")
        sys.stdout.write("\x1f".join(values) + "\n")


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, default=DEFAULT_INVENTORY)
    parser.add_argument("--proof-inventory", type=Path, default=DEFAULT_PROOF_INVENTORY)
    parser.add_argument("--non-proof-closure", type=Path, default=DEFAULT_NON_PROOF)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true", help="check output; write nothing")
    parser.add_argument(
        "--emit-shell-plan",
        action="store_true",
        help="emit the checked execution plan with ASCII unit separators",
    )
    parser.add_argument("--records-jsonl", type=Path, help="validate a runtime JSONL record set")
    parser.add_argument("--runtime-accounting-output", type=Path)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        dispositions = build_dispositions(
            args.inventory.resolve(),
            args.proof_inventory.resolve(),
            args.non_proof_closure.resolve(),
        )
        rendered = _render(dispositions)
        if args.check or args.emit_shell_plan or args.records_jsonl:
            if args.output.read_text(encoding="utf-8") != rendered:
                raise DispositionError(f"{args.output}: disposition artifact is stale")
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(rendered, encoding="utf-8")

        runtime = None
        if args.records_jsonl is not None:
            runtime = validate_runtime_records(dispositions, args.records_jsonl)
            if args.runtime_accounting_output is None:
                raise DispositionError(
                    "--records-jsonl requires --runtime-accounting-output"
                )
            args.runtime_accounting_output.parent.mkdir(parents=True, exist_ok=True)
            args.runtime_accounting_output.write_text(_render(runtime), encoding="utf-8")
        elif args.runtime_accounting_output is not None:
            raise DispositionError(
                "--runtime-accounting-output requires --records-jsonl"
            )

        if args.emit_shell_plan:
            _emit_shell_plan(dispositions["rows"])
        else:
            summary = dispositions["summary"]
            action = "OK" if args.check or args.records_jsonl else "wrote"
            print(
                "replacement_harness_dispositions: "
                f"{action} historical={summary['historical_total']} "
                f"active={summary['active']} inactive={summary['inactive_accounted']} "
                f"proof_active={summary['proof']['active']} "
                f"proof_inactive={summary['proof']['inactive_zero_credit']}"
            )
        return 0
    except (DispositionError, OSError, json.JSONDecodeError) as err:
        print(f"replacement_harness_dispositions: ERROR: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
