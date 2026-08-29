#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import hashlib
import json
import re
import shlex
import shutil
import subprocess
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from compiletest_report_paths import MEASUREMENT_FINGERPRINT_PATHS, REPORT_TOOL_PATHS
from ay_manifest_pin import expected_ay_pin_from_locked_workspace
from driver_binary_attestation import attest_driver_binary, find_workspace_driver

EXPECTED_MANIFEST_SCHEMA_VERSION = 1
OUTPUT_SCHEMA_VERSION = 2
FINAL_PROOF_MARKER = "final_marker=PROOF"
DEFAULT_INVENTORY = (
    Path(__file__).resolve().parent.parent
    / "tests"
    / "trust-mc"
    / "replacement-harness-inventory.proof.json"
)
FINAL_VERDICT_RE = re.compile(r"\[AY:(PROOF|CTREX|UNKNOWN|ERROR)\]")
PROOF_QUALIFIERS_RE = re.compile(r"\[AY:PROOF_QUALIFIERS:([^]]+)\]")
SOUND_FALLBACK_RE = re.compile(r"\[AY:SOUND_FALLBACK:([0-9]+)\]")
SOLVER_COMMIT_RE = re.compile(r"^build\.commit=([0-9a-fA-F]{7,40})", re.MULTILINE)
SOLVER_STAMP_COMMIT_RE = re.compile(r"[.+]([0-9a-fA-F]{7,40})@")
DIRTY_PATH_RE = re.compile(
    r"(\.rs$|(^|/)Cargo\.toml$|(^|/)Cargo\.lock$|(^|/)rust-toolchain\.toml$)"
)

HarnessKey = tuple[str, str]


def _read_json_object(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except OSError as err:
        raise ValueError(f"{path}: failed to read JSON: {err}") from err
    except json.JSONDecodeError as err:
        raise ValueError(f"{path}: invalid JSON: {err}") from err
    if not isinstance(data, dict):
        raise ValueError(f"{path}: expected JSON object, got {type(data).__name__}")
    return data


def _repo_root_from_script() -> Path:
    return Path(__file__).resolve().parent.parent


def _git_text(repo_root: Path, args: list[str]) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=repo_root,
        text=True,
        capture_output=True,
        check=False,
    )
    if result.returncode != 0:
        stderr = result.stderr.strip()
        details = f": {stderr}" if stderr else ""
        raise ValueError(f"{repo_root}: git {' '.join(args)} failed{details}")
    return result.stdout


def _current_head(repo_root: Path) -> str:
    head = _git_text(repo_root, ["rev-parse", "HEAD"]).strip()
    if not re.fullmatch(r"[0-9a-fA-F]{40}", head):
        raise ValueError(f"{repo_root}: git rev-parse HEAD returned unusable commit {head!r}")
    return head.lower()


def _current_tree_state(repo_root: Path) -> str:
    status = _git_text(repo_root, ["status", "--porcelain=v1", "--untracked-files=all"])
    report_tool_paths = set(REPORT_TOOL_PATHS)
    for line in status.splitlines():
        path = line[3:]
        if path.startswith("reports/"):
            continue
        if DIRTY_PATH_RE.search(path) or path in report_tool_paths:
            return "dirty"
    return "clean"


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
        raise ValueError(f"{repo_root}: failed to compute tree fingerprint{details}")
    return hashlib.sha256(result.stdout).hexdigest()


def _solver_binary_attestation(solver: str, expected_pin: str) -> dict[str, Any]:
    solver_path = shutil.which(solver)
    if solver_path is None:
        raise ValueError(f"solver {solver!r} not found in PATH")

    result = subprocess.run(
        [solver_path, "--version"],
        text=True,
        capture_output=True,
        check=False,
    )
    version = result.stdout if result.stdout else result.stderr
    commit = _extract_solver_commit(version)
    if commit is None:
        raise ValueError(f"{solver_path}: unable to extract solver commit from --version output")
    if not expected_pin.startswith(commit.lower()) and commit.lower() != expected_pin:
        raise ValueError(
            f"{solver_path}: solver commit {commit} does not match AY pin {expected_pin}"
        )
    return {
        "name": solver,
        "path": solver_path,
        "version": version.strip(),
        "commit": commit,
    }


def _extract_solver_commit(version: str) -> str | None:
    match = SOLVER_COMMIT_RE.search(version)
    if match is not None:
        return match.group(1).lower()
    match = SOLVER_STAMP_COMMIT_RE.search(version)
    if match is not None:
        return match.group(1).lower()
    return None


def _normalize_file(value: Any, *, repo_root: Path, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label}: missing non-empty file")
    path = value.strip().replace("\\", "/")
    repo_prefix = repo_root.as_posix().rstrip("/") + "/"
    if path.startswith(repo_prefix):
        path = path[len(repo_prefix) :]
    while path.startswith("./"):
        path = path[2:]
    if not path.startswith("tests/"):
        raise ValueError(
            f"{label}: file {value!r} does not normalize to a canonical tests/ path"
        )
    return path


def _load_proof_inventory(path: Path, repo_root: Path) -> set[HarnessKey]:
    inventory = _read_json_object(path)
    rows = inventory.get("rows")
    if not isinstance(rows, list):
        raise ValueError(f"{path}: expected rows array")

    keys: set[HarnessKey] = set()
    for index, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"{path}: rows[{index}] must be an object")
        if row.get("expected") != "PROOF":
            raise ValueError(f"{path}: rows[{index}].expected {row.get('expected')!r} != 'PROOF'")
        file_name = _normalize_file(
            row.get("file"),
            repo_root=repo_root,
            label=f"{path}: rows[{index}]",
        )
        harness = row.get("harness")
        if not isinstance(harness, str) or not harness.strip():
            raise ValueError(f"{path}: rows[{index}] missing non-empty harness")
        key = (file_name, harness)
        if key in keys:
            raise ValueError(f"{path}: duplicate proof inventory harness {file_name}::{harness}")
        keys.add(key)

    denominator = inventory.get("denominator")
    if denominator is not None and denominator != len(keys):
        raise ValueError(f"{path}: denominator {denominator!r} does not match {len(keys)} rows")
    return keys


def _manifest_runs(manifest: dict[str, Any], *, label: str) -> list[dict[str, Any]]:
    if manifest.get("schema_version") != EXPECTED_MANIFEST_SCHEMA_VERSION:
        raise ValueError(
            f"{label}: schema_version {manifest.get('schema_version')!r} "
            f"!= {EXPECTED_MANIFEST_SCHEMA_VERSION}"
        )
    runs = manifest.get("runs")
    if not isinstance(runs, list):
        raise ValueError(f"{label}: expected runs array")
    normalized: list[dict[str, Any]] = []
    for index, run in enumerate(runs):
        if not isinstance(run, dict):
            raise ValueError(f"{label}: runs[{index}] must be an object")
        normalized.append(run)
    if not normalized:
        raise ValueError(f"{label}: runs must not be empty")
    return normalized


def _resolve_path(value: Any, *, manifest_path: Path, repo_root: Path, label: str) -> Path:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label}: missing non-empty path")
    path = Path(value)
    if path.is_absolute():
        return path
    manifest_relative = manifest_path.parent / path
    if manifest_relative.exists():
        return manifest_relative
    return repo_root / path


def _command_words(value: Any, *, label: str) -> list[str]:
    if isinstance(value, str):
        words = shlex.split(value)
    elif isinstance(value, list) and all(isinstance(item, str) for item in value):
        words = list(value)
    else:
        raise ValueError(f"{label}: command must be a string or string array")
    while words and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*=.*", words[0]):
        words.pop(0)
    if not words:
        raise ValueError(f"{label}: command is empty after environment assignments")
    return words


def _validate_command(
    command: Any,
    *,
    repo_root: Path,
    file_name: str,
    harness: str,
    label: str,
) -> None:
    words = _command_words(command, label=label)
    exe = words[0].replace("\\", "/")
    if not (
        exe in {"./scripts/trust-mc", "scripts/trust-mc"}
        or exe.endswith("/scripts/trust-mc")
    ):
        raise ValueError(f"{label}: command must invoke ./scripts/trust-mc, got {words[0]!r}")

    args = words[1:]
    if "unstable-options" not in _flag_values(args, "-Z"):
        raise ValueError(f"{label}: command missing '-Z unstable-options'")
    if "ay" not in _flag_values(args, "--backend"):
        raise ValueError(f"{label}: command missing '--backend=ay'")
    if "ay" not in _flag_values(args, "--ay-solver"):
        raise ValueError(f"{label}: command missing '--ay-solver=ay'")
    if "--ay-chc" not in args:
        raise ValueError(f"{label}: command missing '--ay-chc'")
    if "mem" not in _flag_values(args, "--ay-chc-track"):
        raise ValueError(f"{label}: command missing '--ay-chc-track=mem'")
    harness_values = _flag_values(args, "--harness")
    if harness not in harness_values:
        raise ValueError(f"{label}: command harness {harness_values!r} does not include {harness!r}")

    positionals = _positionals(args)
    normalized_positionals = [
        _normalize_file(arg, repo_root=repo_root, label=f"{label}: command positional")
        for arg in positionals
        if _looks_like_test_file(arg)
    ]
    if file_name not in normalized_positionals:
        raise ValueError(
            f"{label}: command file arguments {normalized_positionals!r} do not include {file_name!r}"
        )


def _flag_values(args: list[str], flag: str) -> list[str]:
    values: list[str] = []
    for index, arg in enumerate(args):
        if arg == flag and index + 1 < len(args):
            values.append(args[index + 1])
        elif arg.startswith(f"{flag}="):
            values.append(arg.split("=", 1)[1])
        elif flag == "-Z" and arg.startswith("-Z") and arg != "-Z":
            values.append(arg[2:])
    return values


def _positionals(args: list[str]) -> list[str]:
    consumed: set[int] = set()
    flags_with_values = {"-Z", "--backend", "--ay-solver", "--ay-chc-track", "--harness"}
    for index, arg in enumerate(args):
        if arg in flags_with_values:
            consumed.add(index)
            if index + 1 < len(args):
                consumed.add(index + 1)
        elif any(arg.startswith(f"{flag}=") for flag in flags_with_values if flag != "-Z"):
            consumed.add(index)
        elif arg.startswith("-Z") and arg != "-Z":
            consumed.add(index)
        elif arg.startswith("-"):
            consumed.add(index)
    return [arg for index, arg in enumerate(args) if index not in consumed]


def _looks_like_test_file(value: str) -> bool:
    normalized = value.replace("\\", "/")
    return normalized.endswith(".rs") and (
        normalized.startswith("tests/") or "/tests/" in normalized
    )


def _validate_log(text: str, *, harness: str, label: str) -> None:
    if f"Checking harness {harness}..." not in text:
        raise ValueError(f"{label}: log does not show 'Checking harness {harness}...'")

    final_verdicts = FINAL_VERDICT_RE.findall(text)
    if not final_verdicts:
        raise ValueError(f"{label}: log has no final [AY:*] verification marker")
    final_verdict = final_verdicts[-1]
    if final_verdict != "PROOF":
        raise ValueError(f"{label}: final verification marker is {final_verdict}, not PROOF")

    qualifiers = PROOF_QUALIFIERS_RE.findall(text)
    if not qualifiers:
        raise ValueError(f"{label}: log missing [AY:PROOF_QUALIFIERS:clean]")
    if qualifiers[-1] != "clean":
        raise ValueError(f"{label}: proof qualifiers {qualifiers[-1]!r} are not clean")

    fallback_counts = [int(value) for value in SOUND_FALLBACK_RE.findall(text)]
    if any(count != 0 for count in fallback_counts):
        raise ValueError(f"{label}: nonzero sound fallback marker(s) {fallback_counts!r}")
    if "[AY:TRANSLATION_DROP_REASON:" in text:
        raise ValueError(f"{label}: translation-drop markers are not clean proof evidence")
    if "[AY:DEMOTION_REASONS:" in text:
        raise ValueError(f"{label}: demotion markers are not clean proof evidence")
    if "[AY:RETRY" in text:
        raise ValueError(f"{label}: retry markers are not clean proof evidence")


def _derive_rows(
    manifest_path: Path,
    manifest: dict[str, Any],
    *,
    repo_root: Path,
    proof_keys: set[HarnessKey],
) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    seen: set[HarnessKey] = set()
    for index, run in enumerate(_manifest_runs(manifest, label=str(manifest_path))):
        label = f"{manifest_path}: runs[{index}]"
        file_name = _normalize_file(run.get("file"), repo_root=repo_root, label=label)
        harness = run.get("harness")
        if not isinstance(harness, str) or not harness.strip():
            raise ValueError(f"{label}: missing non-empty harness")
        key = (file_name, harness)
        if key not in proof_keys:
            raise ValueError(f"{label}: {file_name}::{harness} is not in the proof inventory")
        if key in seen:
            raise ValueError(f"{label}: duplicate direct proof run {file_name}::{harness}")
        seen.add(key)

        exit_code = run.get("exit_code")
        if exit_code != 0:
            raise ValueError(f"{label}: exit_code {exit_code!r} is not 0")
        _validate_command(
            run.get("command"),
            repo_root=repo_root,
            file_name=file_name,
            harness=harness,
            label=label,
        )
        log_path = _resolve_path(
            run.get("log"),
            manifest_path=manifest_path,
            repo_root=repo_root,
            label=label,
        )
        try:
            log_text = log_path.read_text(encoding="utf-8", errors="replace")
        except OSError as err:
            raise ValueError(f"{label}: failed to read log {log_path}: {err}") from err
        _validate_log(log_text, harness=harness, label=label)

        row: dict[str, Any] = {
            "file": file_name,
            "harness": harness,
            "verdict": "PROOF",
            "status": "PASS",
            "expected": "PROOF",
            "sound_fallback_count": 0,
            "trusted_proof": True,
            "proof_qualifiers": "clean",
            "translation_drop_reasons": {},
            "execution_state": "complete",
            "execution_details": FINAL_PROOF_MARKER,
        }
        time_sec = run.get("time_sec")
        if (
            isinstance(time_sec, (int, float))
            and not isinstance(time_sec, bool)
            and time_sec >= 0
        ):
            row["time_sec"] = time_sec
        elif time_sec is not None:
            raise ValueError(f"{label}: time_sec {time_sec!r} must be a nonnegative number")
        rows.append(row)

    return sorted(rows, key=lambda row: (row["file"], row["harness"]))


def _summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "rows": len(rows),
        "total": len(rows),
        "pass": len(rows),
        "proof": len(rows),
        "known_fp": 0,
        "trusted_proof": len(rows),
        "ctrex": 0,
        "unknown": 0,
        "error": 0,
        "bmc": 0,
        "fail": 0,
        "xfail": 0,
        "skip": 0,
        "ctrex_breakdown": {
            "encoding_gap": 0,
            "over_approximation": 0,
            "genuine": 0,
            "unknown": 0,
        },
        "proof_breakdown": {
            "clean": len(rows),
            "should_panic": 0,
            "crosschecked": 0,
            "sound_qualified": 0,
            "mem_overapprox_qualified": 0,
        },
        "execution_complete": len(rows),
        "execution_gated": 0,
        "execution_breakdown": {"complete": len(rows)},
    }


def derive_direct_driver_report(
    manifest_path: Path,
    manifest: dict[str, Any],
    *,
    repo_root: Path,
    inventory_path: Path,
    solver: str,
) -> dict[str, Any]:
    proof_keys = _load_proof_inventory(inventory_path, repo_root)
    rows = _derive_rows(manifest_path, manifest, repo_root=repo_root, proof_keys=proof_keys)
    ay_pin = expected_ay_pin_from_locked_workspace(repo_root).lower()
    head = _current_head(repo_root)
    driver_binary = attest_driver_binary(
        find_workspace_driver(repo_root),
        expected_trust_mc_sha=head,
        expected_ay_pin=ay_pin,
    )
    return {
        "schema_version": OUTPUT_SCHEMA_VERSION,
        "report_status": "current",
        "commit": head,
        "tree_state": _current_tree_state(repo_root),
        "tree_fingerprint": _current_tree_fingerprint(repo_root),
        "date": datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "ay_pin": ay_pin,
        "replacement_evidence": True,
        "solver": solver,
        "solver_binary": _solver_binary_attestation(solver, ay_pin),
        "driver_binary": driver_binary,
        "source": "direct-driver",
        "summary": _summary(rows),
        "harnesses": rows,
    }
