#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Run the source-bound frozen replacement corpus through trust-mc and AY.

This is the focused replacement-public lane for the clean public
``ay-compiletest.sh`` runner.  It does not emulate compiletest or synthesize
proof metadata: every report field comes from an exact driver invocation, a
driver marker, checked source disposition, or current repository authority.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time
from collections import Counter
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable


SCRIPT_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPT_DIR.parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from ay_manifest_pin import expected_ay_pin_from_cargo_toml
from compiletest_report_contract import (
    _current_head,
    _current_tree_fingerprint,
    _current_tree_state,
)
from driver_binary_attestation import attest_driver_binary
import replacement_harness_dispositions as dispositions


DEFAULT_REPORT = REPO_ROOT / "reports/compiletest-per-harness-latest-trust-mc.json"
DEFAULT_TSV = REPO_ROOT / "reports/compiletest-per-harness-latest-trust-mc.tsv"
DEFAULT_RUN_MANIFEST = REPO_ROOT / "reports/replacement-public-run-manifest.json"
GENERATOR = REPO_ROOT / "tools/replacement-inventory/generate_inventory.py"
FINAL_VERDICT_RE = re.compile(r"\[AY:(PROOF|CTREX|UNKNOWN|ERROR)\]")
CHECKING_HARNESS_RE = re.compile(r"(?m)^Checking harness (.+)\.\.\.$")
SOLVER_COMMIT_RE = re.compile(r"^build\.commit=([0-9a-fA-F]{7,40})", re.MULTILINE)
SOLVER_STAMP_COMMIT_RE = re.compile(r"[.+]([0-9a-fA-F]{7,40})@")
MARKER_RES = {
    "ctrex": re.compile(r"\[AY:CTREX_CAT:([^]]+)\]"),
    "effective_success": re.compile(r"\[AY:EFFECTIVE_SUCCESS:([^]]+)\]"),
    "sound_fallback": re.compile(r"\[AY:SOUND_FALLBACK:([0-9]+)\]"),
    "unknown_quality": re.compile(r"\[AY:UNKNOWN_QUALITY:([^]]+)\]"),
    "unknown_reason": re.compile(r"\[AY:UNKNOWN_REASON:([^]]+)\]"),
    "proof_qualifiers": re.compile(r"\[AY:PROOF_QUALIFIERS:([^]]+)\]"),
    "demotion": re.compile(r"\[AY:DEMOTION_REASONS:([^]]+)\]"),
    "translation_drop": re.compile(r"\[AY:TRANSLATION_DROP_REASON:([^]]+)\]"),
    "retry_attempts": re.compile(r"\[AY:RETRY_ATTEMPTS:([^]]+)\]"),
    "retry_attempt": re.compile(r"\[AY:RETRY_ATTEMPT:([^]]+)\]"),
    "retry_resolved_by": re.compile(r"\[AY:RETRY_RESOLVED_BY:([^]]+)\]"),
    "retry_final": re.compile(r"\[AY:RETRY_FINAL:([^]]+)\]"),
    "retry_context": re.compile(r"\[AY:RETRY_CONTEXT:([^]]+)\]"),
}
RUSTC_ERROR_RE = re.compile(r"(?m)^error(?:\[[A-Z0-9]+\])?:|^error: aborting due to")
ARTIFACT_ERROR_RE = re.compile(
    r"No such file or directory \(os error 2\)|Failed to process |"
    r"Failed to read CHC SMT file:|\.symtab\.(?:out|smt2)"
)


class ReplacementRunError(ValueError):
    """The public replacement run cannot produce truthful evidence."""


@dataclass(frozen=True)
class RunnerConfig:
    driver: Path
    solver: str
    timeout_seconds: int
    report_dir: Path
    target_dir: Path
    verbose: bool = False


@dataclass(frozen=True)
class Invocation:
    command: list[str]
    cwd: Path
    env: dict[str, str]
    log_path: Path


@dataclass(frozen=True)
class ProcessResult:
    returncode: int
    output: str
    elapsed_seconds: float
    timed_out: bool = False


ProcessRunner = Callable[[dict[str, Any], Invocation, RunnerConfig], ProcessResult]


def _last(pattern: re.Pattern[str], text: str) -> str:
    matches = pattern.findall(text)
    return matches[-1] if matches else ""


def _split_label_details(value: str) -> tuple[str, str]:
    if ":" not in value:
        return value, ""
    label, details = value.split(":", 1)
    return label, details


def _extract_solver_commit(version: str) -> str:
    match = SOLVER_COMMIT_RE.search(version)
    if match is None:
        match = SOLVER_STAMP_COMMIT_RE.search(version)
    if match is None:
        raise ReplacementRunError(
            "ay --version does not include a 7- to 40-character build commit"
        )
    return match.group(1).lower()


def solver_attestation(solver: str, expected_pin: str) -> dict[str, str]:
    if solver != "ay":
        raise ReplacementRunError(
            f"replacement-public requires solver 'ay', got {solver!r}"
        )
    # The driver runs $TRUST_MC_AY_BIN in preference to PATH (and never falls
    # back to PATH while it is set), so attest that binary when it is named.
    solver_path = os.environ.get("TRUST_MC_AY_BIN") or shutil.which(solver)
    if solver_path is None:
        raise ReplacementRunError("ay solver binary not found in PATH")
    result = subprocess.run(
        [solver_path, "--version"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    version = result.stdout.strip()
    if result.returncode != 0 or not version:
        raise ReplacementRunError(f"unable to attest {solver_path} --version")
    commit = _extract_solver_commit(version)
    if not expected_pin.lower().startswith(commit):
        raise ReplacementRunError(
            f"ay binary commit {commit} does not match pinned AY {expected_pin}"
        )
    return {
        "name": "ay",
        "path": solver_path,
        "version": version,
        "commit": commit,
    }


def _header_directive(path: Path, name: str) -> str:
    prefix = re.compile(rf"^//\s*{re.escape(name)}:\s*(.*)$")
    for line in path.read_text(encoding="utf-8").splitlines()[:20]:
        match = prefix.match(line)
        if match is not None:
            return match.group(1).strip()
    return ""


def _authoritative_file_flags(path: Path) -> list[str]:
    raw = _header_directive(path, "kani-flags")
    if not raw:
        return []
    try:
        parsed = shlex.split(raw)
    except ValueError as err:
        raise ReplacementRunError(f"{path}: invalid kani-flags: {err}") from err

    filtered: list[str] = []
    skip_harness_value = False
    for flag in parsed:
        if skip_harness_value:
            skip_harness_value = False
            continue
        if flag == "--harness":
            skip_harness_value = True
            continue
        if flag.startswith("--harness=") or flag == "--exact":
            continue
        filtered.append(flag)
    if skip_harness_value:
        raise ReplacementRunError(f"{path}: kani-flags has --harness without a value")
    return filtered


def build_invocation(
    row: dict[str, Any], config: RunnerConfig, *, ordinal: int
) -> Invocation:
    source = REPO_ROOT / row["file"]
    flags = [
        "-Z",
        "unstable-options",
        "--backend=ay",
        "--ay-solver=ay",
        "--ay-chc",
        "--ay-chc-track=mem",
        f"--harness-timeout={config.timeout_seconds}s",
        "--harness",
        row["driver_harness"],
        "--exact",
    ]
    # A source may forward a trailing --cbmc-args section. The compatibility
    # CLI intentionally consumes its whole tail, so put every driver operand
    # before source flags or the input/target path becomes a discarded CBMC arg.
    source_flags = _authoritative_file_flags(source)

    env = dict(os.environ)
    env["TRUST_MC_EMIT_EFFECTIVE_SUCCESS_MARKERS"] = "1"
    compile_flags = _header_directive(source, "compile-flags")
    if compile_flags:
        existing = env.get("RUSTFLAGS", "").strip()
        env["RUSTFLAGS"] = f"{existing} {compile_flags}".strip()

    if row["executor"] == "cargo":
        cwd = REPO_ROOT / row["cargo_dir"]
        target_key = hashlib.sha256(row["cargo_dir"].encode()).hexdigest()[:16]
        command = [
            str(config.driver),
            "trust-mc",
            "--locked",
            *flags,
            "--target-dir",
            str(config.target_dir / target_key),
            *source_flags,
        ]
    elif row["executor"] == "single-file":
        cwd = REPO_ROOT
        # Keep metadata and native witness outputs out of the source tree.
        # Different harnesses in one file must also have independent outputs.
        output_key = hashlib.sha256(
            f"{row['file']}\0{row['harness']}".encode()
        ).hexdigest()
        command = [
            str(config.driver), *flags,
            "--target-dir", str(config.target_dir / "single" / output_key),
            str(source),
            *source_flags,
        ]
    else:
        raise ReplacementRunError(
            f"{row['file']}::{row['harness']}: unsupported executor {row['executor']!r}"
        )

    log_key = hashlib.sha256(
        f"{row['file']}\0{row['harness']}".encode()
    ).hexdigest()[:16]
    log_path = config.report_dir / "replacement-public-logs" / (
        f"{ordinal:04d}-{log_key}.log"
    )
    return Invocation(command=command, cwd=cwd, env=env, log_path=log_path)


def run_invocation(
    row: dict[str, Any], invocation: Invocation, config: RunnerConfig
) -> ProcessResult:
    del row
    start = time.monotonic()
    timeout = max(config.timeout_seconds * 5 + 10, config.timeout_seconds)
    try:
        result = subprocess.run(
            invocation.command,
            cwd=invocation.cwd,
            env=invocation.env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
            check=False,
        )
        return ProcessResult(
            returncode=result.returncode,
            output=result.stdout,
            elapsed_seconds=time.monotonic() - start,
        )
    except subprocess.TimeoutExpired as err:
        output = err.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return ProcessResult(
            returncode=124,
            output=output,
            elapsed_seconds=time.monotonic() - start,
            timed_out=True,
        )
    except OSError as err:
        return ProcessResult(
            returncode=127,
            output=f"replacement runner failed to invoke driver: {err}\n",
            elapsed_seconds=time.monotonic() - start,
        )


def _translation_drop_reasons(output: str) -> dict[str, int]:
    reasons: Counter[str] = Counter()
    for marker in MARKER_RES["translation_drop"].findall(output):
        lhs, separator, raw_count = marker.rpartition("=")
        if not separator or not raw_count.isdigit():
            continue
        reason = lhs.rsplit(":", 1)[-1]
        if reason:
            reasons[reason] += int(raw_count)
    return dict(sorted(reasons.items()))


def _retry_fields(output: str) -> dict[str, Any]:
    attempts = _last(MARKER_RES["retry_attempts"], output)
    if not attempts:
        attempts = ",".join(MARKER_RES["retry_attempt"].findall(output))
    resolved_by = _last(MARKER_RES["retry_resolved_by"], output)
    final = _last(MARKER_RES["retry_final"], output)
    context = _last(MARKER_RES["retry_context"], output)
    retried = bool(
        attempts
        or resolved_by
        or final
        or context
        or "[AY:RETRY]" in output
    )
    if not retried:
        return {}
    fields: dict[str, Any] = {"retried": True}
    if attempts:
        fields["retry_attempts"] = attempts
    if resolved_by:
        fields["retry_resolved_by"] = resolved_by
    if final:
        fields["retry_final"] = final
    for item in context.split(",") if context else []:
        key, separator, value = item.partition("=")
        if not separator:
            continue
        if key == "recursive" and value in {"true", "false"}:
            fields["retry_recursive"] = value == "true"
        elif key == "relations" and value.isdigit():
            fields["retry_relation_count"] = int(value)
    return fields


def _is_cover_property(name: str) -> bool:
    return name == "cover" or name.startswith("cover.") or ".cover." in name


def _property_rows(output: str) -> tuple[list[dict[str, str]], str | None]:
    """Read real ordinary and cover checks through the same strict field parser."""
    properties = []
    blocks = list(re.finditer(
        r"^Check ([^:\n]+): ([^\n]+)\n(.*?)(?=^Check [^\n]*|^\s*SUMMARY:|^VERIFICATION:|\Z)",
        output, re.MULTILINE | re.DOTALL,
    ))
    if len(blocks) != len(re.findall(r"^Check [^\n]*", output, re.MULTILINE)):
        return properties, "malformed property header"
    seen_numbers = set()
    seen_names = set()
    for block in blocks:
        number, name, body = block.groups()
        if not re.fullmatch(r"[1-9][0-9]*", number) or number in seen_numbers or name in seen_names:
            return properties, "invalid or repeated property check identity"
        seen_numbers.add(number)
        seen_names.add(name)
        cover = _is_cover_property(name)
        if cover and not re.fullmatch(r"(?:[^\s]+\.)?cover\.[0-9]+", name):
            return properties, "invalid cover check identity"
        label = "cover check" if cover else "property check"
        # Count every field prefix, including malformed case/quoting, before
        # validating it. An ignored second field could hide a failed check.
        fields: dict[str, list[str]] = {"status": [], "description": []}
        for line in body.splitlines():
            field = re.match(r"^[ \t]*(?:-[ \t]*)?(status|description)\b", line, re.IGNORECASE)
            if field is not None:
                fields[field[1].lower()].append(line)
        if len(fields["status"]) != 1 or len(fields["description"]) != 1:
            return properties, f"malformed {label} {number}"
        status = re.fullmatch(r"[ \t]*- Status: ([A-Z]+)[ \t]*", fields["status"][0])
        description = re.fullmatch(r'[ \t]*- Description: "([^\r\n]*)"[ \t]*', fields["description"][0])
        if (status is None or description is None or not re.fullmatch(r"\S+", name)
                or (not cover and status[1] not in {"SUCCESS", "FAILURE", "UNDETERMINED", "UNREACHABLE"})):
            return properties, f"malformed {label} {number}"
        properties.append({"name": name, "description": description[1], "status": status[1]})
    return properties, None


def _cover_properties(output: str) -> tuple[list[dict[str, str]], str | None]:
    """Read named cover checks; preserve the existing cover-oracle interface."""
    properties, error = _property_rows(output)
    return [{"description": p["description"], "status": p["status"]}
            for p in properties if _is_cover_property(p["name"])], error


def _semantic_evidence_error(
    row: dict[str, Any], result: ProcessResult, checks: list[dict[str, str]],
    property_error: str | None, cover_mismatch: str | None,
) -> tuple[str | None, str | None]:
    finals = list(re.finditer(r"(?m)^VERIFICATION:- ([^\r\n]+)$", result.output))
    if len(finals) != 1:
        return None, "missing or repeated verification result"
    final = finals[0][1].strip()
    selected = list(CHECKING_HARNESS_RE.finditer(result.output))
    if len(selected) == 1 and any(
        not selected[0].end() < check.start() < finals[0].start()
        for check in re.finditer(r"(?m)^Check ", result.output)
    ):
        return final, "property check outside the selected harness result"
    if property_error:
        return final, property_error
    if "UNVALIDATED" in final:
        return final, "unvalidated verification result"
    if row["expected"] in {"PROOF", "BMC_SAFE"}:
        if final != "SUCCESSFUL":
            return final, "safety expectation lacks validated successful result"
        if any(check["status"] != "SUCCESS" for check in checks):
            return final, "safety expectation has an undecided or unsuccessful check"
        # A source-bound cover oracle can establish a cover-only outcome.
        # A no-check marker, including the compiler-certified qualifier, is
        # not a replacement proof without a matching artifact authority.
        if not checks and not (
            dispositions.cover_expectations(row) is not None and cover_mismatch is None
        ):
            return final, "safety expectation has no checked property evidence"
    elif row["expected"] == "CTREX":
        expected_panic = (
            final == "SUCCESSFUL (encountered one or more panics as expected)"
            and _last(MARKER_RES["effective_success"], result.output) == "should_panic_panics_only"
        )
        if final != "FAILED" and not expected_panic:
            return final, "bug expectation lacks a failed semantic result"
        if not any(check["status"] == "FAILURE" for check in checks):
            return final, "bug expectation has no failing checked property"
    return final, None


def parse_driver_result(
    row: dict[str, Any], result: ProcessResult
) -> tuple[dict[str, Any], dict[str, Any]]:
    output = result.output
    selected_harnesses = CHECKING_HARNESS_RE.findall(output)
    final_markers = FINAL_VERDICT_RE.findall(output)
    verdict = final_markers[-1] if final_markers else ""
    effective_success = _last(MARKER_RES["effective_success"], output)
    if not verdict and (
        MARKER_RES["unknown_quality"].search(output)
        or MARKER_RES["unknown_reason"].search(output)
        or "[AY:CTREX_CAT:Unknown" in output
    ):
        verdict = "UNKNOWN"

    if selected_harnesses != [row["driver_harness"]]:
        execution_state = "identity_mismatch"
        execution_details = (
            f"selected_harnesses={selected_harnesses!r}; "
            f"expected={row['driver_harness']!r}"
        )
        verdict = "ERROR"
    elif result.timed_out:
        execution_state = "watchdog_timeout"
        execution_details = "outer_timeout"
        verdict = "ERROR"
    elif final_markers:
        execution_state = "complete"
        execution_details = f"final_marker={final_markers[-1]}"
    elif "[trust-mc] Memory pressure cleanup:" in output:
        execution_state = "watchdog_cleanup"
        execution_details = "memory_pressure_cleanup"
        verdict = "ERROR"
    elif verdict == "UNKNOWN":
        execution_state = "complete"
        unknown_reason = _last(MARKER_RES["unknown_reason"], output)
        execution_details = (
            f"unknown_marker={unknown_reason}" if unknown_reason else "unknown_marker"
        )
    else:
        execution_state = "missing_verdict"
        if ARTIFACT_ERROR_RE.search(output):
            execution_details = "artifact_path_error"
        elif RUSTC_ERROR_RE.search(output):
            execution_details = "rustc_error"
        else:
            execution_details = "no_final_marker"
        verdict = "ERROR"

    # The corpus records semantic outcomes. A should_panic harness can succeed
    # as a test while its checked semantic result remains a counterexample.
    # Keep the driver's outcome independent of the expected label; converting
    # that counterexample to PROOF rejects the corpus's negative expectation
    # and can mistake an existential panic witness for a safety proof.
    expected = row["expected"]
    matched = execution_state == "complete" and verdict == expected
    if expected == "BMC_SAFE":
        matched = execution_state == "complete" and verdict in {"BMC", "PROOF"}
    # A bug oracle requires an actual validated refutation. A coarse CTREX
    # marker from unsupported/over-approximate execution is not that evidence.
    # Other negative expectations retain their own checked closure semantics.
    ctrex = _last(MARKER_RES["ctrex"], output)
    ctrex_category = _split_label_details(ctrex)[0] if ctrex else ""
    if expected == "CTREX" and ctrex_category != "Genuine":
        matched = False
    properties, property_error = _property_rows(output)
    covers = [{"description": p["description"], "status": p["status"]}
              for p in properties if _is_cover_property(p["name"])]
    cover_error = property_error
    cover_mismatch = dispositions.cover_mismatch(row, covers, cover_error)
    if cover_mismatch is not None:
        matched = False
    checks = [p for p in properties if not _is_cover_property(p["name"])]
    verification_result, semantic_error = _semantic_evidence_error(
        row, result, checks, property_error, cover_mismatch,
    )
    if semantic_error is not None:
        matched = False
    # A complete checked result can survive an abnormal process exit, but
    # that process did not complete the CLI control. Preserve its evidence
    # independently of the execution credit. UNKNOWN/ERROR keep their own
    # closure semantics; they have no universal normal-exit convention.
    checked_outcome = expected in {"PROOF", "BMC_SAFE", "CTREX"}
    validated_semantic_evidence = checked_outcome and matched
    expected_returncode = None
    if expected in {"PROOF", "BMC_SAFE"}:
        expected_returncode = 0
    elif expected == "CTREX":
        expected_panic = (
            verification_result == "SUCCESSFUL (encountered one or more panics as expected)"
            and effective_success == "should_panic_panics_only"
        )
        expected_returncode = 0 if expected_panic else 1
    completion_error = None
    if expected_returncode is not None and result.returncode != expected_returncode:
        completion_error = (
            f"expected normal exit {expected_returncode}, got returncode {result.returncode}"
        )
        matched = False
    status = "PASS" if matched else "FAIL"

    sound_fallback = _last(MARKER_RES["sound_fallback"], output)
    flat: dict[str, Any] = {
        "file": row["file"],
        "harness": row["harness"],
        "verdict": verdict,
        "status": status,
        "expected": expected,
        "sound_fallback_count": int(sound_fallback) if sound_fallback else 0,
        "translation_drop_reasons": _translation_drop_reasons(output),
        "execution_state": execution_state,
        "execution_details": execution_details,
        "time_sec": round(result.elapsed_seconds, 3),
        "checked_properties": checks,
        "returncode": result.returncode,
    }
    if checked_outcome:
        flat["validated_semantic_evidence"] = validated_semantic_evidence
        flat["expected_returncode"] = expected_returncode
    if completion_error is not None:
        flat["cli_completion_error"] = completion_error
    if verification_result is not None:
        flat["verification_result"] = verification_result
    if semantic_error is not None:
        flat["semantic_evidence_error"] = semantic_error
    if property_error is not None:
        flat["property_error"] = property_error
    if verdict == "PROOF" and status == "PASS":
        flat["trusted_proof"] = True
    if effective_success:
        flat["effective_success"] = effective_success
    if covers or dispositions.cover_expectations(row) is not None:
        flat["cover_properties"] = covers
    if cover_error:
        flat["cover_error"] = cover_error
    if cover_mismatch:
        flat["cover_mismatch"] = cover_mismatch

    ctrex = _last(MARKER_RES["ctrex"], output)
    if ctrex:
        category, details = _split_label_details(ctrex)
        flat["ctrex_category"] = category
        if details:
            flat["ctrex_details"] = details
    unknown_quality = _last(MARKER_RES["unknown_quality"], output)
    if unknown_quality:
        quality, details = _split_label_details(unknown_quality)
        flat["unknown_quality"] = quality
        if details:
            flat["unknown_details"] = details
    unknown_reason = _last(MARKER_RES["unknown_reason"], output)
    if unknown_reason:
        flat["unknown_reason"] = unknown_reason
    qualifiers = _last(MARKER_RES["proof_qualifiers"], output)
    if qualifiers:
        flat["proof_qualifiers"] = qualifiers
    demotion = _last(MARKER_RES["demotion"], output)
    if demotion:
        flat["demotion_reasons"] = [item for item in demotion.split(",") if item]
    flat.update(_retry_fields(output))

    runtime_record = {
        "schema_version": 2,
        "file": row["file"],
        "harness": row["harness"],
        "verdict": verdict,
        "status": status,
        "expected": expected,
        "metadata": {
            "execution": {
                "state": execution_state,
                "details": execution_details,
                "returncode": result.returncode,
            }
        },
    }
    for field in ("cover_properties", "cover_error", "cover_mismatch", "checked_properties",
                  "verification_result", "semantic_evidence_error", "property_error",
                  "returncode", "expected_returncode", "validated_semantic_evidence",
                  "cli_completion_error", "ctrex_category", "ctrex_details"):
        if field in flat:
            runtime_record[field] = flat[field]
    return flat, runtime_record


def inactive_rows(row: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    flat = {
        "file": row["file"],
        "harness": row["harness"],
        "verdict": "SKIP",
        "status": "SKIP",
        "expected": row["expected"],
        "sound_fallback_count": 0,
        "translation_drop_reasons": {},
        "execution_state": "inactive_accounted",
        "execution_details": row["reason"],
    }
    runtime_record = {
        "schema_version": 2,
        "file": row["file"],
        "harness": row["harness"],
        "verdict": "SKIP",
        "status": "SKIP",
        "expected": row["expected"],
        "metadata": {
            "execution": {
                "state": "inactive_accounted",
                "details": row["reason"],
            }
        },
    }
    return flat, runtime_record


def execute_plan(
    disposition_report: dict[str, Any],
    config: RunnerConfig,
    *,
    process_runner: ProcessRunner = run_invocation,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    flat_rows: list[dict[str, Any]] = []
    runtime_records: list[dict[str, Any]] = []
    runs: list[dict[str, Any]] = []
    config.report_dir.mkdir(parents=True, exist_ok=True)
    (config.report_dir / "replacement-public-logs").mkdir(parents=True, exist_ok=True)
    total = len(disposition_report["rows"])

    for ordinal, row in enumerate(disposition_report["rows"], 1):
        label = f"{row['file']}::{row['harness']}"
        if row["disposition"] == "inactive":
            flat, runtime = inactive_rows(row)
            print(
                f"[{ordinal:03d}/{total}] SKIP {label} "
                "(cfg-disabled, zero credit)"
            )
        else:
            invocation = build_invocation(row, config, ordinal=ordinal)
            result = process_runner(row, invocation, config)
            invocation.log_path.parent.mkdir(parents=True, exist_ok=True)
            invocation.log_path.write_text(result.output, encoding="utf-8")
            flat, runtime = parse_driver_result(row, result)
            outcome = flat["status"]
            print(
                f"[{ordinal:03d}/{total}] {outcome} {label} "
                f"(expected={row['expected']} actual={flat['verdict']})"
            )
            if config.verbose or outcome != "PASS":
                print(result.output[-4000:], file=sys.stderr)
            runs.append(
                {
                    "file": row["file"],
                    "harness": row["harness"],
                    "driver_harness": row["driver_harness"],
                    "executor": row["executor"],
                    "cwd": str(invocation.cwd),
                    "command": invocation.command,
                    "log": str(invocation.log_path),
                    "exit_code": result.returncode,
                    "time_sec": round(result.elapsed_seconds, 3),
                }
            )
        flat_rows.append(flat)
        runtime_records.append(runtime)
    return flat_rows, runtime_records, runs


def _summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    execution_counts = Counter(row["execution_state"] for row in rows)
    proof_qualifiers = [str(row.get("proof_qualifiers", "")) for row in rows]
    return {
        "total": len(rows),
        "pass": sum(row["status"] == "PASS" for row in rows),
        "proof": sum(row["verdict"] == "PROOF" for row in rows),
        "known_fp": sum(bool(row.get("known_fp")) for row in rows),
        "trusted_proof": sum(bool(row.get("trusted_proof")) for row in rows),
        "ctrex": sum(row["verdict"] == "CTREX" for row in rows),
        "fail": sum(row["status"] == "FAIL" for row in rows),
        "unknown": sum(row["verdict"] == "UNKNOWN" for row in rows),
        "error": sum(row["verdict"] == "ERROR" for row in rows),
        "bmc": sum(row["verdict"] == "BMC" for row in rows),
        "xfail": sum(row["status"] == "XFAIL" for row in rows),
        "skip": sum(row["status"] == "SKIP" for row in rows),
        "ctrex_breakdown": {
            "encoding_gap": sum(row.get("ctrex_category") == "EncodingGap" for row in rows),
            "over_approximation": sum(
                row.get("ctrex_category") == "OverApproximation" for row in rows
            ),
            "genuine": sum(row.get("ctrex_category") == "Genuine" for row in rows),
            "unknown": sum(row.get("ctrex_category") == "Unknown" for row in rows),
        },
        "proof_breakdown": {
            "clean": sum(value == "clean" for value in proof_qualifiers),
            "should_panic": sum(value == "should_panic" for value in proof_qualifiers),
            "crosschecked": sum("crosschecked=" in value for value in proof_qualifiers),
            "sound_qualified": sum("sound_fallback=" in value for value in proof_qualifiers),
            "mem_overapprox_qualified": sum(
                "kani_mem_overapprox=" in value for value in proof_qualifiers
            ),
        },
        "execution_complete": execution_counts.get("complete", 0),
        "execution_gated": sum(
            count for state, count in execution_counts.items() if state != "complete"
        ),
        "execution_breakdown": dict(sorted(execution_counts.items())),
    }


def build_report(
    rows: list[dict[str, Any]],
    runtime_accounting: dict[str, Any],
    *,
    ay_pin: str,
    solver_attestation: dict[str, str],
    driver_attestation: dict[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": 2,
        "report_status": "current",
        "commit": _current_head(REPO_ROOT),
        "tree_state": _current_tree_state(REPO_ROOT),
        "tree_fingerprint": _current_tree_fingerprint(REPO_ROOT),
        "date": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "ay_pin": ay_pin,
        "replacement_evidence": True,
        "solver": "ay",
        "solver_binary": solver_attestation,
        "driver_binary": driver_attestation,
        "source": "replacement-public",
        "summary": _summary(rows),
        "replacement_accounting": runtime_accounting,
        "harnesses": sorted(rows, key=lambda row: (row["file"], row["harness"])),
    }


def _write_json_atomic(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    rendered = json.dumps(value, indent=2, sort_keys=True) + "\n"
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=path.parent, delete=False
    ) as handle:
        handle.write(rendered)
        temporary = Path(handle.name)
    temporary.replace(path)


def _write_tsv(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "\t".join(
            (
                f"{row['file']}::{row['harness']}",
                str(row["verdict"]),
                str(row.get("time_sec", 0)),
                str(row["expected"]),
                str(row["status"]),
            )
        )
        for row in sorted(rows, key=lambda item: (item["file"], item["harness"]))
    ]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def checked_disposition_report() -> dict[str, Any]:
    generator = subprocess.run(
        [sys.executable, str(GENERATOR), "--check"],
        cwd=REPO_ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if generator.returncode != 0:
        raise ReplacementRunError(
            "canonical public inventories are stale:\n" + generator.stdout
        )
    report = dispositions.build_dispositions(
        dispositions.DEFAULT_INVENTORY,
        dispositions.DEFAULT_PROOF_INVENTORY,
        dispositions.DEFAULT_NON_PROOF,
    )
    expected = json.dumps(report, indent=2, sort_keys=True) + "\n"
    try:
        actual = dispositions.DEFAULT_OUTPUT.read_text(encoding="utf-8")
    except OSError as err:
        raise ReplacementRunError(
            f"unable to read disposition report: {err}"
        ) from err
    if actual != expected:
        raise ReplacementRunError(
            f"{dispositions.DEFAULT_OUTPUT}: source dispositions are stale"
        )
    expected_count = os.environ.get("AY_EXPECTED_HARNESSES")
    historical = report["summary"]["historical_total"]
    if expected_count is not None and expected_count != str(historical):
        raise ReplacementRunError(
            f"AY_EXPECTED_HARNESSES={expected_count} does not match {historical}"
        )
    return report


def locally_inactive_rows(disposition_report: dict[str, Any]) -> list[dict[str, Any]]:
    """Return the cfg-disabled rows that are still inside the replacement bar.

    The BAR is what the INCUMBENT DOES. A row upstream Kani itself disabled
    because CBMC could not run it is not something Kani does, so it cannot
    block a REPLACEMENT claim; it stays in the historical denominator with zero
    execution and zero proof credit. A row WE disabled stays inside the bar and
    blocks — that asymmetry is the anti-cheat.
    """

    return [
        row
        for row in disposition_report["rows"]
        if row["disposition"] == "inactive"
        and row.get("inactive_origin") != "upstream"
    ]


def clean_measurement_fingerprint(stage: str) -> str:
    """Require a clean evidence tree and return its tracked-input digest."""

    tree_state = _current_tree_state(REPO_ROOT)
    if tree_state != "clean":
        raise ReplacementRunError(
            f"replacement-public {stage} tree_state is {tree_state!r}, not 'clean'"
        )
    return _current_tree_fingerprint(REPO_ROOT)


def validate_runtime(
    disposition_report: dict[str, Any],
    records: list[dict[str, Any]],
) -> dict[str, Any]:
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", suffix=".jsonl", delete=False
    ) as handle:
        for record in records:
            handle.write(json.dumps(record, sort_keys=True) + "\n")
        path = Path(handle.name)
    try:
        return dispositions.validate_runtime_records(disposition_report, path)
    finally:
        path.unlink(missing_ok=True)


def run(args: argparse.Namespace) -> int:
    if os.environ.get("AY_REPORT_NON_REPLACEMENT", "").lower() in {
        "1",
        "true",
        "yes",
    }:
        raise ReplacementRunError(
            "AY_REPORT_NON_REPLACEMENT is incompatible with replacement-public"
        )
    disposition_report = checked_disposition_report()
    if args.plan_only:
        print(json.dumps(disposition_report["summary"], indent=2, sort_keys=True))
        return 1 if locally_inactive_rows(disposition_report) else 0

    initial_tree_fingerprint = clean_measurement_fingerprint("pre-run")
    driver = args.driver.resolve()
    if not driver.is_file() or not os.access(driver, os.X_OK):
        raise ReplacementRunError(f"driver is not executable: {driver}")
    ay_pin = expected_ay_pin_from_cargo_toml(REPO_ROOT).lower()
    head = _current_head(REPO_ROOT).lower()
    solver_binary = solver_attestation(args.solver, ay_pin)
    driver_binary = attest_driver_binary(
        driver,
        expected_trust_mc_sha=head,
        expected_ay_pin=ay_pin,
    )
    config = RunnerConfig(
        driver=driver,
        solver=args.solver,
        timeout_seconds=args.timeout,
        report_dir=args.report_dir.resolve(),
        target_dir=(REPO_ROOT / "target/replacement-public").resolve(),
        verbose=args.verbose,
    )
    rows, runtime_records, runs = execute_plan(disposition_report, config)
    report_path = config.report_dir / DEFAULT_REPORT.name
    tsv_path = config.report_dir / DEFAULT_TSV.name
    manifest_path = config.report_dir / DEFAULT_RUN_MANIFEST.name
    manifest = {
        "schema_version": 1,
        "artifact_kind": "trust-mc.replacement_public_run_manifest",
        "report": str(report_path),
        "source_commit": head,
        "ay_pin": ay_pin,
        "tree_fingerprint": initial_tree_fingerprint,
        "driver_binary": driver_binary,
        "finalized": False,
        "runs": runs,
    }
    # Retain actual commands, exits and log paths even if final validation
    # rejects a row or detects changed inputs. A failed run is still useful
    # evidence; finalized=False never supplies replacement authority.
    _write_json_atomic(manifest_path, manifest)
    runtime = validate_runtime(disposition_report, runtime_records)
    report = build_report(
        rows,
        runtime,
        ay_pin=ay_pin,
        solver_attestation=solver_binary,
        driver_attestation=driver_binary,
    )
    final_tree_fingerprint = clean_measurement_fingerprint("post-run")
    if final_tree_fingerprint != initial_tree_fingerprint:
        raise ReplacementRunError(
            "replacement-public measurement inputs changed during execution"
        )
    if report["tree_fingerprint"] != final_tree_fingerprint:
        raise ReplacementRunError(
            "replacement-public report tree fingerprint is not the post-run tree"
        )
    _write_json_atomic(report_path, report)
    _write_tsv(tsv_path, rows)
    manifest["finalized"] = True
    _write_json_atomic(manifest_path, manifest)
    print(f"replacement-public report: {report_path}")
    print(
        "replacement-public accounting: "
        f"historical={runtime['historical_total']} "
        f"active={runtime['active_executed']} "
        f"inactive={runtime['inactive_accounted']} "
        f"bar={runtime['proof']['bar'] + runtime['non_proof']['bar']} "
        f"proof_bar={runtime['proof']['bar']} "
        f"upstream_inactive={runtime['proof']['upstream_inactive']}"
    )
    failures = sum(row["status"] == "FAIL" for row in rows)
    local_inactive = locally_inactive_rows(disposition_report)
    counted = (
        runtime["proof"]["local_inactive"] + runtime["non_proof"]["local_inactive"]
    )
    if len(local_inactive) != counted:
        raise ReplacementRunError(
            "locally-inactive accounting disagrees with the checked source plan"
        )
    if failures:
        print(f"replacement-public: FAIL: {failures} active row(s) failed", file=sys.stderr)
    if local_inactive:
        for row in local_inactive:
            print(
                f"  locally disabled: {row['file']}::{row['harness']}",
                file=sys.stderr,
            )
        print(
            "replacement-public: FAIL: the replacement bar is blocked by "
            f"{len(local_inactive)} LOCALLY-disabled row(s) with zero credit; "
            "upstream-disabled rows are outside the bar, ours are not",
            file=sys.stderr,
        )
    return 1 if failures or local_inactive else 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--driver", type=Path, help="Executable trust-mc driver")
    parser.add_argument("--solver", default="ay")
    parser.add_argument("--timeout", type=int, default=60)
    parser.add_argument("--report-dir", type=Path, default=REPO_ROOT / "reports")
    parser.add_argument("--verbose", action="store_true")
    parser.add_argument(
        "--plan-only",
        action="store_true",
        help="Validate and print the source-bound plan without executing it",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    if args.timeout <= 0:
        parser.error("--timeout must be greater than zero")
    if not args.plan_only and args.driver is None:
        parser.error("--driver is required unless --plan-only is used")
    try:
        return run(args)
    except (ReplacementRunError, OSError, ValueError, json.JSONDecodeError) as err:
        print(f"replacement-public: ERROR: {err}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
