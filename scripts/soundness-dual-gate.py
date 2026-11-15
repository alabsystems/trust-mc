#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Manifest-driven soundness dual gate (plan gate G4 groundwork).

Runs every harness listed in ``tools/soundness-duals/manifest.toml`` through a
prebuilt trust-mc bundle, once per lane (``bmc`` = default lane, ``chc`` =
``--ay-chc``), and classifies each (harness, lane) row:

  match          the verdict agrees with the manifest expectation (for
                 CERTIFIED_OBLIGATION_FREE: SUCCESSFUL with zero checks AND the
                 compiler's certificate — the D16 verdict for a harness that
                 has nothing to prove)
  missed-bug     the program carries a bug and the engine reported SUCCESSFUL,
                 or a cover probe reported a decided status it never computed
                 (SOUNDNESS CLASS)
  false-certificate
                 the engine CERTIFIED a counterexample ([AY:CTREX_CAT:Genuine])
                 that the manifest says cannot exist: FAILED-Genuine on a safe
                 program (expected SUCCESSFUL or NOT_GENUINE), or Genuine where
                 forbid_genuine = true. A confident wrong bug report; gates.
  false-failure  the engine reported a demoted (not Genuine) FAILED on a safe
                 program, or refused to certify an obligation-free one
                 (INCONCLUSIVE on a CERTIFIED_OBLIGATION_FREE harness)
  unknown        INCONCLUSIVE, wall-clock timeout, or a vacuous SUCCESS
  error          no verdict: compile failure, crash, harness not run, drift
  unclassified   the manifest marks the harness needs_review (no expectation)

The gate refuses (exit 2) unless the ``ay`` binary it puts first on PATH names
the Cargo.toml AY pin in ``ay --version``. It exits 1 when any soundness-class,
false-certificate or error row is not known-red for that lane AND that class,
or when no row reached a decided verdict at all (a crashed or hung driver must never read as a pass);
``--strict`` also fails on every other non-match row. It exits 0 otherwise. A
JSON report with provenance is written to ``--report``.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as _dt
import hashlib
import json
import os
import platform
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any, Iterable

if sys.version_info < (3, 11):  # pragma: no cover - interpreter guard
    sys.exit("soundness-dual-gate.py needs python >= 3.11 (tomllib); see scripts/ay_python.sh")

import tomllib
from ay_cli_build_identity import PROTOCOL as AY_BUILD_PROTOCOL, SCHEMA as AY_BUILD_SCHEMA

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
DUALS_DIR = REPO_ROOT / "tools" / "soundness-duals"
DEFAULT_MANIFEST = DUALS_DIR / "manifest.toml"
DEFAULT_BUNDLE = Path.home() / "trust-mc" / "target" / "trust-mc"
# The default --ay-dir follows the Cargo.toml AY pin: the directory
# scripts/build-pinned-ay-cli.sh builds the CLI into, <cache root>/
# trust-mc-ay-cli-<first 9 of the pin>/compiler-<identity>/release. An unkeyed
# cache would silently go stale on the next pin bump.
AY_CLI_CACHE_ROOT_ENV = "TRUST_MC_AY_CLI_CACHE_ROOT"
DEFAULT_REPORT = REPO_ROOT / "target" / "soundness-dual-gate" / "report.json"

MANIFEST_SCHEMA = "trust-mc.soundness-dual-manifest/v1"
REPORT_SCHEMA = "trust-mc.soundness-dual-gate-report/v2"

LANES = ("bmc", "chc")
KINDS = ("dual", "negative", "ledger")
EXPECTED = (
    "FAILED",
    "SUCCESSFUL",
    "NOT_GENUINE",
    "NOT_SUCCESSFUL",
    "TOLERATED",
    "CERTIFIED_OBLIGATION_FREE",
)
# The proof qualifier a compiler-certified obligation-free harness carries
# (`trust-mc-driver/src/verification_result.rs`): the one signal that a
# zero-check SUCCESSFUL went THROUGH the no-checks gate on the certificate.
CERTIFIED_NO_CHECKS_QUALIFIER = "no_checks=compiler_certified_obligation_free"
CLASSES = (
    "match",
    "missed-bug",
    "false-certificate",
    "false-failure",
    "unknown",
    "error",
    "unclassified",
)
SOUNDNESS_CLASSES = frozenset({"missed-bug"})
# Rows that fail the gate without --strict. An error row has no verdict (compile
# failure, crash, harness not run): it cannot show that a bug was caught, so it
# must not let the gate pass. A false-certificate row is a Genuine counterexample
# the manifest says cannot exist: the engine vouched for a bug report with no
# encoding doubt and was wrong, so its certification channel is as broken as a
# missed bug's proof channel and it gates too. A demoted FAILED on a safe
# program (false-failure) makes no such claim and gates only under --strict.
GATING_CLASSES = SOUNDNESS_CLASSES | {"false-certificate", "error"}
# A known-red row names the ONE class it is red for; any other non-match class
# in that lane is scored as if the row were not known-red, so a row parked for a
# false certificate cannot mask a later missed bug.
KNOWN_RED_CLASSES = tuple(c for c in CLASSES if c not in ("match", "unclassified"))
DECIDED_VERDICTS = ("FAILED", "SUCCESSFUL")
# Inherited environment that can change a verdict (driver and compiler knobs,
# toolchain selection). Recorded in the report; the gate sets its own values
# for TRUST_MC_SYSROOT, RUSTFLAGS and PATH.
VERDICT_ENV_PREFIXES = ("TRUST_", "AY_", "KANI_", "CBMC_", "CHC_", "RUST")
GATE_SET_ENV = frozenset({"TRUST_MC_SYSROOT", "RUSTFLAGS"})
SECRET_ENV_RE = re.compile(r"TOKEN|SECRET|PASSWORD|CREDENTIAL|KEY", re.IGNORECASE)
# Most severe first; a harness row takes the most severe of its verdict and covers.
SEVERITY = ("missed-bug", "false-certificate", "false-failure", "error", "unknown", "unclassified", "match")
PROPERTIES = (
    "assertion",
    "overflow",
    "memory-safety",
    "valid-value",
    "uninit",
    "contract",
    "frame",
    "loop-contract",
    "nan",
    "panic",
    "unreachable",
    "unsupported",
)
COVER_TRUTHS = ("SATISFIED", "UNSATISFIABLE")
CHECK_TRUTHS = ("FAILURE", "SUCCESS")
FAIL_VERDICTS = ("FAILED", "NOT_SUCCESSFUL")

ENTRY_KEYS = frozenset({"path", "kind", "flags", "lanes", "oracle", "note", "harness"})
HARNESS_KEYS = frozenset(
    {
        "name",
        "expected",
        "property",
        "forbid_genuine",
        "known_red",
        "known_red_lanes",
        "known_red_class",
        "evidence",
        "needs_review",
        "covers",
        "checks",
        "note",
    }
)
COVER_KEYS = frozenset({"description", "truth"})
RESERVED_FLAGS = ("--ay-chc", "--harness", "--harness-timeout", "--exact")
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
PIN_RE = re.compile(r"^[0-9a-f]{40}$")


class ManifestError(ValueError):
    """The manifest is malformed or disagrees with the source tree."""

    def __init__(self, problems: Iterable[str]):
        self.problems = list(problems)
        super().__init__("\n".join(self.problems))


class GateRefusal(RuntimeError):
    """A precondition failed; the gate must not produce verdict rows."""


# --------------------------------------------------------------------------
# Manifest model
# --------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class CoverSpec:
    description: str
    truth: str


@dataclasses.dataclass(frozen=True)
class CheckSpec:
    description: str
    truth: str


@dataclasses.dataclass(frozen=True)
class HarnessSpec:
    name: str
    expected: str | None
    property: str | None = None
    forbid_genuine: bool = False
    known_red: bool = False
    known_red_lanes: tuple[str, ...] = ()
    known_red_class: str | None = None
    evidence: str | None = None
    needs_review: str | None = None
    covers: tuple[CoverSpec, ...] = ()
    checks: tuple[CheckSpec, ...] = ()
    note: str | None = None


@dataclasses.dataclass(frozen=True)
class EntrySpec:
    path: str
    kind: str
    flags: tuple[str, ...]
    lanes: tuple[str, ...]
    oracle: str
    harnesses: tuple[HarnessSpec, ...]
    note: str | None = None


@dataclasses.dataclass(frozen=True)
class Manifest:
    path: Path
    entries: tuple[EntrySpec, ...]

    @property
    def base_dir(self) -> Path:
        return self.path.parent

    def source(self, entry: EntrySpec) -> Path:
        return (self.base_dir / entry.path).resolve()


def _str_list(value: Any, where: str, problems: list[str]) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(v, str) for v in value):
        problems.append(f"{where}: expected a list of strings")
        return ()
    return tuple(value)


def parse_manifest_data(data: dict[str, Any], path: Path) -> Manifest:
    """Validate the parsed TOML document and build the manifest model."""
    problems: list[str] = []
    if data.get("schema") != MANIFEST_SCHEMA:
        problems.append(f"schema must be {MANIFEST_SCHEMA!r}, got {data.get('schema')!r}")
    unknown_top = set(data) - {"schema", "entry"}
    if unknown_top:
        problems.append(f"unknown top-level keys: {sorted(unknown_top)}")
    raw_entries = data.get("entry")
    if not isinstance(raw_entries, list) or not raw_entries:
        problems.append("manifest needs at least one [[entry]]")
        raise ManifestError(problems)

    entries: list[EntrySpec] = []
    seen_paths: set[str] = set()
    for index, raw in enumerate(raw_entries):
        where = f"entry[{index}]"
        if not isinstance(raw, dict):
            problems.append(f"{where}: not a table")
            continue
        unknown = set(raw) - ENTRY_KEYS
        if unknown:
            problems.append(f"{where}: unknown keys {sorted(unknown)}")
        rel = raw.get("path")
        if not isinstance(rel, str) or not rel.endswith(".rs"):
            problems.append(f"{where}: path must be a .rs path relative to the manifest")
            continue
        where = f"entry {rel}"
        if rel in seen_paths:
            problems.append(f"{where}: duplicate entry")
        seen_paths.add(rel)
        kind = raw.get("kind")
        if kind not in KINDS:
            problems.append(f"{where}: kind must be one of {KINDS}, got {kind!r}")
        flags = _str_list(raw.get("flags", []), f"{where}: flags", problems)
        for flag in flags:
            if flag.split("=", 1)[0] in RESERVED_FLAGS:
                problems.append(f"{where}: flag {flag!r} is set by the gate, not the manifest")
        lanes = _str_list(raw.get("lanes", list(LANES)), f"{where}: lanes", problems)
        if not lanes or any(lane not in LANES for lane in lanes) or len(set(lanes)) != len(lanes):
            problems.append(f"{where}: lanes must be a non-empty subset of {LANES} without repeats")
        if any(flag.startswith("--ay-chc-track") for flag in flags) and tuple(lanes) != ("chc",):
            problems.append(f"{where}: --ay-chc-track flags are CHC-only; lanes must be [\"chc\"]")
        oracle = raw.get("oracle")
        if not isinstance(oracle, str) or not oracle.strip():
            problems.append(f"{where}: oracle (where the expectation comes from) is required")
            oracle = ""
        note = raw.get("note")
        if note is not None and not isinstance(note, str):
            problems.append(f"{where}: note must be a string")
        raw_harnesses = raw.get("harness")
        if not isinstance(raw_harnesses, list) or not raw_harnesses:
            problems.append(f"{where}: at least one [[entry.harness]] is required")
            raw_harnesses = []
        harnesses: list[HarnessSpec] = []
        seen_names: set[str] = set()
        for raw_h in raw_harnesses:
            spec = _parse_harness(raw_h, where, tuple(lanes), problems)
            if spec is None:
                continue
            if spec.name in seen_names:
                problems.append(f"{where}: duplicate harness {spec.name}")
            seen_names.add(spec.name)
            harnesses.append(spec)
        entries.append(
            EntrySpec(
                path=rel,
                kind=str(kind),
                flags=flags,
                lanes=tuple(lanes),
                oracle=oracle,
                harnesses=tuple(harnesses),
                note=note if isinstance(note, str) else None,
            )
        )
    if problems:
        raise ManifestError(problems)
    return Manifest(path=path, entries=tuple(entries))


def _parse_harness(
    raw: Any, where: str, lanes: tuple[str, ...], problems: list[str]
) -> HarnessSpec | None:
    if not isinstance(raw, dict):
        problems.append(f"{where}: harness is not a table")
        return None
    name = raw.get("name")
    if not isinstance(name, str) or not IDENT_RE.match(name):
        problems.append(f"{where}: harness name {name!r} is not an identifier")
        return None
    hwhere = f"{where}::{name}"
    unknown = set(raw) - HARNESS_KEYS
    if unknown:
        problems.append(f"{hwhere}: unknown keys {sorted(unknown)}")
    expected = raw.get("expected")
    needs_review = raw.get("needs_review")
    if expected is None and needs_review is None:
        problems.append(f"{hwhere}: needs an expected verdict or a needs_review reason")
    if expected is not None and needs_review is not None:
        problems.append(f"{hwhere}: expected and needs_review are exclusive (do not guess)")
    if expected is not None and expected not in EXPECTED:
        problems.append(f"{hwhere}: expected must be one of {EXPECTED}, got {expected!r}")
    if needs_review is not None and (not isinstance(needs_review, str) or not needs_review.strip()):
        problems.append(f"{hwhere}: needs_review must be a non-empty reason")
    prop = raw.get("property")
    if prop is not None:
        if expected not in FAIL_VERDICTS:
            problems.append(f"{hwhere}: property only applies to FAILED / NOT_SUCCESSFUL")
        if prop not in PROPERTIES:
            problems.append(f"{hwhere}: property must be one of {PROPERTIES}, got {prop!r}")
    forbid_genuine = raw.get("forbid_genuine", False)
    if not isinstance(forbid_genuine, bool):
        problems.append(f"{hwhere}: forbid_genuine must be a boolean")
        forbid_genuine = False
    if forbid_genuine and expected != "FAILED":
        problems.append(f"{hwhere}: forbid_genuine only applies to expected = \"FAILED\"")
    known_red = raw.get("known_red", False)
    if not isinstance(known_red, bool):
        problems.append(f"{hwhere}: known_red must be a boolean")
        known_red = False
    evidence = raw.get("evidence")
    if evidence is not None and (not isinstance(evidence, str) or not evidence.strip()):
        problems.append(f"{hwhere}: evidence must be a non-empty string")
    known_red_class = raw.get("known_red_class")
    if known_red_class is not None:
        if known_red_class not in KNOWN_RED_CLASSES:
            problems.append(
                f"{hwhere}: known_red_class must be one of {KNOWN_RED_CLASSES}, got {known_red_class!r}"
            )
            known_red_class = None
        elif not known_red:
            problems.append(f"{hwhere}: known_red_class without known_red = true")
    red_lanes: tuple[str, ...] = ()
    if "known_red_lanes" in raw:
        red_lanes = _str_list(raw["known_red_lanes"], f"{hwhere}: known_red_lanes", problems)
        if not known_red:
            problems.append(f"{hwhere}: known_red_lanes without known_red = true")
        if not red_lanes or any(lane not in lanes for lane in red_lanes):
            problems.append(f"{hwhere}: known_red_lanes must be a non-empty subset of {lanes}")
    if known_red:
        if not evidence:
            problems.append(f"{hwhere}: known_red = true needs the audit evidence id")
        if known_red_class is None and "known_red_class" not in raw:
            problems.append(
                f"{hwhere}: known_red = true needs known_red_class (the one class it is red "
                "for, so it cannot mask a different regression)"
            )
        if expected is None or expected == "TOLERATED":
            problems.append(f"{hwhere}: known_red needs a scored expectation")
        if not red_lanes:
            red_lanes = lanes
    covers: list[CoverSpec] = []
    raw_covers = raw.get("covers", [])
    if not isinstance(raw_covers, list):
        problems.append(f"{hwhere}: covers must be a list of tables")
        raw_covers = []
    for raw_cover in raw_covers:
        if not isinstance(raw_cover, dict) or set(raw_cover) - COVER_KEYS:
            problems.append(f"{hwhere}: cover must be a table with keys {sorted(COVER_KEYS)}")
            continue
        desc = raw_cover.get("description")
        truth = raw_cover.get("truth")
        if not isinstance(desc, str) or not desc:
            problems.append(f"{hwhere}: cover description is required")
            continue
        if truth not in COVER_TRUTHS:
            problems.append(f"{hwhere}: cover truth must be one of {COVER_TRUTHS}")
            continue
        covers.append(CoverSpec(description=desc, truth=truth))
    checks: list[CheckSpec] = []
    raw_checks = raw.get("checks", [])
    if not isinstance(raw_checks, list):
        problems.append(f"{hwhere}: checks must be a list of tables")
        raw_checks = []
    for raw_check in raw_checks:
        if not isinstance(raw_check, dict) or set(raw_check) - COVER_KEYS:
            problems.append(f"{hwhere}: check must be a table with keys {sorted(COVER_KEYS)}")
            continue
        desc = raw_check.get("description")
        truth = raw_check.get("truth")
        if not isinstance(desc, str) or not desc:
            problems.append(f"{hwhere}: check description is required")
            continue
        if truth not in CHECK_TRUTHS:
            problems.append(f"{hwhere}: check truth must be one of {CHECK_TRUTHS}")
            continue
        checks.append(CheckSpec(description=desc, truth=truth))
    note = raw.get("note")
    if note is not None and not isinstance(note, str):
        problems.append(f"{hwhere}: note must be a string")
        note = None
    return HarnessSpec(
        name=name,
        expected=expected if expected in EXPECTED else None,
        property=prop if prop in PROPERTIES else None,
        forbid_genuine=forbid_genuine,
        known_red=known_red,
        known_red_lanes=red_lanes,
        known_red_class=known_red_class if known_red else None,
        evidence=evidence if isinstance(evidence, str) else None,
        needs_review=needs_review if isinstance(needs_review, str) else None,
        covers=tuple(covers),
        checks=tuple(checks),
        note=note,
    )


def load_manifest(path: Path) -> Manifest:
    try:
        data = tomllib.loads(path.read_text(encoding="utf-8"))
    except OSError as err:
        raise ManifestError([f"{path}: cannot read manifest: {err}"]) from err
    except tomllib.TOMLDecodeError as err:
        raise ManifestError([f"{path}: invalid TOML: {err}"]) from err
    return parse_manifest_data(data, path)


# --------------------------------------------------------------------------
# Harness discovery (manifest drift check)
# --------------------------------------------------------------------------

_PROOF_ATTR_RE = re.compile(
    r"#\[\s*(?:kani::proof(?:_for_contract\s*\([^)]*\))?|cfg_attr\s*\(\s*kani\s*,[^\]]*kani::proof[^\]]*)\s*\]"
)
_FN_RE = re.compile(
    r"^(?:pub(?:\([^)]*\))?\s+)?(?:const\s+)?(?:async\s+)?(?:unsafe\s+)?"
    r"(?:extern\s+\"[^\"]*\"\s+)?fn\s+([A-Za-z_][A-Za-z0-9_]*)"
)


def discover_harnesses(source: str) -> list[str]:
    """Return proof harness names in source order.

    Recognises ``#[kani::proof]``, ``#[kani::proof_for_contract(..)]`` and the
    ``#[cfg_attr(kani, kani::proof..)]`` spelling. Line comments are skipped, so a
    commented-out attribute never counts.
    """
    names: list[str] = []
    pending = False
    for raw_line in source.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("//"):
            continue
        attr = _PROOF_ATTR_RE.search(line)
        if attr and line.startswith("#"):
            pending = True
            line = line[attr.end():].strip()
            while line.startswith("#["):
                close = line.find("]")
                if close < 0:
                    break
                line = line[close + 1:].strip()
            if not line:
                continue
        if pending:
            match = _FN_RE.match(line)
            if match:
                names.append(match.group(1))
                pending = False
    return names


def validate_against_tree(manifest: Manifest) -> list[str]:
    """Check every entry against its source file and the duals directory."""
    problems: list[str] = []
    listed: set[Path] = set()
    for entry in manifest.entries:
        source = manifest.source(entry)
        listed.add(source)
        if not source.is_file():
            problems.append(f"{entry.path}: file does not exist")
            continue
        discovered = discover_harnesses(source.read_text(encoding="utf-8", errors="replace"))
        declared = [h.name for h in entry.harnesses]
        missing = sorted(set(discovered) - set(declared))
        extra = sorted(set(declared) - set(discovered))
        if missing:
            problems.append(f"{entry.path}: harnesses in source but not in manifest: {missing}")
        if extra:
            problems.append(f"{entry.path}: harnesses in manifest but not in source: {extra}")
    base = manifest.base_dir
    for pattern in ("*.rs", "negative/*.rs"):
        for candidate in sorted(base.glob(pattern)):
            if candidate.resolve() not in listed:
                problems.append(f"{candidate.relative_to(base)}: dual file has no manifest entry")
    return problems


# --------------------------------------------------------------------------
# Driver output parsing
# --------------------------------------------------------------------------


@dataclasses.dataclass
class CheckRow:
    name: str
    property_class: str
    status: str
    description: str


@dataclasses.dataclass
class HarnessRun:
    name: str
    verdict: str | None = None
    verdict_line: str | None = None
    checks: list[CheckRow] = dataclasses.field(default_factory=list)
    markers: list[str] = dataclasses.field(default_factory=list)
    ctrex_category: str | None = None
    # True when ANY counterexample-category marker for this harness says
    # Genuine, not only the first one (fail-closed for NOT_GENUINE twins).
    genuine: bool = False


_CHECKING_RE = re.compile(r"^Checking harness (\S+?)\.\.\.\s*$")
_CHECK_RE = re.compile(r"^Check \d+: (\S+)\s*$")
_STATUS_RE = re.compile(r"^\s*- Status: (\S+)")
_DESC_RE = re.compile(r'^\s*- Description: "(.*)"\s*$')
_VERDICT_RE = re.compile(r"^VERIFICATION:- (\S+)")
_MARKER_RE = re.compile(r"^\[AY:([^\]]*)\]")
MARKER_LIMIT = 12
MARKER_WIDTH = 120


def _short_marker(body: str) -> str:
    if body.startswith("PROOF_TRANSCRIPT_METADATA"):
        return body.split(":json_hex=", 1)[0]
    return body if len(body) <= MARKER_WIDTH else body[: MARKER_WIDTH - 3] + "..."


def parse_driver_output(text: str) -> dict[str, HarnessRun]:
    runs: dict[str, HarnessRun] = {}
    current: HarnessRun | None = None
    check: CheckRow | None = None
    for line in text.splitlines():
        started = _CHECKING_RE.match(line)
        if started:
            current = HarnessRun(name=started.group(1))
            runs[current.name] = current
            check = None
            continue
        if current is None:
            continue
        marker = _MARKER_RE.match(line)
        if marker:
            body = marker.group(1)
            if body.startswith("CTREX_CAT:"):
                category = body.split(":")[1]
                if current.ctrex_category is None:
                    current.ctrex_category = category
                if category == "Genuine":
                    current.genuine = True
            if len(current.markers) < MARKER_LIMIT:
                current.markers.append(_short_marker(body))
            continue
        head = _CHECK_RE.match(line)
        if head:
            parts = head.group(1).rsplit(".", 2)
            prop = parts[1] if len(parts) == 3 else head.group(1)
            check = CheckRow(name=head.group(1), property_class=prop, status="", description="")
            current.checks.append(check)
            continue
        status = _STATUS_RE.match(line)
        if status and check is not None:
            check.status = status.group(1)
            continue
        desc = _DESC_RE.match(line)
        if desc and check is not None:
            check.description = desc.group(1)
            continue
        verdict = _VERDICT_RE.match(line)
        if verdict and current.verdict is None:
            current.verdict = verdict.group(1)
            current.verdict_line = line.strip()
            check = None
    return runs


def run_is_certified_no_checks(run: HarnessRun) -> bool:
    """Did the driver settle this harness as compiler-certified obligation-free?

    Keys on the `[AY:PROOF_QUALIFIERS:...]` line, which the driver prints only
    for a success and only with this qualifier when the empty obligation set
    went through the no-checks gate on the compiler's certificate.
    """
    return any(
        m.startswith("PROOF_QUALIFIERS:") and CERTIFIED_NO_CHECKS_QUALIFIER in m
        for m in run.markers
    )


def find_run(runs: dict[str, HarnessRun], name: str) -> HarnessRun | None:
    if name in runs:
        return runs[name]
    for key, run in runs.items():
        if key.endswith("::" + name):
            return run
    return None


def normalize_verdict(token: str | None) -> str | None:
    if token is None:
        return None
    if token.startswith("SUCCESSFUL"):
        return "SUCCESSFUL"
    if token.startswith("FAILED"):
        return "FAILED"
    return "INCONCLUSIVE"


_CATEGORY_RULES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("nan", ("nan",)),
    ("valid-value", ("invalid value", "valid value", "validity", "invalid enum", "valid discriminant")),
    ("uninit", ("uninit", "initialized")),
    ("frame", ("modifies", "frame", "assigns", "havoc")),
    ("contract", ("postcondition", "precondition", "ensures", "requires", "contract")),
    ("loop-contract", ("loop invariant", "loop_invariant", "decreases", "loop contract", "unwinding")),
    ("unreachable", ("unreachable",)),
    ("unsupported", ("unsupported", "not currently supported", "unimplemented")),
    (
        "memory-safety",
        (
            "dereference",
            "memory safety",
            "pointer",
            "memcpy",
            "overlap",
            "region",
            "aligned",
            "alignment",
            "dealloc",
            "free",
            "out of bounds",
            "dangling",
            "offset",
            "can_dereference",
        ),
    ),
    ("overflow", ("overflow", "underflow")),
    ("panic", ("panic", "unwrap", "expect")),
)


def property_categories(property_class: str, description: str) -> set[str]:
    """Coarse property categories for one failed check (informational only)."""
    text = f"{property_class} {description}".lower()
    found = {category for category, words in _CATEGORY_RULES if any(w in text for w in words)}
    if description.lstrip().startswith("|"):
        # Contract checks print the ensures/requires closure as the description.
        found.add("contract")
    if "assertion failed" in text or property_class in ("assertion", "user_assertion"):
        found.add("assertion")
    if not found:
        found.add("assertion")
    return found


# --------------------------------------------------------------------------
# Classification
# --------------------------------------------------------------------------


def classify_verdict(
    expected: str | None,
    verdict: str | None,
    *,
    genuine: bool = False,
    zero_checks: bool = False,
    forbid_genuine: bool = False,
    timed_out: bool = False,
    certified_no_checks: bool = False,
) -> tuple[str, str]:
    """Map (expectation, observed verdict) to (class, detail)."""
    if expected is None:
        return "unclassified", "needs-review"
    if verdict is None:
        return ("unknown", "wall-timeout") if timed_out else ("error", "no-verdict")
    if expected == "TOLERATED":
        return "match", f"tolerated-{verdict.lower()}"
    if expected == "CERTIFIED_OBLIGATION_FREE":
        # D16: the program has nothing to prove, and the run must SAY so — a
        # zero-check SUCCESSFUL carrying the compiler's certificate. A FAILED is
        # a false failure (a false certificate when Genuine); an INCONCLUSIVE is
        # the walk refusing a body it should have certified, which is exit 1 on
        # a correct program; a SUCCESSFUL with checks is not the twin it claims
        # to be; a zero-check SUCCESSFUL without the qualifier is the clean
        # proof of nothing this expectation exists to refuse.
        if verdict == "FAILED":
            if genuine:
                return "false-certificate", "failed-on-obligation-free-genuine"
            return "false-failure", "failed-on-obligation-free"
        if verdict == "INCONCLUSIVE":
            return "false-failure", "obligation-free-not-certified"
        if not zero_checks:
            return "unknown", "obligation-free-twin-has-checks"
        if not certified_no_checks:
            return "missed-bug", "zero-checks-clean-successful"
        return "match", "certified-obligation-free"
    if verdict == "INCONCLUSIVE":
        if expected == "NOT_SUCCESSFUL":
            return "match", "inconclusive-accepted"
        return "unknown", "inconclusive"
    if expected in FAIL_VERDICTS:
        if verdict == "SUCCESSFUL":
            return "missed-bug", "successful-on-bug" + ("-vacuous" if zero_checks else "")
        if forbid_genuine and genuine:
            return "false-certificate", "genuine-certified-where-forbidden"
        return "match", "failed"
    if expected == "SUCCESSFUL":
        if verdict == "FAILED":
            if genuine:
                return "false-certificate", "failed-on-safe-genuine"
            return "false-failure", "failed-on-safe"
        if zero_checks:
            return "unknown", "vacuous-success"
        return "match", "successful"
    if expected == "NOT_GENUINE":
        if verdict == "FAILED":
            if genuine:
                return "false-certificate", "genuine-on-safe"
            return "match", "tolerated-demotion"
        if zero_checks:
            return "unknown", "vacuous-success"
        return "match", "successful"
    raise ValueError(f"unhandled expectation {expected!r}")


def classify_cover(truth: str, status: str | None) -> tuple[str, str]:
    if status is None:
        return "error", "cover-not-reported"
    if status == "UNDETERMINED":
        return "match", "cover-undetermined"
    if status == truth:
        return "match", f"cover-{status.lower()}"
    if truth == "UNSATISFIABLE" and status == "UNREACHABLE":
        return "match", "cover-unreachable"
    if status == "SATISFIED":
        return "false-failure", "cover-satisfied-but-unsatisfiable"
    if status in ("UNSATISFIABLE", "UNREACHABLE"):
        return "missed-bug", f"cover-{status.lower()}-but-satisfiable"
    # SUCCESS (or any non-cover status) is a decided-looking answer for a probe
    # that reports no reachability result at all.
    return "missed-bug", f"cover-status-{status.lower()}"


def classify_check(truth: str, status: str | None, genuine: bool = False) -> tuple[str, str]:
    """Per-check expectation (R3): a violable check must never read SUCCESS.

    A safe check that reads FAILURE in a run certified Genuine is a false
    certificate, not a false failure: the certificate vouches for every failed
    check of the run (`bug_replace_fnptr`: `old == 7` read FAILURE under
    `[AY:CTREX_CAT:Genuine]` while Kani verifies it).
    """
    if status is None:
        return "error", "check-not-reported"
    if status == "UNDETERMINED":
        return "match", "check-undetermined"
    if status == truth:
        return "match", f"check-{status.lower()}"
    if truth == "FAILURE" and status in ("SUCCESS", "UNREACHABLE"):
        return "missed-bug", f"check-{status.lower()}-but-violable"
    if truth == "SUCCESS" and status == "FAILURE":
        if genuine:
            return "false-certificate", "check-failure-genuine-but-safe"
        return "false-failure", "check-failure-but-safe"
    return "unknown", f"check-status-{status.lower()}"


def is_cover_check(check: CheckRow) -> bool:
    return check.property_class == "cover" or check.description.startswith("cover ")


def match_cover_status(cover: CoverSpec, ordinal: int, cover_checks: list[CheckRow]) -> str | None:
    """Status of the manifest cover: by message when printed, else by source order.

    The driver prints the ``kani::cover!`` message in some lanes and a generic
    ``cover property N`` in others, so the ordinal among cover checks is the
    fallback identity.
    """
    for check in cover_checks:
        if cover.description in check.description:
            return check.status
    if ordinal < len(cover_checks):
        return cover_checks[ordinal].status
    return None


def most_severe(classes: Iterable[str]) -> str:
    ranked = sorted(classes, key=SEVERITY.index)
    return ranked[0] if ranked else "match"


def known_red_applies(row: dict[str, Any]) -> bool:
    """A known-red flag excuses only the class it names, in its lanes."""
    return bool(row["known_red"]) and row.get("known_red_class") == row["class"]


def is_gating(row: dict[str, Any], strict: bool = False) -> bool:
    if row["class"] in ("match", "unclassified"):
        return False
    if known_red_applies(row):
        return False
    if row["class"] in GATING_CLASSES:
        return True
    return strict


def classify_harness(
    spec: HarnessSpec, lane: str, run: HarnessRun | None, *, timed_out: bool
) -> dict[str, Any]:
    verdict = normalize_verdict(run.verdict if run else None)
    checks = run.checks if run else []
    genuine = bool(run and run.genuine)
    cls, detail = classify_verdict(
        spec.expected,
        verdict,
        genuine=genuine,
        zero_checks=bool(run) and not checks,
        forbid_genuine=spec.forbid_genuine,
        timed_out=timed_out,
        certified_no_checks=bool(run) and run_is_certified_no_checks(run),
    )
    if run is None and not timed_out and spec.expected is not None:
        cls, detail = "error", "harness-not-run"
    failed = [c for c in checks if c.status == "FAILURE"]
    seen: set[str] = set()
    for c in failed:
        seen |= property_categories(c.property_class, c.description)
    property_ok: bool | None = None
    if spec.property and verdict == "FAILED":
        property_ok = spec.property in seen
    cover_rows = []
    classes = [cls]
    cover_checks = [c for c in checks if is_cover_check(c)]
    for ordinal, cover in enumerate(spec.covers):
        status = match_cover_status(cover, ordinal, cover_checks)
        c_cls, c_detail = classify_cover(cover.truth, status)
        if status is None and (verdict in (None, "INCONCLUSIVE") or timed_out):
            c_cls, c_detail = "unknown", "cover-not-reported-inconclusive"
        cover_rows.append(
            {"description": cover.description, "truth": cover.truth, "status": status,
             "class": c_cls, "detail": c_detail}
        )
        classes.append(c_cls)
    check_rows = []
    plain_checks = [c for c in checks if not is_cover_check(c)]
    for expectation in spec.checks:
        # Every check whose description matches is scored; the most severe wins,
        # so a second matching check that reads SUCCESS cannot hide behind a
        # first one that reads FAILURE.
        statuses = [c.status for c in plain_checks if expectation.description in c.description]
        scored = [(classify_check(expectation.truth, st, genuine), st) for st in statuses]
        if scored:
            (k_cls, k_detail), status = min(scored, key=lambda item: SEVERITY.index(item[0][0]))
        else:
            status = None
            k_cls, k_detail = classify_check(expectation.truth, None)
        if status is None and (verdict in (None, "INCONCLUSIVE") or timed_out):
            k_cls, k_detail = "unknown", "check-not-reported-inconclusive"
        check_rows.append(
            {"description": expectation.description, "truth": expectation.truth, "status": status,
             "class": k_cls, "detail": k_detail}
        )
        classes.append(k_cls)
    final = most_severe(classes)
    if final != cls:
        detail = next(r["detail"] for r in cover_rows + check_rows if r["class"] == final)
    known_red = spec.known_red and lane in spec.known_red_lanes
    return {
        "harness": spec.name,
        "lane": lane,
        "expected": spec.expected,
        "property": spec.property,
        "verdict": verdict,
        "verdict_line": run.verdict_line if run else None,
        "class": final,
        "detail": detail,
        "soundness": final in SOUNDNESS_CLASSES,
        "known_red": known_red,
        "known_red_class": spec.known_red_class if known_red else None,
        "evidence": spec.evidence,
        "needs_review": spec.needs_review,
        "ctrex_category": run.ctrex_category if run else None,
        "checks": len(checks),
        "failed_checks": [[c.property_class, c.description] for c in failed][:8],
        "property_seen": sorted(seen),
        "property_ok": property_ok,
        "covers": cover_rows,
        "check_expectations": check_rows,
        "markers": list(run.markers) if run else [],
    }


# --------------------------------------------------------------------------
# Preflight and provenance
# --------------------------------------------------------------------------


def portable(value: str | Path) -> str:
    """Render a path without the machine's home prefix (reports are committed)."""
    text = str(value)
    home = str(Path.home())
    if text == home:
        return "~"
    if text.startswith(home + os.sep):
        return "~" + text[len(home):]
    return text


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def check_ay_version(version_text: str, pin: str) -> str:
    """Return the matched build commit, or raise GateRefusal."""
    if not PIN_RE.match(pin):
        raise GateRefusal(f"Cargo.toml AY pin {pin!r} is not a 40-character lowercase sha")
    commits = set(re.findall(r"(?<![0-9a-f])([0-9a-f]{40})(?![0-9a-f])", version_text.lower()))
    if pin not in commits:
        first = version_text.strip().splitlines()[0] if version_text.strip() else "<empty>"
        raise GateRefusal(
            f"ay --version does not name the Cargo.toml AY pin {pin}: {first!r}"
        )
    return pin


def _git(repo: Path, *args: str) -> str | None:
    try:
        return subprocess.run(
            ["git", "-C", str(repo), *args], capture_output=True, text=True, check=True
        ).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def repo_state(repo: Path) -> dict[str, Any] | None:
    top = _git(repo, "rev-parse", "--show-toplevel")
    if top is None:
        return None
    head = _git(repo, "rev-parse", "HEAD")
    tracked = _git(repo, "status", "--porcelain", "--untracked-files=no") or ""
    untracked = _git(repo, "ls-files", "--others", "--exclude-standard") or ""
    return {
        "path": portable(top),
        "head": head,
        "dirty": bool(tracked),
        "dirty_tracked_paths": len(tracked.splitlines()),
        "untracked_paths": len(untracked.splitlines()),
    }


def bundle_source_candidate(bundle: Path) -> Path | None:
    """The checkout a `<repo>/target*/trust-mc` bundle was built in.

    Uses the path as given, not its resolution: `target` is often a symlink
    (on this host `target -> target.noindex`), and the resolved parent name
    would hide the repository.
    """
    parent = bundle.absolute().parent
    if parent.name.startswith("target"):
        return parent.parent
    return None


def bundle_checkout_at_run(bundle: Path) -> dict[str, Any] | None:
    """State of the checkout holding the bundle, read at gate time.

    This is NOT the commit the bundle was built from: the checkout may have
    moved since the build. ``driver_mtime_utc`` is recorded beside it.
    """
    candidate = bundle_source_candidate(bundle)
    state = repo_state(candidate) if candidate is not None else None
    if state is not None:
        state["note"] = "checkout HEAD at gate time; not evidence of the bundle's build commit"
    return state


def verdict_env(environ: dict[str, str]) -> dict[str, str]:
    """Inherited variables that can change a verdict, for the report."""
    recorded = {}
    for name in sorted(environ):
        if name in GATE_SET_ENV or not name.startswith(VERDICT_ENV_PREFIXES):
            continue
        recorded[name] = "<redacted>" if SECRET_ENV_RE.search(name) else portable(environ[name])
    return recorded


def expected_ay_pin() -> str:
    sys.path.insert(0, str(SCRIPTS_DIR))
    try:
        from ay_manifest_pin import expected_ay_pin_from_cargo_toml
    finally:
        sys.path.pop(0)
    return expected_ay_pin_from_cargo_toml(REPO_ROOT)


def ay_cli_cache_root(environ: dict[str, str] | None = None) -> Path:
    """The directory holding ``trust-mc-ay-cli-<rev9>``, chosen exactly as
    scripts/build-pinned-ay-cli.sh chooses it: ``TRUST_MC_AY_CLI_CACHE_ROOT``,
    else ``~/Library/Caches`` on macOS, else ``${XDG_CACHE_HOME:-~/.cache}``."""
    env = os.environ if environ is None else environ
    if env.get(AY_CLI_CACHE_ROOT_ENV):
        return Path(env[AY_CLI_CACHE_ROOT_ENV])
    home = Path(env["HOME"]) if env.get("HOME") else Path.home()
    if sys.platform == "darwin":
        return home / "Library" / "Caches"
    return Path(env["XDG_CACHE_HOME"]) if env.get("XDG_CACHE_HOME") else home / ".cache"


def pinned_ay_cli_dir(pin: str, cache_root: Path, compiler_key: str) -> Path:
    """The compiler-bound directory produced by build-pinned-ay-cli.sh."""
    if not PIN_RE.match(pin):
        raise GateRefusal(f"Cargo.toml AY pin {pin!r} is not a 40-character lowercase sha")
    if not re.fullmatch(r"[0-9a-f]{64}", compiler_key):
        raise GateRefusal("AY compiler cache key must be a full lowercase sha256")
    return cache_root / f"trust-mc-ay-cli-{pin[:9]}" / f"compiler-{compiler_key}" / "release"


def default_ay_dir() -> Path:
    """Ask the helper for the held compiler's path; never guess a legacy cache."""
    try:
        result = subprocess.run(
            [str(SCRIPTS_DIR / "build-pinned-ay-cli.sh"), "--check-path"],
            check=True, capture_output=True, text=True,
        )
        binary = result.stdout.strip()
        if not binary:
            raise GateRefusal("the pinned AY helper returned no binary path")
        return Path(binary).parent
    except (OSError, subprocess.CalledProcessError) as err:
        raise GateRefusal(f"cannot resolve the compiler-bound AY CLI: {err}") from err


def preflight(bundle: Path, ay_dir: Path, *, need_bundle: bool = True) -> dict[str, Any]:
    """Refuse a run whose ay CLI misses the pin or whose bundle is absent.
    ``need_bundle=False`` (a --cache-only run, which starts no driver) checks
    the ay CLI alone; the cache keys carry the bundle's input identity."""
    driver = bundle / "bin" / "trust-mc-driver"
    compiler = bundle / "bin" / "trust-mc-compiler"
    have_driver = driver.is_file() and os.access(driver, os.X_OK)
    if need_bundle and not have_driver:
        raise GateRefusal(f"bundle driver missing or not executable: {driver}")
    ay = ay_dir / "ay"
    if not ay.is_file() or not os.access(ay, os.X_OK):
        raise GateRefusal(
            f"pinned ay CLI missing: {ay} (scripts/build-pinned-ay-cli.sh builds the "
            "Cargo.toml pin into the default --ay-dir)"
        )
    try:
        pin = expected_ay_pin()
    except ValueError as err:
        raise GateRefusal(f"cannot derive the Cargo.toml AY pin: {err}") from err
    ay_out = subprocess.run([str(ay), "--version"], capture_output=True, text=True)
    ay_text = (ay_out.stdout or "") + (ay_out.stderr or "")
    if ay_out.returncode != 0:
        raise GateRefusal(f"{ay} --version exited {ay_out.returncode}")
    check_ay_version(ay_text, pin)
    ay_record = {
        "path": portable(ay),
        "version": ay_text.strip().splitlines()[0],
        "build_commit": pin,
        "cargo_toml_pin": pin,
        "pin_match": True,
        "binary_sha256": sha256_file(ay),
    }
    receipt = ay_dir.parent / "builder.json"
    if receipt.is_file():
        try:
            builder = json.loads(receipt.read_text())
            if (builder["schema"] != AY_BUILD_SCHEMA or builder["ay_commit"] != pin
                    or builder["binary_sha256"] != ay_record["binary_sha256"]):
                raise ValueError("receipt does not bind this AY binary and pin")
            ay_record["builder"] = builder["builder"]
        except (OSError, ValueError, KeyError, TypeError) as err:
            raise GateRefusal(f"invalid AY builder receipt: {receipt}: {err}") from err
    if not have_driver:
        return {"bundle": {"dir": portable(bundle), "absent": True, "driver_sha256": "absent",
                           "driver_version": "absent (--cache-only)"}, "ay": ay_record}
    ver = subprocess.run([str(driver), "--version"], capture_output=True, text=True)
    if ver.returncode != 0:
        raise GateRefusal(f"{driver} --version exited {ver.returncode}")
    bundle_repo = bundle_checkout_at_run(bundle)
    driver_mtime = _dt.datetime.fromtimestamp(driver.stat().st_mtime, _dt.timezone.utc)
    return {
        "bundle": {
            "dir": portable(bundle),
            "driver_sha256": sha256_file(driver),
            "driver_version": ver.stdout.strip(),
            "compiler_sha256": sha256_file(compiler) if compiler.is_file() else None,
            "driver_mtime_utc": driver_mtime.replace(microsecond=0).isoformat(),
            "checkout_at_run": bundle_repo,
        },
        "ay": ay_record,
    }


# --------------------------------------------------------------------------
# Running
# --------------------------------------------------------------------------


@dataclasses.dataclass(frozen=True)
class Job:
    entry: EntrySpec
    lane: str
    source: Path


def build_command(driver: Path, job: Job, harness_timeout: int, source: Path | None = None) -> list[str]:
    cmd = [str(driver), str(source or job.source), "-Z", "unstable-options",
           f"--harness-timeout={harness_timeout}s"]
    if job.lane == "chc":
        cmd.append("--ay-chc")
    cmd.extend(job.entry.flags)
    return cmd


def wall_timeout(entry: EntrySpec, harness_timeout: int, slack: int) -> int:
    return slack + len(entry.harnesses) * (2 * harness_timeout + 30)


def run_job(
    job: Job,
    *,
    driver: Path,
    env: dict[str, str],
    harness_timeout: int,
    slack: int,
    log_dir: Path,
) -> dict[str, Any]:
    """One (file, lane) run, unscheduled (the scaled path is ``run_jobs``)."""
    limit = wall_timeout(job.entry, harness_timeout, slack)
    started = time.monotonic()
    timed_out = False
    with tempfile.TemporaryDirectory(prefix="dual-gate-") as cwd:
        # The driver writes and re-reads `<stem>__<harness>.symtab.*` artifacts
        # NEXT TO THE SOURCE FILE. Running both lanes of one file concurrently
        # against the shared source made them race on those artifacts ("SMT-LIB2
        # file not found"), and it also wrote into the checkout. Each run
        # therefore verifies its own private copy.
        source_copy = Path(cwd) / job.source.name
        shutil.copyfile(job.source, source_copy)
        cmd = build_command(driver, job, harness_timeout, source_copy)
        proc = subprocess.Popen(
            cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            text=True, errors="replace", start_new_session=True,
        )
        try:
            output, _ = proc.communicate(timeout=limit)
        except subprocess.TimeoutExpired:
            timed_out = True
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            output, _ = proc.communicate()
    seconds = round(time.monotonic() - started, 1)
    return score_output(job, output, cmd=cmd, exit_code=None if timed_out else proc.returncode,
                        timed_out=timed_out, seconds=seconds, limit=limit, log_dir=log_dir)


# The driver's budget-bound unknown reasons (SolverUnknownReason::is_budget_bound
# in trust-mc-driver/src/verification_provenance.rs): an outcome that depends on
# the time or memory the run had, not only on its inputs.
BUDGET_BOUND_REASONS = ("Timeout", "TranslationTimeout", "PreSolveDeadline", "Memout", "BudgetExhausted",
                        "DriverTimeout", "CompileTimeout")
_BUDGET_MARKER_RE = re.compile(r"\[AY:(?:UNKNOWN_REASON|STAGE_SKIPPED:[^\]\s]*?):(?:%s)\]"
                               % "|".join(BUDGET_BOUND_REASONS))


def budget_bound(output: str) -> bool:
    """Did any harness of this run end on a budget (a solver or driver
    timeout, a memout, a stage skipped for want of time)? Such an output is
    not a function of the run's inputs: the entry cache never stores it, so a
    load-dependent verdict on main is recomputed beside each branch instead of
    standing for it."""
    return bool(_BUDGET_MARKER_RE.search(output))


def score_output(
    job: Job,
    output: str,
    *,
    cmd: list[str],
    exit_code: int | None,
    timed_out: bool,
    seconds: float,
    limit: int,
    log_dir: Path,
    extra: dict[str, Any] | None = None,
) -> dict[str, Any]:
    """Classify one driver output against the CURRENT manifest. A cached
    output is scored by exactly this function, so a re-scored row judges what
    a fresh one would."""
    safe = re.sub(r"[^A-Za-z0-9_.-]+", "_", job.entry.path)
    log_path = log_dir / job.lane / f"{safe}.log"
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text(output, encoding="utf-8")
    proc_returncode = exit_code
    runs = parse_driver_output(output)
    rows = []
    for spec in job.entry.harnesses:
        row = classify_harness(spec, job.lane, find_run(runs, spec.name), timed_out=timed_out)
        row["path"] = job.entry.path
        row["kind"] = job.entry.kind
        if row["class"] == "error":
            row["output_tail"] = output.strip().splitlines()[-12:]
        rows.append(row)
    declared = {h.name for h in job.entry.harnesses}
    unlisted = sorted(k for k in runs if k.split("::")[-1] not in declared)
    run = {
        "path": job.entry.path,
        "lane": job.lane,
        "command": [Path(cmd[0]).name, job.entry.path, *cmd[2:]],
        "exit_code": None if timed_out else proc_returncode,
        "timed_out": timed_out,
        "wall_limit_s": limit,
        "seconds": seconds,
        "unlisted_harnesses": unlisted,
        "budget_bound": timed_out or budget_bound(output),
    }
    run.update(extra or {})
    return {"run": run, "rows": rows}


# --------------------------------------------------------------------------
# Scaling and reuse (scripts/host_room.py; docs/landing-gates.md)
# --------------------------------------------------------------------------

ENTRY_CACHE_SCHEMA = "trust-mc.dual-entry-cache/v2"


def _host_room():
    sys.path.insert(0, str(SCRIPTS_DIR))
    try:
        import host_room  # noqa: PLC0415
    finally:
        sys.path.pop(0)
    return host_room


def entry_cache_key(
    *,
    bundle_identity: str,
    ay_version: str,
    ay_identity: dict[str, Any],
    job: Job,
    source_sha256: str,
    harness_timeout: int,
    wall_limit_s: int,
    gate_sha256: str,
    inherited_env: dict[str, str],
) -> str:
    """The COMPLETE input set of one (file, lane) driver run: the bundle's
    input identity (tree, toolchain, pins, build profile), the ay CLI, the lane,
    the source bytes, the flags, both time limits, this script, and the
    inherited environment that can change a verdict. Any element missing from
    the key would let a run stand for one it is not."""
    payload = {
        "schema": ENTRY_CACHE_SCHEMA,
        "bundle_identity": bundle_identity,
        "ay_version": ay_version,
        "ay_identity": ay_identity,
        "ay_build_protocol": AY_BUILD_PROTOCOL,
        "lane": job.lane,
        "path": job.entry.path,
        "source_sha256": source_sha256,
        "flags": list(job.entry.flags),
        "harness_timeout_s": harness_timeout,
        "wall_limit_s": wall_limit_s,
        "gate_sha256": gate_sha256,
        "inherited_env": dict(sorted(inherited_env.items())),
    }
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()


def cache_path(cache_dir: Path, key: str) -> Path:
    return cache_dir / key[:2] / f"{key}.json"


def cache_load(cache_dir: Path, key: str) -> dict[str, Any] | None:
    path = cache_path(cache_dir, key)
    try:
        record = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    if record.get("schema") != ENTRY_CACHE_SCHEMA or record.get("key") != key:
        return None
    try:
        os.utime(path)          # a reuse keeps the entry from being pruned
    except OSError:
        pass
    return record


def cache_store(cache_dir: Path, key: str, record: dict[str, Any]) -> None:
    path = cache_path(cache_dir, key)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(f".tmp{os.getpid()}")
    tmp.write_text(json.dumps({"schema": ENTRY_CACHE_SCHEMA, "key": key, **record}), encoding="utf-8")
    os.replace(tmp, path)


def _dual_task(
    index: int,
    job: Job,
    *,
    driver: Path,
    env: dict[str, str],
    harness_timeout: int,
    slack: int,
    log_dir: Path,
    history: dict[tuple[str, str], dict[str, Any]],
    results: list[dict[str, Any]],
    announce: Any,
    cache: tuple[Path | None, str | None],
    cap_mb: int | None = None,
):
    """One (file, lane) run as a scaled-runner task (``host_room.run_tasks``)."""
    hr = _host_room()
    limit = wall_timeout(job.entry, harness_timeout, slack)
    state: dict[str, Any] = {}

    def prepare():
        # Each attempt verifies its own private copy of the source (see run_job).
        cwd = tempfile.mkdtemp(prefix="dual-gate-")
        state["cwd"] = cwd
        source_copy = Path(cwd) / job.source.name
        shutil.copyfile(job.source, source_copy)
        state["cmd"] = build_command(driver, job, harness_timeout, source_copy)
        return state["cmd"], env, cwd, limit

    def cleanup() -> None:
        shutil.rmtree(state.pop("cwd", ""), ignore_errors=True)

    def done(output: str, outcome: Any) -> None:
        extra = {"peak_rss_mb": outcome.peak_rss_mb, "cpu_s": outcome.cpu_s, "cap_mb": outcome.cap_mb,
                 "attempts": outcome.attempts}
        result = score_output(job, output, cmd=state["cmd"], exit_code=outcome.exit_code,
                              timed_out=outcome.timed_out, seconds=outcome.wall_s, limit=limit,
                              log_dir=log_dir, extra=extra)
        results.append(result)
        cache_dir, key = cache
        # Only a run that ended on its own, with no harness ended by a budget,
        # is stored: its output is then a function of the key's inputs. A
        # timeout, a signal or a budget-bound harness is re-run next time.
        if (cache_dir is not None and key is not None and not outcome.timed_out
                and outcome.exit_code is not None and outcome.exit_code >= 0
                and not result["run"]["budget_bound"]):
            cache_store(cache_dir, key, {
                "output": output, "command": state["cmd"], "exit_code": outcome.exit_code,
                "timed_out": False, "seconds": outcome.wall_s, "peak_rss_mb": outcome.peak_rss_mb,
                "cpu_s": outcome.cpu_s, "created_utc": utc_now(),
            })
        announce(job, result, "")

    prior = history.get((job.entry.path, job.lane))
    expected = prior.get("seconds") if prior else None
    return hr.Task(key=f"{job.lane}:{job.entry.path}", expected_s=expected, prepare=prepare,
                   done=done, cleanup=cleanup, alone=cap_mb is not None and runs_alone(prior, cap_mb))


def load_history(path: Path | None) -> dict[tuple[str, str], dict[str, Any]]:
    """(path, lane) -> the prior run record (seconds, peak_rss_mb, cpu_s)."""
    if path is None:
        return {}
    try:
        report = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as err:
        print(f"[dual-gate] history {path} unreadable ({err}); scheduling without it", file=sys.stderr)
        return {}
    return {(r["path"], r["lane"]): r for r in report.get("runs", []) if "path" in r and "lane" in r}


# The share of a pool's children whose measured peak sizes the pool's need.
# The rest, whose own history says they outgrow the pool's cap, run alone.
POOL_NEED_QUANTILE = 0.95


def history_need_mb(history: dict[tuple[str, str], dict[str, Any]], lanes: Iterable[str], floor_mb: int) -> int:
    """The pool's per-child need: the peak POOL_NEED_QUANTILE of these lanes'
    prior runs stayed under (plus a quarter), never under ay's usable floor.
    Not the largest: on 2026-10-15 main's CHC side peaked at 41 MiB (median),
    882 MiB (95th percentile) and 9235 MiB (one file), and a need of 1.25 x
    9235 MiB left a 24 GiB host no room for even one driver. A run whose own
    peak outgrows the pool's cap runs alone instead (``runs_alone``)."""
    peaks = sorted(r["peak_rss_mb"] for (_, lane), r in history.items()
                   if lane in lanes and isinstance(r.get("peak_rss_mb"), int))
    if not peaks:
        return floor_mb
    at = min(len(peaks) - 1, int(POOL_NEED_QUANTILE * len(peaks)))
    return max(floor_mb, int(peaks[at] * 1.25))


def runs_alone(prior: dict[str, Any] | None, cap_mb: int) -> bool:
    """A run whose last peak (plus a quarter) exceeds the pool's per-child cap
    would cross it and be killed: it runs after the pool, alone and uncapped,
    as a run that crossed its cap is re-run, without the killed attempt."""
    peak = (prior or {}).get("peak_rss_mb")
    return isinstance(peak, int) and int(peak * 1.25) > cap_mb


def history_threads(history: dict[tuple[str, str], dict[str, Any]], lanes: Iterable[str]) -> float:
    """Cores one child keeps busy: CPU seconds over wall seconds of the prior
    runs that lasted long enough to say (at least 1.0)."""
    cpu = wall = 0.0
    for (_, lane), r in history.items():
        if lane in lanes and isinstance(r.get("cpu_s"), (int, float)) and r.get("seconds", 0) >= 5:
            cpu += r["cpu_s"]
            wall += r["seconds"]
    return max(1.0, round(cpu / wall, 2)) if wall else 1.0


def summarize(rows: list[dict[str, Any]], lanes: Iterable[str], strict: bool) -> dict[str, Any]:
    per_lane: dict[str, dict[str, int]] = {}
    for lane in lanes:
        counts = {cls: 0 for cls in CLASSES}
        for row in rows:
            if row["lane"] == lane:
                counts[row["class"]] += 1
        counts["total"] = sum(counts[cls] for cls in CLASSES)
        counts["property_mismatch"] = sum(
            1 for row in rows if row["lane"] == lane and row["property_ok"] is False
        )
        per_lane[lane] = counts
    def ident(row: dict[str, Any]) -> dict[str, Any]:
        return {"path": row["path"], "harness": row["harness"], "lane": row["lane"],
                "class": row["class"], "detail": row["detail"], "known_red": row["known_red"],
                "known_red_class": row["known_red_class"], "evidence": row["evidence"]}
    gating = [ident(r) for r in rows if is_gating(r, strict)]
    decided = sum(1 for r in rows if r["verdict"] in DECIDED_VERDICTS)
    reasons = []
    if gating:
        reasons.append("gating-rows")
    if not rows:
        reasons.append("no-rows-scored")
    elif decided == 0:
        reasons.append("no-decided-verdict")
    return {
        "per_lane": per_lane,
        "decided_rows": decided,
        "soundness_rows": [ident(r) for r in rows if r["soundness"]],
        "false_certificate_rows": [ident(r) for r in rows if r["class"] == "false-certificate"],
        "gating_rows": gating,
        "known_red_now_green": [ident(r) for r in rows if r["known_red"] and r["class"] == "match"],
        # Red for a different reason than the manifest records: the flag no
        # longer excuses the row, and the manifest needs the new class (or none).
        "known_red_class_changed": [
            ident(r) for r in rows
            if r["known_red"] and r["class"] not in ("match", r["known_red_class"])
        ],
        "needs_review": sorted({f"{r['path']}::{r['harness']}" for r in rows if r["needs_review"]}),
        "gate_reasons": reasons,
        "gate": "fail" if reasons else "pass",
    }


def select_entries(manifest: Manifest, only: list[str], kinds: list[str]) -> list[EntrySpec]:
    chosen = []
    for entry in manifest.entries:
        if kinds and entry.kind not in kinds:
            continue
        if only and not any(token in entry.path for token in only):
            continue
        chosen.append(entry)
    return chosen


def utc_now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--bundle", type=Path, default=DEFAULT_BUNDLE,
                        help="trust-mc bundle dir holding bin/trust-mc-driver (TRUST_MC_SYSROOT)")
    parser.add_argument("--ay-dir", type=Path, default=None,
                        help="directory with the pinned ay CLI, put first on PATH (default: "
                             "the compiler-bound cache selected by build-pinned-ay-cli.sh, "
                             "where scripts/build-pinned-ay-cli.sh builds it)")
    parser.add_argument("--lane", action="append", choices=LANES, dest="lanes")
    parser.add_argument("--jobs", default="auto",
                        help="driver processes at once: 'auto' (default) sizes them to the measured "
                             "room (scripts/host_room.py), or a number as an upper bound")
    parser.add_argument("--need-mb", type=int,
                        help="per-driver memory need, MiB (default: the largest peak in --history "
                             "plus a quarter, at least ay's 2048 MiB floor)")
    parser.add_argument("--history", type=Path,
                        help="a prior report: its per-run durations order the runs longest first "
                             "and its peaks size --need-mb")
    parser.add_argument("--entry-cache", type=Path,
                        help="reuse/store driver outputs keyed on their complete inputs "
                             "(needs --bundle-identity)")
    parser.add_argument("--cache-only", action="store_true",
                        help="start no driver: score the cached runs, and exit 3 (no report) when "
                             "any run is missing from --entry-cache")
    parser.add_argument("--bundle-identity",
                        help="the bundle's input identity (scripts/landing-gate.py computes it "
                             "from the tree, toolchain and pins)")
    parser.add_argument("--timeout", type=int, default=30, help="per-harness timeout, seconds")
    parser.add_argument("--wall-slack", type=int, default=180,
                        help="per-file wall-clock slack added to harnesses*(2*timeout+30)")
    parser.add_argument("--only", action="append", default=[], help="path substring filter")
    parser.add_argument("--kind", action="append", choices=KINDS, default=[])
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--log-dir", type=Path, help="keep per-run driver logs here")
    parser.add_argument("--strict", action="store_true",
                        help="also fail on false-failure and unknown rows not known-red for that class")
    parser.add_argument("--validate", action="store_true",
                        help="validate the manifest against the tree and exit")
    args = parser.parse_args(argv)

    try:
        manifest = load_manifest(args.manifest)
        drift = validate_against_tree(manifest)
        if drift:
            raise ManifestError(drift)
    except ManifestError as err:
        print("[dual-gate] manifest invalid:", file=sys.stderr)
        for problem in err.problems:
            print(f"  - {problem}", file=sys.stderr)
        return 2
    lanes = tuple(args.lanes) if args.lanes else LANES
    entries = select_entries(manifest, args.only, args.kind)
    harness_count = sum(len(e.harnesses) for e in entries)
    if args.validate:
        print(f"[dual-gate] manifest ok: {len(manifest.entries)} entries, "
              f"{sum(len(e.harnesses) for e in manifest.entries)} harnesses")
        return 0
    max_jobs: int | None = None
    if args.jobs != "auto":
        try:
            max_jobs = int(args.jobs)
        except ValueError:
            max_jobs = 0
    if (max_jobs is not None and max_jobs < 1) or args.timeout < 1:
        print("[dual-gate] --jobs must be 'auto' or positive, and --timeout positive", file=sys.stderr)
        return 2
    if args.cache_only and args.entry_cache is None:
        print("[dual-gate] --cache-only needs --entry-cache", file=sys.stderr)
        return 2
    if args.entry_cache is not None and not args.bundle_identity:
        print("[dual-gate] --entry-cache needs --bundle-identity (the key would be incomplete)",
              file=sys.stderr)
        return 2

    load_start = list(os.getloadavg())
    started_utc = utc_now()
    started = time.monotonic()
    # Provenance of what was scored is read BEFORE the run, and re-read after it
    # so a checkout or manifest that moved mid-run is visible in the report.
    trust_mc_start = repo_state(REPO_ROOT)
    manifest_sha_start = sha256_file(args.manifest)
    inherited_env = verdict_env(dict(os.environ))
    try:
        if args.ay_dir is None:
            args.ay_dir = default_ay_dir()
        pre = preflight(args.bundle, args.ay_dir, need_bundle=not args.cache_only)
    except GateRefusal as err:
        print(f"[dual-gate] REFUSED: {err}", file=sys.stderr)
        return 2

    env = dict(os.environ)
    env["PATH"] = f"{args.ay_dir}{os.pathsep}{env.get('PATH', '')}"
    env["TRUST_MC_SYSROOT"] = str(args.bundle)
    env["RUSTFLAGS"] = "-Awarnings"
    driver = args.bundle / "bin" / "trust-mc-driver"
    keep_logs = args.log_dir is not None
    log_dir = args.log_dir or Path(tempfile.mkdtemp(prefix="dual-gate-logs-"))

    jobs = [Job(entry, lane, manifest.source(entry))
            for entry in entries for lane in lanes if lane in entry.lanes]
    hr = _host_room()
    history = load_history(args.history)
    print(f"[dual-gate] {len(entries)} files, {harness_count} harnesses, {len(jobs)} runs, "
          f"lanes={','.join(lanes)} timeout={args.timeout}s")
    print(f"[dual-gate] driver {pre['bundle']['driver_sha256'][:12]} ({pre['bundle']['driver_version']}); "
          f"ay {pre['ay']['version']}")
    if inherited_env:
        print(f"[dual-gate] inherited verdict-relevant env (recorded): {', '.join(inherited_env)}")
    results: list[dict[str, Any]] = []
    gate_sha = sha256_file(Path(__file__).resolve())
    cache_hits = 0
    progress = [0]

    def announce(job: Job, result: dict[str, Any], how: str) -> None:
        progress[0] += 1
        bad = [r for r in result["rows"] if r["class"] != "match"]
        flag = " ".join(f"{r['harness']}={r['class']}" for r in bad) or "all match"
        print(f"[dual-gate] {progress[0]}/{len(jobs)} {job.lane} {job.entry.path} "
              f"{result['run']['seconds']}s{how}: {flag}", flush=True)

    keys: dict[int, str] = {}
    to_run: list[tuple[int, Job]] = []
    for index, job in enumerate(jobs):
        if args.entry_cache is not None:
            limit = wall_timeout(job.entry, args.timeout, args.wall_slack)
            key = entry_cache_key(
                bundle_identity=args.bundle_identity, ay_version=pre["ay"]["version"],
                ay_identity={"binary_sha256": pre["ay"]["binary_sha256"],
                             "builder": pre["ay"].get("builder")}, job=job,
                source_sha256=sha256_file(job.source), harness_timeout=args.timeout,
                wall_limit_s=limit, gate_sha256=gate_sha, inherited_env=inherited_env,
            )
            keys[index] = key
            record = cache_load(args.entry_cache, key)
            if record is not None:
                cache_hits += 1
                result = score_output(
                    job, record["output"], cmd=record["command"], exit_code=record["exit_code"],
                    timed_out=record["timed_out"], seconds=record["seconds"], limit=limit,
                    log_dir=log_dir, extra={"cached": key, "peak_rss_mb": record.get("peak_rss_mb"),
                                            "cpu_s": record.get("cpu_s")},
                )
                results.append(result)
                announce(job, result, f" (cached {key[:12]})")
                continue
        to_run.append((index, job))
    if args.entry_cache is not None:
        print(f"[dual-gate] entry cache: {cache_hits} of {len(jobs)} runs reused, {len(to_run)} to run")
    if args.cache_only and to_run:
        print(f"[dual-gate] CACHE-INCOMPLETE: {len(to_run)} runs are not in the entry cache "
              f"(first: {to_run[0][1].lane} {to_run[0][1].entry.path})")
        return 3

    plan = None
    if to_run:
        need_mb = args.need_mb or history_need_mb(history, lanes, hr.AY_MIN_CAP_MB)
        threads = history_threads(history, lanes)
        plan = hr.wait_for_plan(need_mb=need_mb, label="dual-gate " + ",".join(lanes),
                                threads_per_child=threads, max_jobs=max_jobs,
                                log=lambda line: print(line, flush=True))
        if not plan.admitted:
            print(f"[dual-gate] REFUSED: {plan.reason}", file=sys.stderr)
            return 2
    tasks = []
    for index, job in to_run:
        tasks.append(_dual_task(index, job, driver=driver, env=env, harness_timeout=args.timeout,
                                slack=args.wall_slack, log_dir=log_dir, history=history,
                                results=results, announce=announce,
                                cache=(args.entry_cache, keys.get(index)),
                                cap_mb=plan.cap_mb if plan else None))
    outcomes = hr.run_tasks(tasks, plan, log=lambda line: print(line, flush=True)) if tasks else {}
    breached = sorted(key for key, o in outcomes.items() if o.attempts > 1)

    rows = sorted((row for r in results for row in r["rows"]),
                  key=lambda r: (r["path"], r["harness"], r["lane"]))
    runs = sorted((r["run"] for r in results), key=lambda r: (r["path"], r["lane"]))
    summary = summarize(rows, lanes, args.strict)
    runtime = round(time.monotonic() - started, 1)
    manifest_rel = os.path.relpath(args.manifest.resolve(), REPO_ROOT)
    trust_mc_end = repo_state(REPO_ROOT)
    manifest_sha_end = sha256_file(args.manifest)

    def moved(a: dict[str, Any] | None, b: dict[str, Any] | None) -> bool:
        key = lambda s: None if s is None else (s["head"], s["dirty_tracked_paths"])  # noqa: E731
        return key(a) != key(b)
    report = {
        "schema": REPORT_SCHEMA,
        "provenance": {
            "started_at_utc": started_utc,
            "finished_at_utc": utc_now(),
            "runtime_seconds": runtime,
            "trust_mc": trust_mc_start,
            "trust_mc_changed_during_run": moved(trust_mc_start, trust_mc_end),
            "manifest": {"path": manifest_rel, "sha256": manifest_sha_start,
                         "changed_during_run": manifest_sha_start != manifest_sha_end},
            **pre,
            "host": {
                "platform": platform.platform(),
                "python": platform.python_version(),
                "cpu_count": os.cpu_count(),
                "load_average_start": [round(x, 2) for x in load_start],
                "load_average_end": [round(x, 2) for x in os.getloadavg()],
            },
            "config": {
                "lanes": list(lanes),
                "jobs": plan.jobs if plan else 0,
                "jobs_requested": args.jobs,
                "scaling": plan.record() if plan else None,
                "entry_cache": None if args.entry_cache is None else {
                    "dir": portable(args.entry_cache), "bundle_identity": args.bundle_identity,
                    "reused": cache_hits, "ran": len(to_run),
                    "not_stored_budget_bound": sum(1 for r in results if r["run"].get("budget_bound")
                                                   and "cached" not in r["run"])},
                "rerun_uncapped": breached,
                "history": None if args.history is None else portable(args.history),
                "harness_timeout_s": args.timeout,
                "wall_timeout_rule": f"{args.wall_slack} + harnesses * (2 * {args.timeout} + 30) seconds per file",
                "strict": args.strict,
                "only": args.only,
                "kinds": args.kind,
                "env": {"RUSTFLAGS": "-Awarnings", "TRUST_MC_SYSROOT": portable(args.bundle),
                        "PATH_first": portable(args.ay_dir)},
                "inherited_env": inherited_env,
            },
        },
        "summary": summary,
        "runs": runs,
        "rows": rows,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if not keep_logs:
        shutil.rmtree(log_dir, ignore_errors=True)

    for lane in lanes:
        counts = summary["per_lane"][lane]
        print(f"[dual-gate] {lane}: " + " ".join(f"{c}={counts[c]}" for c in CLASSES)
              + f" total={counts['total']}")
    for label, key in (("SOUNDNESS", "soundness_rows"), ("FALSE-CERTIFICATE", "false_certificate_rows")):
        for row in summary[key]:
            tag = "known-red" if known_red_applies(row) else "GATING"
            print(f"[dual-gate] {label} {tag}: {row['path']}::{row['harness']} [{row['lane']}] "
                  f"{row['detail']}" + (f" ({row['evidence']})" if row["evidence"] else ""))
    for row in summary["known_red_class_changed"]:
        print(f"[dual-gate] known-red row changed class ({row['known_red_class']} -> {row['class']}), "
              f"update the manifest: {row['path']}::{row['harness']} [{row['lane']}]")
    for row in summary["known_red_now_green"]:
        print(f"[dual-gate] known-red now green (flip the manifest): "
              f"{row['path']}::{row['harness']} [{row['lane']}]")
    for row in summary["gating_rows"]:
        if row["class"] == "error":
            print(f"[dual-gate] ERROR GATING: {row['path']}::{row['harness']} [{row['lane']}] {row['detail']}")
    print(f"[dual-gate] report {args.report} runtime {runtime}s gate={summary['gate']}"
          + (f" ({', '.join(summary['gate_reasons'])})" if summary["gate_reasons"] else "")
          + (f" logs {log_dir}" if keep_logs else ""))
    return 1 if summary["gate"] == "fail" else 0


if __name__ == "__main__":
    sys.exit(main())
