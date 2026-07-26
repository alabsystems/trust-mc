# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""ay / trust-mc replacement progress and audit tool.

Cross-references the frozen public replacement-harness inventory against a
*fresh* compiletest per-harness report and computes replacement progress:

  * how many PROOF rows are actually proven (verifier SUCCESS, zero fallback),
  * how many non-PROOF rows (CTREX / UNKNOWN / ERROR / BMC_SAFE) are closed,
    i.e. their observed outcome matches the recorded expectation,
  * and, under ``--require-complete``, whether 100% replacement accounting has
    been reached (exit nonzero otherwise).

This tool is informational/audit tooling. It never fabricates progress: when no
fresh report is supplied it prints ``MEASUREMENT MISSING -- no fresh run`` and
exits nonzero.

Inputs
------
1. The public inventory ``tests/trust-mc/replacement-harness-inventory.json``
   (schema ``{schema_version, suite, denominator, row_sha256, rows[]}`` with
   each row ``{file, harness, expected, lane}``; ``expected`` is one of
   PROOF / CTREX / UNKNOWN / ERROR / BMC_SAFE).

2. A compiletest per-harness report. Two report shapes are accepted:

   a. The canonical trust-mc proof-summary artifact
      (``trust-mc-driver/src/proof_summary.rs``, ``schema_version: 1``,
      ``artifact_kind: "trust_mc.proof_summary_pointer"``) with a
      ``harnesses[]`` array of
      ``{harness, crate_name, status, effective_success, validation_status,
        proof_qualifiers[], property_counts{...}}`` entries.

   b. The ``scripts/ay-compiletest.sh`` per-harness report: a list of records
      (or ``{"harnesses": [...]}``) each carrying a ``harness`` name plus the
      verifier markers it parsed from ``trust-mc`` stdout --
      ``ctrex_category`` (from ``[AY:CTREX_CAT:...]``),
      ``sound_fallback`` (from ``[AY:SOUND_FALLBACK:n]``) and
      ``effective_success`` (from ``[AY:EFFECTIVE_SUCCESS:reason]``).

The two shapes are auto-detected.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

TOOL = "replacement_progress"
BRAND = "ay / trust-mc"

# Inventory expectation vocabulary (see the frozen inventory generator).
EXPECTED_OUTCOMES = ("PROOF", "CTREX", "UNKNOWN", "ERROR", "BMC_SAFE")

# Verifier per-check / per-harness status vocabulary
# (trust-mc-driver/src/property_model.rs::CheckStatus, serde UPPERCASE, plus the
#  harness-level VerificationStatus SUCCESS|FAILURE). UNKNOWN displays as
#  UNDETERMINED.
HARNESS_SUCCESS = "SUCCESS"
HARNESS_FAILURE = "FAILURE"


# --------------------------------------------------------------------------- #
# Observed (actual) outcome model
# --------------------------------------------------------------------------- #
@dataclass(frozen=True)
class Observed:
    """A single harness result distilled from a fresh report."""

    harness: str
    crate_name: str | None
    status: str  # SUCCESS | FAILURE | <missing>
    effective_success: bool
    sound_fallback: int
    ctrex_category: str | None
    failed: int
    undetermined: int
    unknown: int
    validation_status: str | None

    def classify(self) -> str:
        """Map an observed harness result onto the inventory vocabulary.

        Returns one of EXPECTED_OUTCOMES so it can be compared row-for-row.
        """
        # A clean, fully-validated success with no soundness fallback proves a
        # PROOF row.
        if self.status == HARNESS_SUCCESS:
            if self.sound_fallback == 0:
                if self.undetermined == 0 and self.unknown == 0:
                    return "PROOF"
                # Success reported but with inconclusive checks underneath.
                return "UNKNOWN"
            # Success only via a sound over-approximation / fallback. Surfaced
            # as BMC_SAFE: closed, but not a clean inductive/bit-precise proof.
            return "BMC_SAFE"
        # Non-success.
        if self.ctrex_category:
            return "CTREX"
        if self.undetermined > 0 or self.unknown > 0:
            return "UNKNOWN"
        if self.status == HARNESS_FAILURE and self.failed > 0:
            return "CTREX"
        return "ERROR"


@dataclass
class RowResult:
    file: str
    harness: str
    expected: str
    lane: str
    observed: Observed | None
    actual: str  # classified observed outcome, or "MISSING"
    is_proof: bool
    matched: bool  # expected == actual
    proven: bool  # PROOF row, SUCCESS, zero fallback
    closed: bool  # non-PROOF row whose outcome is justified (== expected)
    fallback: int


@dataclass
class Progress:
    suite: str
    denominator: int
    rows: list[RowResult] = field(default_factory=list)

    # PROOF accounting
    proof_total: int = 0
    proof_proven: int = 0
    proof_fallback: int = 0  # PROOF rows that "passed" only via fallback
    proof_missing: int = 0
    proof_regressed: int = 0  # PROOF rows that did NOT prove

    # non-PROOF accounting
    nonproof_total: int = 0
    nonproof_closed: int = 0
    nonproof_missing: int = 0
    nonproof_unjustified: int = 0

    # coverage
    rows_measured: int = 0
    rows_missing: int = 0

    @property
    def complete(self) -> bool:
        """Exact 100% replacement-accounting criterion.

        Complete iff EVERY inventory row was measured against the fresh report
        and:
          * every PROOF row is SUCCESS with zero soundness fallback, and
          * every non-PROOF row is justified (observed outcome == expected).
        Any missing measurement, any PROOF fallback, any PROOF regression, or
        any unjustified non-PROOF row makes the suite incomplete.
        """
        return (
            self.rows_missing == 0
            and self.proof_total == self.proof_proven
            and self.proof_fallback == 0
            and self.proof_regressed == 0
            and self.nonproof_total == self.nonproof_closed
            and self.nonproof_unjustified == 0
        )


# --------------------------------------------------------------------------- #
# Report parsing
# --------------------------------------------------------------------------- #
def _as_int(value: Any, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _normalize_harness(name: str) -> str:
    """Normalize a harness name for matching across inventory/report.

    Inventory harnesses may be bare (``check_foo``) or path-qualified
    (``mod::check_foo``); report pretty_names may carry a leading ``crate::``.
    We index by both the full name and its terminal segment.
    """
    return name.strip()


def _harness_keys(name: str) -> tuple[str, str]:
    full = _normalize_harness(name)
    tail = full.rsplit("::", 1)[-1]
    return full, tail


def _qualifiers_fallback(qualifiers: Iterable[Any]) -> int:
    """Extract a sound_fallback=N count from proof_qualifiers, if present."""
    for qual in qualifiers or []:
        text = str(qual)
        if text.startswith("sound_fallback="):
            return _as_int(text.split("=", 1)[1])
    return 0


def _observed_from_proof_summary(entry: dict[str, Any]) -> Observed:
    counts = entry.get("property_counts") or {}
    status_raw = str(entry.get("status", "")).strip().lower()
    if status_raw == "success":
        status = HARNESS_SUCCESS
    elif status_raw == "failure":
        status = HARNESS_FAILURE
    else:
        status = status_raw.upper() or "<missing>"
    return Observed(
        harness=str(entry.get("harness", "")),
        crate_name=entry.get("crate_name"),
        status=status,
        effective_success=bool(entry.get("effective_success", False)),
        sound_fallback=_qualifiers_fallback(entry.get("proof_qualifiers", [])),
        ctrex_category=None,
        failed=_as_int(counts.get("failed")),
        undetermined=_as_int(counts.get("undetermined")),
        unknown=_as_int(counts.get("unknown")),
        validation_status=entry.get("validation_status"),
    )


def _observed_from_ay_compiletest(entry: dict[str, Any]) -> Observed:
    # scripts/ay-compiletest.sh marker-derived record.
    status_raw = str(entry.get("status", "")).strip().upper()
    if status_raw not in (HARNESS_SUCCESS, HARNESS_FAILURE):
        # Fall back to effective_success / failed markers.
        if bool(entry.get("effective_success", False)):
            status_raw = HARNESS_SUCCESS
        elif entry.get("failed") or entry.get("ctrex_category"):
            status_raw = HARNESS_FAILURE
        else:
            status_raw = status_raw or "<missing>"
    return Observed(
        harness=str(entry.get("harness", "")),
        crate_name=entry.get("crate_name") or entry.get("crate"),
        status=status_raw,
        effective_success=bool(entry.get("effective_success", False)),
        sound_fallback=_as_int(entry.get("sound_fallback")),
        ctrex_category=(entry.get("ctrex_category") or None),
        failed=_as_int(entry.get("failed")),
        undetermined=_as_int(entry.get("undetermined")),
        unknown=_as_int(entry.get("unknown")),
        validation_status=entry.get("validation_status"),
    )


def parse_report(report: Any) -> tuple[list[Observed], str]:
    """Auto-detect and parse a fresh report into Observed records.

    Returns ``(observed, report_kind)``.
    """
    if isinstance(report, dict):
        kind = str(report.get("artifact_kind", ""))
        harnesses = report.get("harnesses")
        if harnesses is None and isinstance(report.get("results"), list):
            harnesses = report["results"]
        if harnesses is None:
            raise ValueError("report object has no 'harnesses' array")
        if kind.startswith("trust_mc.proof_summary"):
            return [_observed_from_proof_summary(h) for h in harnesses], "proof_summary"
        # Heuristic: proof_summary entries carry 'property_counts'.
        if harnesses and isinstance(harnesses[0], dict) and "property_counts" in harnesses[0]:
            return [_observed_from_proof_summary(h) for h in harnesses], "proof_summary"
        return [_observed_from_ay_compiletest(h) for h in harnesses], "ay-compiletest"
    if isinstance(report, list):
        return [_observed_from_ay_compiletest(h) for h in report], "ay-compiletest"
    raise ValueError("unrecognized report shape (expected object or array)")


# --------------------------------------------------------------------------- #
# Inventory loading
# --------------------------------------------------------------------------- #
def load_inventory(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if "rows" not in data or not isinstance(data["rows"], list):
        raise ValueError(f"{path}: not a replacement-harness inventory (no 'rows')")
    return data


def _index_observed(observed: list[Observed]) -> dict[tuple[str, str], Observed]:
    index: dict[tuple[str, str], Observed] = {}
    for obs in observed:
        full, tail = _harness_keys(obs.harness)
        # Full name wins; tail is a fallback key only registered if unambiguous.
        index.setdefault(("full", full), obs)
        index.setdefault(("crate", f"{obs.crate_name}::{full}"), obs)
    # Tail index, registered only when a tail is unique.
    tails: dict[str, list[Observed]] = {}
    for obs in observed:
        _, tail = _harness_keys(obs.harness)
        tails.setdefault(tail, []).append(obs)
    for tail, group in tails.items():
        if len(group) == 1:
            index.setdefault(("tail", tail), group[0])
    return index


def _lookup(
    index: dict[tuple[str, str], Observed], row: dict[str, Any]
) -> Observed | None:
    harness = row.get("harness", "")
    full, tail = _harness_keys(harness)
    file_stem = Path(str(row.get("file", ""))).stem
    for key in (
        ("crate", f"{file_stem}::{full}"),
        ("full", full),
        ("tail", tail),
    ):
        hit = index.get(key)
        if hit is not None:
            return hit
    return None


# --------------------------------------------------------------------------- #
# Core computation
# --------------------------------------------------------------------------- #
def compute_progress(inventory: dict[str, Any], observed: list[Observed]) -> Progress:
    index = _index_observed(observed)
    prog = Progress(
        suite=str(inventory.get("suite", "tests/trust-mc")),
        denominator=_as_int(inventory.get("denominator"), len(inventory["rows"])),
    )

    for row in inventory["rows"]:
        expected = str(row.get("expected", "")).upper()
        is_proof = expected == "PROOF"
        obs = _lookup(index, row)

        if obs is None:
            actual = "MISSING"
            matched = proven = closed = False
            fallback = 0
            prog.rows_missing += 1
        else:
            actual = obs.classify()
            fallback = obs.sound_fallback
            matched = actual == expected
            prog.rows_measured += 1
            if is_proof:
                proven = actual == "PROOF" and obs.status == HARNESS_SUCCESS and fallback == 0
                closed = False
            else:
                proven = False
                closed = matched

        rr = RowResult(
            file=str(row.get("file", "")),
            harness=str(row.get("harness", "")),
            expected=expected,
            lane=str(row.get("lane", "")),
            observed=obs,
            actual=actual,
            is_proof=is_proof,
            matched=matched,
            proven=proven,
            closed=closed,
            fallback=fallback,
        )
        prog.rows.append(rr)

        if is_proof:
            prog.proof_total += 1
            if obs is None:
                prog.proof_missing += 1
            elif proven:
                prog.proof_proven += 1
            elif obs.status == HARNESS_SUCCESS and fallback > 0:
                prog.proof_fallback += 1
            else:
                prog.proof_regressed += 1
        else:
            prog.nonproof_total += 1
            if obs is None:
                prog.nonproof_missing += 1
            elif closed:
                prog.nonproof_closed += 1
            else:
                prog.nonproof_unjustified += 1

    return prog


# --------------------------------------------------------------------------- #
# Rendering
# --------------------------------------------------------------------------- #
def _pct(num: int, den: int) -> str:
    if den == 0:
        return "n/a"
    return f"{100.0 * num / den:5.1f}%"


def render_text(prog: Progress, *, verbose: bool) -> str:
    lines: list[str] = []
    lines.append(f"{BRAND} replacement progress  ({TOOL})")
    lines.append(f"  suite        : {prog.suite}")
    lines.append(f"  denominator  : {prog.denominator}")
    lines.append(f"  rows measured: {prog.rows_measured}/{len(prog.rows)} "
                 f"({_pct(prog.rows_measured, len(prog.rows))})")
    lines.append("")
    lines.append("PROOF rows (must reach SUCCESS, zero fallback):")
    lines.append(f"  proven        : {prog.proof_proven}/{prog.proof_total} "
                 f"({_pct(prog.proof_proven, prog.proof_total)})")
    lines.append(f"  passed-on-fallback (NOT counted as proven): {prog.proof_fallback}")
    lines.append(f"  regressed     : {prog.proof_regressed}")
    lines.append(f"  not measured  : {prog.proof_missing}")
    lines.append("")
    lines.append("non-PROOF rows (CTREX / UNKNOWN / ERROR / BMC_SAFE; must match expectation):")
    lines.append(f"  closed        : {prog.nonproof_closed}/{prog.nonproof_total} "
                 f"({_pct(prog.nonproof_closed, prog.nonproof_total)})")
    lines.append(f"  unjustified   : {prog.nonproof_unjustified}")
    lines.append(f"  not measured  : {prog.nonproof_missing}")
    lines.append("")
    accounted = prog.proof_proven + prog.nonproof_closed
    lines.append(f"replacement accounting: {accounted}/{len(prog.rows)} "
                 f"({_pct(accounted, len(prog.rows))})")
    lines.append(f"complete: {'YES' if prog.complete else 'NO'}")

    if verbose:
        outstanding = [
            r for r in prog.rows
            if (r.is_proof and not r.proven) or (not r.is_proof and not r.closed)
        ]
        if outstanding:
            lines.append("")
            lines.append("outstanding rows:")
            for r in outstanding:
                reason = (
                    "not measured" if r.actual == "MISSING"
                    else f"expected={r.expected} actual={r.actual}"
                    + (f" fallback={r.fallback}" if r.fallback else "")
                )
                lines.append(f"  {r.file}::{r.harness}  [{reason}]")
    return "\n".join(lines)


def render_json(prog: Progress) -> str:
    accounted = prog.proof_proven + prog.nonproof_closed
    payload = {
        "tool": TOOL,
        "brand": BRAND,
        "suite": prog.suite,
        "denominator": prog.denominator,
        "rows_total": len(prog.rows),
        "rows_measured": prog.rows_measured,
        "rows_missing": prog.rows_missing,
        "proof": {
            "total": prog.proof_total,
            "proven": prog.proof_proven,
            "passed_on_fallback": prog.proof_fallback,
            "regressed": prog.proof_regressed,
            "not_measured": prog.proof_missing,
        },
        "non_proof": {
            "total": prog.nonproof_total,
            "closed": prog.nonproof_closed,
            "unjustified": prog.nonproof_unjustified,
            "not_measured": prog.nonproof_missing,
        },
        "replacement_accounting": {
            "accounted": accounted,
            "out_of": len(prog.rows),
        },
        "complete": prog.complete,
        "rows": [
            {
                "file": r.file,
                "harness": r.harness,
                "expected": r.expected,
                "actual": r.actual,
                "matched": r.matched,
                "proven": r.proven,
                "closed": r.closed,
                "fallback": r.fallback,
            }
            for r in prog.rows
        ],
    }
    return json.dumps(payload, indent=2, sort_keys=True)


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def build_parser() -> argparse.ArgumentParser:
    repo_default = (
        Path(__file__).resolve().parents[2]
        / "tests" / "trust-mc" / "replacement-harness-inventory.json"
    )
    parser = argparse.ArgumentParser(
        prog=TOOL,
        description=(
            f"{BRAND} replacement progress / audit tool. Cross-references the "
            "frozen replacement-harness inventory against a fresh compiletest "
            "per-harness report and reports replacement progress."
        ),
    )
    parser.add_argument(
        "--inventory",
        type=Path,
        default=repo_default,
        help=(
            "Public replacement-harness inventory JSON "
            "(default: tests/trust-mc/replacement-harness-inventory.json)."
        ),
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help=(
            "Fresh compiletest per-harness report JSON: either the trust-mc "
            "proof-summary artifact or a scripts/ay-compiletest.sh report. "
            "If omitted, the tool prints 'MEASUREMENT MISSING -- no fresh run' "
            "and exits nonzero."
        ),
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Output format (default: text).",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="List each outstanding (unproven/unclosed) row.",
    )
    parser.add_argument(
        "--require-complete",
        action="store_true",
        help=(
            "Exit nonzero unless 100%% replacement accounting is reached: every "
            "row measured, all PROOF rows SUCCESS with zero fallback, and all "
            "non-PROOF rows justified."
        ),
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    try:
        inventory = load_inventory(args.inventory)
    except (OSError, ValueError, json.JSONDecodeError) as err:
        sys.stderr.write(f"{TOOL}: ERROR: cannot load inventory: {err}\n")
        return 2

    # No fresh report -> measurement is missing. Never fabricate progress.
    if args.report is None:
        sys.stdout.write("MEASUREMENT MISSING -- no fresh run\n")
        sys.stderr.write(
            f"{TOOL}: no --report supplied; run compiletest under AY and pass the "
            "resulting proof-summary / ay-compiletest report.\n"
        )
        return 3

    try:
        report = json.loads(args.report.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as err:
        sys.stdout.write("MEASUREMENT MISSING -- no fresh run\n")
        sys.stderr.write(f"{TOOL}: ERROR: cannot load report {args.report}: {err}\n")
        return 3

    try:
        observed, kind = parse_report(report)
    except ValueError as err:
        sys.stdout.write("MEASUREMENT MISSING -- no fresh run\n")
        sys.stderr.write(f"{TOOL}: ERROR: unparseable report: {err}\n")
        return 3

    if not observed:
        sys.stdout.write("MEASUREMENT MISSING -- no fresh run\n")
        sys.stderr.write(f"{TOOL}: ERROR: report {args.report} has zero harnesses.\n")
        return 3

    prog = compute_progress(inventory, observed)

    if args.format == "json":
        sys.stdout.write(render_json(prog) + "\n")
    else:
        sys.stderr.write(f"{TOOL}: parsed {len(observed)} harness result(s) "
                         f"from a '{kind}' report.\n")
        sys.stdout.write(render_text(prog, verbose=args.verbose) + "\n")

    if args.require_complete and not prog.complete:
        sys.stderr.write(
            f"{TOOL}: REPLACEMENT INCOMPLETE -- "
            f"proof_proven={prog.proof_proven}/{prog.proof_total} "
            f"(fallback={prog.proof_fallback}, regressed={prog.proof_regressed}), "
            f"nonproof_closed={prog.nonproof_closed}/{prog.nonproof_total} "
            f"(unjustified={prog.nonproof_unjustified}), "
            f"rows_missing={prog.rows_missing}.\n"
        )
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
