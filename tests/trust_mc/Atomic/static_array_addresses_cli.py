#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Run real CHC checks with grades and failed-check evidence; no oracle ledger edits.

Run through build-slot with --bundle and an unused --evidence directory. This
is focused integration evidence, not the normal landing or release gate.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

SAFE = (
    "slice_safe", "choice_safe", "symbolic_safe", "iter_safe",
    "aliases_cross_view_safe", "sequential_rmw_safe", "cursor_snapshot_safe",
    "early_break_safe", "conditional_write_safe", "two_objects_safe", "iter_skip_safe",
)
BUG = (
    "slice_bug", "choice_bug", "symbolic_bug", "iter_bug", "sequential_rmw_bug",
    "early_break_bug", "conditional_write_bug", "oob_bug",
)
BUG_ASSERTIONS = {
    "slice_bug": "stale cell", "choice_bug": "stale false arm",
    "symbolic_bug": "wrong selected", "iter_bug": "stale last cell",
    "sequential_rmw_bug": "stale old RMW",
    "early_break_bug": "unvisited cell is not written",
    "conditional_write_bug": "missing write on false path",
}
GUARDED = ("guard_mixed_producer", "guard_opaque_receiver")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", required=True, type=Path)
    parser.add_argument("--evidence", required=True, type=Path)
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args()
    driver = args.bundle.resolve() / "bin/trust-mc-driver"
    source = Path(__file__).resolve().with_suffix(".rs")
    # This script's stem has _cli; the probe is the adjacent Rust fixture.
    source = source.with_name("static_array_addresses.rs")
    args.evidence.mkdir(parents=True, exist_ok=False)
    report = {"source_sha256": sha(source), "driver_sha256": sha(driver), "rows": []}
    requested = set(args.only)
    assert not requested.difference(SAFE + BUG + GUARDED), requested
    for name in SAFE + BUG + GUARDED:
        if requested and name not in requested:
            continue
        folder = args.evidence / name
        folder.mkdir()
        row_source = folder / source.name
        row_source.write_bytes(source.read_bytes())
        summary_path = folder / "proof-summary.json"
        env = dict(os.environ)
        env["TRUST_MC_CHC_ROW_EXPORT_DIR"] = str(folder / "queries")
        cmd = [str(driver), "--ay-chc", "--verbose", "-Z", "unstable-options", "--harness-timeout=30s",
               "--harness", name, "--exact", "--proof-summary-json", str(summary_path), str(row_source)]
        (folder / "command.json").write_text(json.dumps(cmd, indent=2) + "\n")
        run = subprocess.run(cmd, env=env, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, cwd=folder, timeout=300)
        (folder / "run.log").write_text(run.stdout)
        row = {"harness": name, "exit": run.returncode, "log_sha256": sha(folder / "run.log")}
        errors = []
        manifests = list((folder / "queries").glob("*/manifest.json"))
        exported = None
        if len(manifests) == 1:
            exported = json.loads(manifests[0].read_text())
            smt_source = manifests[0].parent / exported["source"]["file"]
            if sha(smt_source) != exported["source"]["sha256"]:
                errors.append("exported query digest mismatch")
            row["query_manifest_sha256"] = sha(manifests[0])
        elif name not in GUARDED:
            errors.append("missing unique query export")
        if not summary_path.is_file():
            errors.append("missing machine-readable result")
        else:
            artifact = json.loads(summary_path.read_text())
            harnesses = artifact["harnesses"]
            if len(harnesses) != 1:
                errors.append("not exactly one executed harness")
            else:
                result = harnesses[0]
                row["result"] = result
                counts = result["property_counts"]
                if counts["total"] == 0:
                    errors.append("no program checks")
                if name in SAFE:
                    if run.returncode != 0 or not result["effective_success"]:
                        errors.append("safe probe did not succeed")
                    if result["validation_status"] != "validated" or result["proof_qualifiers"] != []:
                        errors.append("safe probe lacks clean validated grade")
                    if counts["failed"] or counts["undetermined"] or counts["unknown"]:
                        errors.append("undecided/failed program checks")
                elif name in BUG:
                    if run.returncode == 0 or result["effective_success"]:
                        errors.append("bug probe succeeded")
                    if result["validation_status"] != "validated":
                        errors.append("bug counterexample was not validated")
                    proof_rows = [] if exported is None else exported.get("rows", [])
                    certified = any(
                        r.get("outcome", {}).get("outcome") == "refuted"
                        and r["outcome"].get("ay_transcript_metadata", {}).get("accepted_as_proof") is True
                        and r["outcome"]["ay_transcript_metadata"].get("proof_status") == "verified-counterexample"
                        and r.get("prepared_matches_reparse") is True
                        for r in proof_rows
                    )
                    exact_witness = exported is not None and str(exported.get("acyclic_witness_outcome", "")).startswith("witness:")
                    if not certified and not exact_witness:
                        errors.append("no strict counterexample or exact replayed witness in query export")
                    if "[AY:CTREX_CAT:Genuine]" not in run.stdout:
                        errors.append("bug lacks a certified Genuine counterexample")
                    failed = result.get("failed_checks", [])
                    if not failed:
                        errors.append("no identified failed program check")
                    # OOB intentionally fails the program's indexing check;
                    # all other controls must reach a user assertion.
                    classes = re.findall(r"^Check \d+: \S+\.assertion\.\d+\s*\n\s*- Status: FAILURE", run.stdout, re.M)
                    if name != "oob_bug" and (not classes or not any(f["description"].strip('"') == BUG_ASSERTIONS[name] for f in failed)):
                        errors.append("failure not attributed to a program assertion")
                    if name == "oob_bug" and not any("bound" in f["description"].lower() or "index" in f["description"].lower() for f in failed):
                        errors.append("OOB control lost its bounds failure")
                elif result["effective_success"] and result["proof_qualifiers"] == []:
                    errors.append("unsupported producer became a clean proof")
        row["errors"] = errors
        report["rows"].append(row)
        (args.evidence / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(name, "PASS" if not errors else "FAIL: " + "; ".join(errors), flush=True)
    return int(any(row["errors"] for row in report["rows"]))


if __name__ == "__main__":
    raise SystemExit(main())
