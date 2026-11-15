#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Focused accounting checks; run via build-slot on a supplied exact-source bundle."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

ROWS = [
    ("address_accounting.rs", "p05_signed_rmw_safe", "exact_safe"),
    ("address_accounting.rs", "p05_signed_rmw_bug", "exact_bug"),
    ("address_accounting.rs", "mixed_exact_opaque_safe", "tainted"),
    ("address_accounting.rs", "mixed_exact_opaque_bug", "tainted_bug"),
    ("address_accounting.rs", "nested_caller_safe", "tainted"),
    ("address_accounting.rs", "nested_caller_bug", "tainted_bug"),
    ("address_accounting.rs", "genuinely_unstubbed_safe", "tainted"),
    ("address_accounting.rs", "genuinely_unstubbed_bug", "tainted_bug"),
    ("address_accounting_projected.rs", "projected_return_safe", "guarded"),
    ("address_accounting_projected.rs", "projected_return_wrong_root", "guarded_bug"),
    ("address_accounting_fake_core.rs", "fake_core_safe", "exact_safe"),
    ("address_accounting_fake_core.rs", "fake_core_wrong_address", "exact_bug"),
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect(folder, name, expectation, output):
    problems = []
    summary = json.loads((folder / "proof-summary.json").read_text())
    harnesses = summary["harnesses"]
    selected = [h for h in harnesses if h.get("harness", "").split("::")[-1] == name]
    # Older summaries call this field `name`.
    if not selected:
        selected = [h for h in harnesses if h.get("name", "").split("::")[-1] == name]
    if len(selected) != 1:
        return {"issues": ["missing unique harness"], "summary": summary}
    result = selected[0]
    metadata = list(folder.glob("*.kani-metadata.json"))
    if len(metadata) != 1:
        return {"issues": ["missing unique retained compiler metadata"], "result": result}
    md = json.loads(metadata[0].read_text())
    info = md.get("unstubbed_abstractions")
    total = 0 if info is None else info["count"]
    per = {} if info is None else info.get("per_harness", {})
    count = sum(v for k, v in per.items() if k.split("::")[-1] == name) if per else total
    genuine = "[AY:CTREX_CAT:Genuine]" in output
    counts = result["property_counts"]
    clean = result["effective_success"] and result["validation_status"] == "validated" and not result["proof_qualifiers"]
    if counts["total"] == 0:
        problems.append("zero program checks")
    if expectation.startswith("exact") and count != 0:
        problems.append("exact lane retains unresolved abstraction")
    if expectation == "exact_safe" and (not clean or counts["failed"] or counts["unknown"] or counts["undetermined"]):
        problems.append("safe lane lacks complete validated success")
    if expectation == "exact_bug" and (not genuine or result["validation_status"] != "validated" or not counts["failed"]):
        problems.append("bug lane lacks validated Genuine failure")
    if expectation.startswith("tainted") and count == 0:
        problems.append("opaque/inlined/unstubbed lane lost abstraction taint")
    if expectation.startswith(("tainted", "guarded")) and genuine:
        problems.append("conservative lane certified a counterexample")
    if expectation.endswith("bug") and clean:
        problems.append("false clean proof")
    return {"result": result, "unstubbed_total": total, "unstubbed_per_harness": per,
            "resolved_count": count, "genuine": genuine, "issues": problems,
            "metadata_sha256": sha(metadata[0])}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--evidence", type=Path, required=True)
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args()
    args.evidence.mkdir(parents=True, exist_ok=False)
    report = {"driver_sha256": sha(args.bundle / "bin/trust-mc-driver"), "rows": []}
    for filename, name, expectation in ROWS:
        if args.only and name not in args.only:
            continue
        folder = args.evidence / name
        folder.mkdir()
        # The spoof must actually compile as crate `core`, matching its attribute.
        source = folder / ("core.rs" if filename == "address_accounting_fake_core.rs" else filename)
        source.write_bytes(Path(__file__).with_name(filename).read_bytes())
        cmd = [str(args.bundle / "bin/trust-mc-driver"), "--ay-chc", "--verbose", "-Z", "unstable-options",
               "--harness-timeout=30s", "--harness", name, "--exact", "--keep-temps",
               "--proof-summary-json", str(folder / "proof-summary.json"), str(source)]
        env = dict(os.environ)
        env["TRUST_MC_CHC_ROW_EXPORT_DIR"] = str(folder / "queries")
        (folder / "command.json").write_text(json.dumps(cmd, indent=2) + "\n")
        run = subprocess.run(cmd, cwd=folder, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=300)
        (folder / "run.log").write_text(run.stdout)
        row = {"harness": name, "expectation": expectation, "exit": run.returncode,
               "source_sha256": sha(source), "log_sha256": sha(folder / "run.log")}
        if (folder / "proof-summary.json").is_file():
            row.update(inspect(folder, name, expectation, run.stdout))
        else:
            row["issues"] = ["no machine result"]
        report["rows"].append(row)
        (args.evidence / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(name, row["issues"], flush=True)
    if not args.only:
        # Compile all eight harnesses in one compiler invocation. Per-harness
        # custody must not leak an opaque sibling's taint onto the exact models,
        # or clear the opaque models because another harness was exact.
        folder = args.evidence / "combined-harnesses"
        folder.mkdir()
        source = folder / "address_accounting.rs"
        source.write_bytes(Path(__file__).with_name(source.name).read_bytes())
        cmd = [str(args.bundle / "bin/trust-mc-driver"), "--ay-chc", "--verbose", "-Z", "unstable-options",
               "--harness-timeout=30s", "--keep-temps", "--proof-summary-json",
               str(folder / "proof-summary.json"), str(source)]
        env = dict(os.environ)
        env["TRUST_MC_CHC_ROW_EXPORT_DIR"] = str(folder / "queries")
        (folder / "command.json").write_text(json.dumps(cmd, indent=2) + "\n")
        run = subprocess.run(cmd, cwd=folder, env=env, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, text=True, timeout=600)
        (folder / "run.log").write_text(run.stdout)
        metadata = list(folder.glob("*.kani-metadata.json"))
        combined = {"exit": run.returncode, "issues": [], "source_sha256": sha(source),
                    "log_sha256": sha(folder / "run.log")}
        if len(metadata) != 1 or not (folder / "proof-summary.json").is_file():
            combined["issues"].append("combined invocation omitted metadata or results")
        else:
            md = json.loads(metadata[0].read_text())
            info = md.get("unstubbed_abstractions") or {}
            counts = info.get("per_harness", {})
            combined["unstubbed_per_harness"] = counts
            summary = json.loads((folder / "proof-summary.json").read_text())
            results = summary["harnesses"]
            for filename, name, expectation in ROWS:
                if filename != source.name:
                    continue
                count = sum(v for k, v in counts.items() if k.split("::")[-1] == name)
                found = [r for r in results if r.get("harness", r.get("name", "")).split("::")[-1] == name]
                if len(found) != 1 or found[0]["property_counts"]["total"] == 0:
                    combined["issues"].append(name + ": no unique nonempty result")
                if expectation.startswith("exact") and count:
                    combined["issues"].append(name + ": inherited sibling taint")
                if expectation.startswith("tainted") and not count:
                    combined["issues"].append(name + ": lost own taint")
            combined["metadata_sha256"] = sha(metadata[0])
        report["combined"] = combined
        (args.evidence / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        print("combined-harnesses", combined["issues"], flush=True)
    return int(any(row["issues"] for row in report["rows"]) or bool(report.get("combined", {}).get("issues")))


if __name__ == "__main__":
    raise SystemExit(main())
