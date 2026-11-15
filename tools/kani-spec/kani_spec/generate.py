# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Build spec/kani/<rev>/{manifest.json,clauses.json,units.jsonl,oracles.jsonl}."""
from __future__ import annotations

import hashlib
import json
import tomllib
from collections import Counter
from pathlib import Path

from . import GENERATOR_VERSION, SPEC_REVISION, SpecError
from .checkout import cache_root, verify_checkout
from .classify import CLAUSES, build_context, classify, clauses_for, tags_for
from .collect import build_unit, collect_paths, perf_overlays, suite_table
from .fsview import Tree
from .header import test_description
from .oracle import build_oracle
from .overlay import apply_overlay, compute_rule, effective_oracle_fields

CI_STEPS = (
    ("ci/firecracker-codegen", "scripts/kani-regression.sh", "codegen-firecracker.sh",
     "codegen of the firecracker submodule (Linux x86_64)", "codegen_only_build", "cbmc-specific",
     "goto codegen of the Firecracker tree; no verdict"),
    ("ci/manifest-path", "scripts/kani-regression.sh", "--manifest-path",
     "cargo kani --manifest-path tests/cargo-kani/cargo-features-flag/Cargo.toml --harness trivial_success",
     "cargo_workflow", "cli-surface", "cargo kani --manifest-path front-door behaviour"),
    ("ci/crate-unit-tests", "scripts/kani-regression.sh", "cargo test -p kani_macros",
     "cargo test of cprover_bindings, kani-compiler, kani-driver, kani_metadata, kani (concrete_playback), kani_macros",
     "harness.attribute", "cli-surface",
     "implementation unit tests; only kani_macros expansion tests carry harness-language meaning"),
    ("ci/verify-std", ".github/workflows/verify-std-check.yml", "verify-std",
     "kani verify-std against model-checking/verify-rust-std", "std_verification", "toolchain-dependent",
     "external repo; std source of the pinned nightly; oracle is HEAD not worse than BASE"),
    ("ci/benchcomp-e2e", ".github/workflows/bench-e2e.yml", "benchcomp",
     "benchcomp wall-clock comparison over tests/perf", "timeouts_limits", "cli-surface",
     "wall-clock benchmark, not a verdict"),
    ("ci/benchcomp-tests", ".github/workflows/kani.yml", "test/run",
     "tools/benchcomp python tests", "output_formats", "cli-surface", "tooling tests"),
    ("ci/perf-ignored", ".github/workflows/cbmc-latest.yml", "--ignored",
     "compiletest --suite perf --mode cargo-kani-test ignore --ignored against CBMC develop", "timeouts_limits",
     "fixme", "runs the ignored perf tests only"),
)


def dumps_line(obj) -> str:
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, separators=(",", ":"))


def dumps_doc(obj) -> str:
    return json.dumps(obj, sort_keys=True, ensure_ascii=False, indent=2) + "\n"


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def build_rows(tree: Tree, overlay: dict | None = None, rev: str | None = None):
    table = suite_table(tree)
    rows = {}
    suites = []
    for entry in table:
        suite, mode = entry["suite"], entry["mode"]
        t = tree.with_overlays(perf_overlays(tree, suite)) if entry["perf_overlays"] else tree
        paths, error = collect_paths(t, suite, mode)
        excluded, ids = Counter(), []
        for p in paths:
            if mode == "kani-fixme" and test_description(p, mode, {})["ignore"]:
                excluded[test_description(p, mode, {})["ignore_message"]] += 1
                continue
            unit, private = build_unit(t, suite, mode, p)
            if unit["unit_kind"] == "rs-file":
                private["root_src"] = t.read_text(p)
                d = p.rsplit("/", 1)[0]
                private["sibling_c"] = any(n.endswith(".c") for n in t.listdir(d))
            oracle = build_oracle(unit, private["expected"])
            if unit["id"] in rows:
                raise SpecError(f"duplicate unit id {unit['id']}")
            rows[unit["id"]] = (unit, private, oracle)
            ids.append(unit["id"])
        suites.append({**entry, "upstream_collected": len(paths), "unit_ids": ids,
                       "excluded_from_units": dict(sorted(excluded.items())), "collection_error": error})
    applied = apply_overlay(overlay, rev, {"rows": rows, "tree": tree}) if overlay is not None else []
    for uid in sorted(rows):
        unit, private, oracle = rows[uid]
        oracle["effective"] = effective_oracle_fields(oracle)
        ctx = build_context(unit, private, oracle)
        unit["clauses"] = clauses_for(ctx)
        unit["classification"], unit["classification_reason"] = classify(ctx)
        unit["tags"] = tags_for(ctx)
        oracle["classification"] = unit["classification"]
    return table, suites, rows, applied


def _count_summary(ids, rows):
    cls, kinds, ignored = Counter(), Counter(), Counter()
    harnesses = pfc = expected = templates = inactive = 0
    for uid in ids:
        unit, _, oracle = rows[uid]
        cls[unit["classification"]] += 1
        for k in oracle["oracle_kinds"]:
            kinds[k] += 1
        if unit["ignored"]:
            ignored[unit["ignored"]] += 1
        templates += sum(1 for h in unit["harnesses"] if h["macro_template"])
        inactive += sum(1 for h in unit["harnesses"] if h.get("cfg_active") is False)
        real = [h for h in unit["harnesses"]
                if not h["macro_template"] and h.get("selected") is not False and h.get("cfg_active") is not False]
        harnesses += len(real)
        pfc += sum(1 for h in real if h["kind"] == "proof_for_contract")
        expected += 1 if unit.get("expected_path") else 0
    return {"units": len(ids), "classification": dict(sorted(cls.items())),
            "oracle_kinds": dict(sorted(kinds.items())), "ignored_units": dict(sorted(ignored.items())),
            "harnesses": harnesses, "harness_macro_templates": templates, "harnesses_cfg_inactive": inactive,
            "proof_for_contract": pfc, "expected_files": expected}


def generate_rev(pin, overlay: dict, overlay_bytes: bytes, checkout: Path | None = None) -> dict:
    path = Path(checkout) if checkout else cache_root() / pin.rev
    info = verify_checkout(path, pin)
    tree = Tree(path)
    table, suites, rows, applied = build_rows(tree, overlay, pin.rev)

    unit_lines = [dumps_line(rows[uid][0]) for uid in sorted(rows)]
    oracle_lines = [dumps_line(rows[uid][2]) for uid in sorted(rows)]
    units_bytes = ("\n".join(unit_lines) + "\n").encode()
    oracles_bytes = ("\n".join(oracle_lines) + "\n").encode()

    clause_rows = []
    for cid in sorted(CLAUSES):
        desc, rules = CLAUSES[cid]
        n = sum(1 for u, _, _ in rows.values() if cid in u["clauses"])
        nv = sum(1 for u, _, _ in rows.values() if cid in u["clauses"] and u["classification"] == "verdict-spec")
        clause_rows.append({"id": cid, "description": desc,
                            "rules": [{"target": t, "pattern": p} for t, p in rules],
                            "units": n, "verdict_spec_units": nv})
    clauses_bytes = dumps_doc({"schema": "trust-mc.kani-spec.clauses/v1", "kani_rev": pin.rev,
                               "clauses": clause_rows}).encode()

    ci_steps = []
    for sid, source, anchor, what, clause, cls, reason in CI_STEPS:
        if not tree.is_file(source) or anchor not in tree.read_text(source):
            raise SpecError(f"CI step {sid}: anchor {anchor!r} not found in {source}; triage the CI surface")
        ci_steps.append({"id": sid, "source": source, "source_sha256": tree.sha256(source), "anchor": anchor,
                         "what": what, "clause": clause, "classification": cls, "reason": reason})

    suite_rows = []
    for s in suites:
        summary = _count_summary(s["unit_ids"], rows)
        suite_rows.append({"suite": s["suite"], "mode": s["mode"], "sources": s["sources"],
                           "ci_jobs": s["ci_jobs"], "perf_overlays": s["perf_overlays"],
                           "upstream_collected": s["upstream_collected"],
                           "excluded_from_units": s["excluded_from_units"],
                           "collection_error": s["collection_error"], **summary})
    totals = _count_summary(sorted(rows), rows)
    totals["upstream_collected"] = sum(s["upstream_collected"] for s in suites)
    kani_version = None
    try:
        root_manifest = tomllib.loads(tree.read_text("Cargo.toml"))
        kani_version = (root_manifest.get("package") or {}).get("version") or \
            ((root_manifest.get("workspace") or {}).get("package") or {}).get("version")
    except (tomllib.TOMLDecodeError, OSError):
        pass
    manifest = {
        "schema": "trust-mc.kani-spec.manifest/v1",
        "generator_version": GENERATOR_VERSION,
        "spec_version": f"kani@{pin.rev}+spec.{SPEC_REVISION}",
        "kani_rev": pin.rev,
        "kani_nightly": info["nightly"],
        "kani_version": kani_version,
        "pin_name": pin.name,
        "submodules": dict(pin.submodules),
        "collection": {
            "rs_modes": "every *.rs not starting with . # ~, recursing except auxiliary/",
            "cargo_modes": "each `expected` or `*.expected` entry of a directory holding Cargo.toml",
            "exec_mode": "each entry directly under the suite directory (config.yml required)",
            "ignore_rule": "path containing fixme, else ignore, is collected but ignored (unit kept, class fixme)",
            "kani_fixme": "only basenames containing fixme are units; regular and ignore basenames are counted in excluded_from_units",
            "perf_overlays": "tests/perf/overlays/<d>/* shadow tests/perf/<d>/ as scripts/kani-perf.sh copies them",
            "submodules": "test-bearing submodules are checked out at their gitlink as Kani CI does",
        },
        "suites": suite_rows,
        "totals": totals,
        "ci_steps": ci_steps,
        "overlay": {"path": "spec/kani/overlay.toml", "sha256": sha256_bytes(overlay_bytes), "applied": applied},
        "files": {
            "clauses.json": sha256_bytes(clauses_bytes),
            "oracles.jsonl": sha256_bytes(oracles_bytes),
            "units.jsonl": sha256_bytes(units_bytes),
        },
    }
    return {
        "manifest.json": dumps_doc(manifest).encode(),
        "clauses.json": clauses_bytes,
        "units.jsonl": units_bytes,
        "oracles.jsonl": oracles_bytes,
    }


def compute_radii(pin, overlay: dict, checkout: Path | None = None) -> dict:
    path = Path(checkout) if checkout else cache_root() / pin.rev
    verify_checkout(path, pin)
    tree = Tree(path)
    _, _, rows, _ = build_rows(tree)
    ctx = {"rows": rows, "tree": tree}
    out = {}
    for entry in overlay.get("correction", []):
        if "rule" in entry:
            out[entry["id"]] = sorted(compute_rule(entry["rule"], ctx))
        else:
            out[entry["id"]] = sorted(u for u in entry["blast_radius"].get(pin.rev, []) if u in rows)
    return out
