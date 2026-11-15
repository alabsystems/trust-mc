# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""spec/kani/overlay.toml: the only hand-edited input of the spec.

Every correction names a rule and a per-rev blast radius. Rule-based
entries are recomputed from the generated units and oracles; generation
refuses when the computed set differs from the committed one, so a
correction can never silently grow or shrink when Kani moves. The rules
port the verdict heuristics hard-coded in
tools/kani-domination/src/discover.rs (and quarantine.rs, which discover.rs
applies) so the Rust runner can be retired onto the spec.
"""
from __future__ import annotations

import re
import tomllib
from pathlib import Path

from . import SpecError

SCHEMA = "trust-mc.kani-spec.overlay/v1"
VERDICT_MODES = ("expected", "cargo-kani", "cargo-kani-test")
KINDS = ("oracle", "invocation", "corpus-invalid", "retired")


# ---------------------------------------------------------------- discover.rs port
def legacy_expected_verdict(content: str):
    """discover.rs expected_file_verdict -> (verdict, deciding rule)."""
    if "VERIFICATION:- FAILED" in content:
        return "FAILED", "verification-failed-line"
    if "VERIFICATION:- SUCCESSFUL" in content or "VERIFICATION SUCCESSFUL" in content:
        return "SUCCESSFUL", "verification-successful-line"
    if "one or more unwinding failures" in content:
        return "FAILED", "unwinding-banner"
    if "memcpy src/dst overlap" in content:
        return "FAILED", "memcpy-overlap"
    for line in content.splitlines():
        t = line.strip()
        if t.startswith("Complete -"):
            for seg in t[len("Complete -"):].split(","):
                seg = seg.strip()
                for suffix in ("failures", "failure"):
                    if seg.endswith(suffix):
                        num = seg[:-len(suffix)].strip()
                        if num.isdigit():
                            return ("SUCCESSFUL" if int(num) == 0 else "FAILED"), "complete-summary"
    marker = None
    for line in content.splitlines():
        t = line.strip()
        if t in ("FAILURE", "FAILURE\\", "UNDETERMINED", "UNDETERMINED\\"):
            marker = marker or "exact-status-token"
        elif "Status: FAILURE" in t:
            marker = marker or "status-failure"
        elif t.startswith("Failed Checks:"):
            marker = marker or "failed-checks"
        elif t.startswith("Verification failed for"):
            marker = marker or "verification-failed-for"
        elif t.rstrip("\\").rstrip().endswith(": FAILURE"):
            marker = marker or "old-format-colon-failure"
    if marker:
        return "FAILED", marker
    saw = False
    for line in content.splitlines():
        t = line.strip()
        if t.startswith("**"):
            rest = t[2:].lstrip()
            if " of " in rest:
                n, tail = rest.split(" of ", 1)
                if "failed" in tail and n.strip().isdigit():
                    saw = True
                    if int(n.strip()) > 0:
                        return "FAILED", "n-of-m-failed"
    if saw:
        return "SUCCESSFUL", "n-of-m-failed"
    return None, None


def legacy_is_compile_error(content: str) -> bool:
    return "error: aborting due to" in content or "error[E" in content


def legacy_header_expects_fail(src: str) -> bool:
    for line in src.split("\n")[:80]:
        body = line.lstrip("/ ").strip()
        if body.startswith("kani-expect-fail"):
            return True
    return False


def legacy_prose_c_lib(src: str, test_path: str, tree, directives) -> list:
    flags = directives["kani_flags"]
    if "--c-lib" in flags:
        return []
    d = test_path.rsplit("/", 1)[0]
    for line in src.split("\n"):
        t = line.lstrip()
        if t.startswith("//!"):
            body = t[3:].strip()
        elif t.startswith("//"):
            body = t[2:].strip()
        else:
            continue
        if not body.startswith("kani ") or " -- " not in body:
            continue
        for tok in body.split(" -- ", 1)[1].split():
            if tok.endswith(".c") and tree.is_file(f"{d}/{tok}"):
                extra = [] if "c-ffi" in flags else ["-Z", "c-ffi"]
                return extra + ["--c-lib", f"{d}/{tok}"]
    return []


# ---------------------------------------------------------------- rules
def _is_proof_entry(src: str) -> bool:
    return "#[kani::proof" in src or "kani::proof]" in src or "#[proof]" in src


def compute_rule(rule: str, ctx) -> dict:
    """Return {unit_id: effect} for a rule over one rev's generated rows."""
    hits = {}
    prefix = "legacy-verdict:"
    if rule.startswith(prefix):
        want = rule[len(prefix):]
        for uid, (unit, private, oracle) in ctx["rows"].items():
            if unit["mode"] not in VERDICT_MODES or private.get("expected") is None:
                continue
            verdict, deciding = legacy_expected_verdict(private["expected"])
            if want == "compile-error-text":
                if (verdict is None and unit["unit_kind"] == "rs-file"
                        and legacy_is_compile_error(private["expected"])):
                    hits[uid] = {"stage": "check", "run_verdict": None}
            elif deciding == want:
                hits[uid] = {"run_verdict": verdict}
        return hits
    if rule == "legacy-directive:kani-expect-fail":
        for uid, (unit, private, oracle) in ctx["rows"].items():
            if unit["unit_kind"] == "rs-file" and legacy_header_expects_fail(private.get("root_src") or ""):
                hits[uid] = {"run_verdict": "FAILED"}
        return hits
    if rule == "legacy-invocation:prose-c-lib":
        for uid, (unit, private, oracle) in ctx["rows"].items():
            if unit["unit_kind"] != "rs-file":
                continue
            extra = legacy_prose_c_lib(private.get("root_src") or "", unit["path"], ctx["tree"], unit["directives"])
            if extra:
                hits[uid] = {"extra_kani_flags": extra}
        return hits
    if rule == "retired:sole-entry-dir-expected":
        per_dir = {}
        for uid, (unit, private, oracle) in ctx["rows"].items():
            if unit["unit_kind"] == "rs-file" and _is_proof_entry(private.get("root_src") or ""):
                d = unit["path"].rsplit("/", 1)[0]
                per_dir[(unit["suite"], d)] = per_dir.get((unit["suite"], d), 0) + 1
        for uid, (unit, private, oracle) in ctx["rows"].items():
            exp = unit.get("expected_path")
            if unit["mode"] != "expected" or not exp or not exp.endswith("/expected"):
                continue
            d = unit["path"].rsplit("/", 1)[0]
            if exp == f"{d}/expected" and per_dir.get((unit["suite"], d), 0) != 1:
                hits[uid] = {"note": "upstream applies the directory expected file; discover.rs gave this unit none"}
        return hits
    raise SpecError(f"overlay: unknown rule {rule!r}")


# ---------------------------------------------------------------- load / apply
def load_overlay(path: Path) -> dict:
    data = tomllib.loads(Path(path).read_text(encoding="utf-8"))
    if data.get("schema") != SCHEMA:
        raise SpecError(f"{path}: schema must be {SCHEMA!r}")
    ids = set()
    for entry in data.get("correction", []):
        for key in ("id", "kind", "source", "audit", "blast_radius"):
            if key not in entry:
                raise SpecError(f"{path}: correction {entry.get('id')!r} lacks {key!r}")
        if entry["id"] in ids:
            raise SpecError(f"{path}: duplicate correction id {entry['id']}")
        ids.add(entry["id"])
        if entry["kind"] not in KINDS:
            raise SpecError(f"{path}: {entry['id']}: kind must be one of {KINDS}")
        if "rule" not in entry and "effect" not in entry:
            raise SpecError(f"{path}: {entry['id']}: explicit entries need an effect")
    for ex in data.get("exemption", []):
        for key in ("unit", "rev", "class", "reason", "signed_by", "signed_on"):
            if key not in ex:
                raise SpecError(f"{path}: exemption lacks {key!r}")
    return data


def apply_overlay(overlay: dict, rev: str, ctx) -> list:
    """Validate blast radii for `rev` and annotate rows in place.

    Returns a list of {id, kind, rule, count} for the manifest.
    """
    rows = ctx["rows"]
    applied = []
    problems = []
    for entry in overlay.get("correction", []):
        committed = entry["blast_radius"].get(rev)
        if committed is None:
            continue
        committed = list(committed)
        if committed != sorted(set(committed)):
            problems.append(f"{entry['id']}: blast_radius[{rev[:12]}] must be sorted and unique")
        if "rule" in entry:
            computed = compute_rule(entry["rule"], ctx)
        else:
            computed = {uid: dict(entry["effect"]) for uid in committed if uid in rows}
            missing = sorted(set(committed) - set(rows))
            if missing:
                problems.append(f"{entry['id']}: units absent at {rev[:12]}: {missing}")
        if sorted(computed) != sorted(set(committed)):
            added = sorted(set(computed) - set(committed))
            removed = sorted(set(committed) - set(computed))
            problems.append(f"{entry['id']} ({entry.get('rule', 'explicit')}) blast radius at {rev[:12]} changed: "
                            f"+{added} -{removed}")
            continue
        for uid in sorted(computed):
            effect = dict(computed[uid])
            if "effect" in entry:
                effect.update(entry["effect"])
            unit, private, oracle = rows[uid]
            note = {"id": entry["id"], "kind": entry["kind"], "effect": {k: effect[k] for k in sorted(effect)}}
            if entry["kind"] == "oracle":
                native = (oracle.get("run_verdict") or {}).get("verdict")
                wanted = effect.get("run_verdict")
                if "stage" in effect:
                    note["relation"] = "stage" if oracle.get("stage") != effect["stage"] else "agrees"
                elif wanted is None:
                    note["relation"] = "none"
                elif native is None:
                    note["relation"] = "fills"
                elif native == wanted:
                    note["relation"] = "agrees"
                elif unit["ignored"]:
                    # Upstream never runs an ignored unit, so its derived verdict is
                    # only the directive default; an audited correction may override it.
                    note["relation"] = "overrides-ignored-unit"
                else:
                    note["relation"] = "conflicts"
                    problems.append(f"{entry['id']}: {uid} derives {native} but the correction says {wanted}")
                oracle.setdefault("overlay", []).append(note)
            elif entry["kind"] == "corpus-invalid":
                note["evidence"] = entry["audit"]
                oracle.setdefault("overlay", []).append(note)
            elif entry["kind"] == "invocation":
                unit.setdefault("overlay", []).append(note)
            else:
                unit.setdefault("overlay", []).append(note)
        applied.append({"id": entry["id"], "kind": entry["kind"], "rule": entry.get("rule"),
                        "units": len(computed)})
    for ex in overlay.get("exemption", []):
        if ex["rev"] != rev:
            continue
        if ex["unit"] not in rows:
            problems.append(f"exemption for absent unit {ex['unit']} at {rev[:12]}")
            continue
        unit, private, oracle = rows[ex["unit"]]
        unit.setdefault("exemptions", []).append({k: ex[k] for k in sorted(ex)})
    if problems:
        raise SpecError("overlay.toml does not match the generated spec:\n  " + "\n  ".join(problems))
    return applied


def effective_oracle_fields(oracle: dict) -> dict:
    """What a scorer reads: upstream-derived fields with oracle overlays applied."""
    run = oracle.get("run_verdict")
    stage = oracle.get("stage")
    basis = run["basis"] if run else None
    verdict = run["verdict"] if run else None
    # `complete`: the verdict covers the whole run. A SUCCESSFUL stated for one of
    # several harnesses is not a whole-run SUCCESSFUL, and a scorer must not read it as one.
    complete = run.get("complete") if run else None
    # Upstream never runs an ignored unit, so any verdict here is what its directives or
    # expected file state, not an observed outcome.
    ignored = bool(oracle.get("ignored"))
    for note in oracle.get("overlay", []):
        eff = note["effect"]
        if note["kind"] == "corpus-invalid":
            return {"stage": stage, "run_verdict": None, "basis": f"overlay:{note['id']}", "complete": None,
                    "corpus_invalid": True, "upstream_ignored": ignored}
        if "stage" in eff:
            stage = eff["stage"]
            verdict, basis, complete = None, f"overlay:{note['id']}", None
        elif eff.get("run_verdict") and (verdict is None or note.get("relation") == "overrides-ignored-unit"):
            verdict, basis = eff["run_verdict"], f"overlay:{note['id']}"
            # A failure marker fails the run; the legacy SUCCESSFUL rules read one summary only.
            complete = verdict == "FAILED"
    return {"stage": stage, "run_verdict": verdict, "basis": basis, "complete": complete,
            "corpus_invalid": False, "upstream_ignored": ignored}


RE_ID = re.compile(r"^[a-z0-9][a-z0-9-]*$")
