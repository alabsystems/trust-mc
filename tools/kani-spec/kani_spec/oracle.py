# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Structured oracles from Kani expected files and compiletest directives.

An expected file is a set of `contains_lines` blocks (runtest.rs
`verify_output`): every block must appear, as consecutive output lines each
containing the trimmed expected line, somewhere in stdout+stderr. Blocks do
not bind to each other, so everything below is what the file *states*; the
`basis` fields say how each verdict was derived and whether it covers every
selected harness.
"""
from __future__ import annotations

import re

STATUS = ("SUCCESS", "FAILURE", "UNDETERMINED", "UNREACHABLE", "SATISFIED", "UNSATISFIABLE")
COVER_ONLY = ("SATISFIED", "UNSATISFIABLE")
_TOK = "|".join(STATUS)
RE_CHECK = re.compile(r"^Check (\d+): ?(.*)$")
RE_STATUS = re.compile(rf"^(?:- )?Status: ({_TOK})\b\s*(.*)$")
RE_BARE = re.compile(rf"^({_TOK})$")
RE_DESC = re.compile(r"^(?:- )?Description: ?(.*)$")
RE_LOC = re.compile(r"^(?:- )?Location: ?(.*)$")
RE_LOC_INLINE = re.compile(r"^(?:\S+:\d+:\d+ )?in function \S.*$|^\S+\.rs:\d+:\d+(?: in function .*)?$")
RE_OLD = re.compile(rf"^(?:\[(?P<name>[^\]]+)\] )?(?:line \d+ )?(?P<desc>.+?): (?P<status>{_TOK})$")
RE_HARNESS = re.compile(r"^Checking harness (.+?)\.\.\.$")
RE_VERIF = re.compile(r"^VERIFICATION(?::-| ) ?(SUCCESSFUL|FAILED)(?: \((.*)\))?\s*$")
RE_FAILED_FOR = re.compile(r"^Verification failed for - (.+?)\s*$")
RE_COMPLETE = re.compile(r"^Complete - (\d+) successfully verified (harnesses|functions), (\d+) failures?, (\d+) total\.?\s*$")
RE_CHECK_SUM = re.compile(r"^\*\* (\d+) of (\d+) failed(?: \((.*)\))?\s*$")
RE_COVER_SUM = re.compile(r"^\*\* (\d+) of (\d+) cover properties satisfied(?: \((.*)\))?\s*$")
RE_PARTIAL_SUM = re.compile(r"^\*\*\s*\d*(?: of)?.*$")
RE_FAILED_CHECKS = re.compile(r"^Failed Checks: ?(.*)$")
RE_DIAG = re.compile(r"^(error|warning)(?:\[(E\d{4})\])?: ?(.*)$")
RE_PROP = re.compile(r"^(?P<func>.*)\.(?P<cls>[A-Za-z_][A-Za-z0-9_]*)\.(?P<idx>\d*)$")
UNWIND_BANNER = "Verification output shows one or more unwinding failures"


def contains_blocks(text: str):
    """runtest.rs contains_lines grouping. Returns (blocks, trivial_count).

    Each block is the list of trimmed expected lines; a block whose lines are
    all empty matches any output with enough lines and is counted, not kept.
    """
    blocks, cur = [], []
    for line in text.split("\n"):
        if line.endswith("\\"):
            cur.append(line[:-1])
        else:
            cur.append(line)
            blocks.append(cur)
            cur = []
    if cur:
        blocks.append(cur)
    kept, trivial = [], 0
    for b in blocks:
        trimmed = [x.strip() for x in b]
        if all(t == "" for t in trimmed):
            trivial += 1
        else:
            kept.append(trimmed)
    return kept, trivial


def _unquote(s: str) -> str:
    s = s.strip()
    if len(s) >= 2 and s.startswith('"') and s.endswith('"'):
        return s[1:-1]
    return s


def _property_class(name: str | None, status: str | None, description: str | None):
    if name:
        m = RE_PROP.match(name.strip())
        if m:
            return m.group("cls"), name.strip()
    if status in COVER_ONLY:
        return "cover", name
    if description and description.startswith("cover condition"):
        return "cover", name
    return None, name


def _others(text: str | None) -> dict:
    out = {}
    for part in (text or "").split(","):
        m = re.match(r"\s*(\d+) (\w+)", part)
        if m:
            out[m.group(2)] = int(m.group(1))
    return out


def parse_expected(text: str) -> dict:
    blocks, trivial = contains_blocks(text)
    records, harness_lines, run_lines, failed_for = [], [], [], []
    completes, check_sums, cover_sums, partial_sums, failed_checks, diags = [], [], [], [], [], []
    banner = UNWIND_BANNER in text
    current_harness = None
    open_rec = None

    def new_record(block, **kw):
        rec = {"check_id": None, "property_name": None, "status": None, "description": None,
               "location": None, "harness": current_harness, "block": block}
        rec.update(kw)
        records.append(rec)
        return rec

    for bi, block in enumerate(blocks):
        for li, line in enumerate(block):
            if line == "":
                open_rec = None
                continue
            m = RE_HARNESS.match(line)
            if m:
                current_harness = m.group(1)
                harness_lines.append(current_harness)
                open_rec = None
                continue
            m = RE_VERIF.match(line)
            if m:
                run_lines.append({"harness": current_harness, "verdict": m.group(1),
                                  "qualifier": m.group(2)})
                open_rec = None
                continue
            m = RE_FAILED_FOR.match(line)
            if m:
                failed_for.append(m.group(1))
                open_rec = None
                continue
            m = RE_COMPLETE.match(line)
            if m:
                completes.append({"succeeded": int(m.group(1)), "unit": m.group(2),
                                  "failed": int(m.group(3)), "total": int(m.group(4))})
                open_rec = None
                continue
            m = RE_COVER_SUM.match(line)
            if m:
                cover_sums.append({"satisfied": int(m.group(1)), "total": int(m.group(2)),
                                   "harness": current_harness, **_others(m.group(3))})
                open_rec = None
                continue
            m = RE_CHECK_SUM.match(line)
            if m:
                check_sums.append({"failed": int(m.group(1)), "total": int(m.group(2)),
                                   "harness": current_harness, **_others(m.group(3))})
                open_rec = None
                continue
            if line.startswith("**") and RE_PARTIAL_SUM.match(line):
                partial_sums.append(line)
                open_rec = None
                continue
            m = RE_FAILED_CHECKS.match(line)
            if m:
                failed_checks.append({"description": m.group(1), "harness": current_harness})
                open_rec = None
                continue
            m = RE_DIAG.match(line)
            if m:
                diags.append({"level": m.group(1), "code": m.group(2), "message": m.group(3)})
                open_rec = None
                continue
            m = RE_CHECK.match(line)
            if m:
                open_rec = new_record(bi, check_id=int(m.group(1)), property_name=m.group(2) or None)
                continue
            if (li + 1 < len(block) and RE_PROP.match(line) and ": " not in line and '"' not in line
                    and (RE_STATUS.match(block[li + 1]) or RE_BARE.match(block[li + 1]))):
                # A property name without the `Check N:` prefix (loop-contract and
                # function-contract expected files): keep its property class.
                open_rec = new_record(bi, property_name=line)
                continue
            m = RE_STATUS.match(line) or RE_BARE.match(line)
            if m:
                if open_rec is not None and open_rec["status"] is None and open_rec["description"] is None:
                    open_rec["status"] = m.group(1)
                else:
                    open_rec = new_record(bi, status=m.group(1))
                continue
            m = RE_DESC.match(line)
            if m:
                if open_rec is not None and open_rec["description"] is None:
                    open_rec["description"] = _unquote(m.group(1))
                else:
                    open_rec = new_record(bi, description=_unquote(m.group(1)))
                continue
            m = RE_LOC.match(line)
            if m and open_rec is not None and open_rec["location"] is None:
                open_rec["location"] = m.group(1) or None
                continue
            if open_rec is not None and RE_LOC_INLINE.match(line):
                if open_rec["location"] in (None, ""):
                    open_rec["location"] = line
                continue
            m = RE_OLD.match(line)
            if m and not line.startswith(("[Kani]", "Status")):
                new_record(bi, property_name=m.group("name"), status=m.group("status"),
                           description=m.group("desc"), form="old-format")
                open_rec = None
                continue
            if open_rec is not None and open_rec["status"] is not None and open_rec["description"] is None \
                    and li > 0 and block[li - 1] in STATUS:
                # `SUCCESS\` followed by a bare description line (expected/vec).
                open_rec["description"] = line
                open_rec = None
                continue
            open_rec = None

    checks, covers = [], []
    for rec in records:
        cls, name = _property_class(rec["property_name"], rec["status"], rec["description"])
        row = {"property_class": cls, "property_name": name, "description": rec["description"],
               "status": rec["status"], "location": rec["location"], "harness": rec["harness"],
               "check_id": rec["check_id"], "block": rec["block"]}
        if rec.get("form"):
            row["form"] = rec["form"]
        (covers if cls == "cover" else checks).append(row)
    return {
        "contains_lines": blocks,
        "trivial_blocks": trivial,
        "checks": checks,
        "covers": covers,
        "harness_lines": harness_lines,
        "verification_lines": run_lines,
        "verification_failed_for": failed_for,
        "complete": completes,
        "check_summaries": check_sums,
        "cover_summaries": cover_sums,
        "partial_summaries": partial_sums,
        "failed_checks": failed_checks,
        "diagnostics": diags,
        "unwinding_failure_banner": banner,
    }


def _match_harness(stated: str, harnesses: list):
    exact = [h for h in harnesses if h["pretty_name"] == stated]
    if exact:
        return exact
    return [h for h in harnesses if h["pretty_name"].endswith("::" + stated) or h["name"] == stated]


def build_oracle(unit: dict, expected_text: str | None) -> dict:
    mode = unit["mode"]
    props = unit["directives"]
    step = props["kani_fail_step"]
    inverted = unit["should_fail"]
    selected = [h for h in unit["harnesses"]
                if h.get("selected") is not False and not h["macro_template"] and h.get("cfg_active") is not False]
    oracle = {
        "id": unit["id"], "suite": suite_of(unit), "mode": mode,
        "ignored": unit["ignored"], "inverted": inverted,
        "expected_path": unit.get("expected_path"),
        "expected_raw": expected_text,
    }
    kinds = []
    parsed = None
    if mode in ("kani", "kani-fixme", "stub-tests"):
        panics = bool(unit.get("directive_panics"))
        if panics:
            oracle["upstream_outcome"] = "props-parse-panic"
        stage = step or "verify"
        base_success = step is None
        expect_success = base_success != inverted
        oracle["stage"] = stage
        exit_kind = "unchecked" if panics else ("success" if expect_success else "failure")
        oracle["expected_exit"] = {"kind": exit_kind, "code": None,
                                   "stage_command": {"check": "kani-compiler -Z no-codegen",
                                                     "codegen": "kani-compiler --goto-c",
                                                     "verify": "kani"}[stage]}
        if panics:
            # TestProps::from_file panics (a kani-*-fail header outside Mode::Kani, or two
            # fail headers) before Kani runs; the should_panic test passes whatever the
            # program does, so upstream states no verdict, exit status or stage outcome.
            kinds.append("props-parse-panic")
            run = None
        elif step in ("check", "codegen"):
            kinds.append("exit-status")
            kinds.append("reject" if step == "check" else "codegen-fail")
            run = None
        elif expect_success:
            kinds.append("exit-status")
            run = {"verdict": "SUCCESSFUL", "basis": "exit-status-inverted" if inverted else "exit-status",
                   "complete": True}
        else:
            kinds.append("exit-status")
            run = {"verdict": "FAILED", "basis": "exit-status-inverted" if inverted else "exit-status",
                   "complete": len(selected) == 1}
        harness_rows = []
        for h in selected:
            verdict = None
            basis = None
            if run and run["verdict"] == "SUCCESSFUL":
                verdict, basis = "SUCCESSFUL", run["basis"]
            elif run and len(selected) == 1:
                verdict, basis = run["verdict"], run["basis"]
            harness_rows.append(_harness_row(h, verdict, basis))
        oracle.update({"run_verdict": run, "harnesses": harness_rows, "checks": [], "covers": [],
                       "summary": None, "diagnostics": [], "contains_lines": [], "trivial_blocks": 0})
    else:
        if mode == "exec":
            oracle["stage"] = "exec"
            oracle["expected_exit"] = {"kind": "code", "code": unit["exec"]["exit_code"], "stage_command": "time <script>"}
            kinds.append("exit-code")
        elif mode in ("coverage-based", "cargo-coverage"):
            oracle["stage"] = "coverage-report"
            oracle["expected_exit"] = {"kind": "unchecked", "code": None, "stage_command": "kani-cov report"}
        else:
            oracle["stage"] = "verify"
            oracle["expected_exit"] = {"kind": "unchecked", "code": None,
                                       "stage_command": "cargo kani" if mode.startswith("cargo") else "kani"}
        if expected_text is None:
            if mode != "exec":
                kinds.append("no-expected-file")
            oracle.update({"run_verdict": None, "harnesses": [_harness_row(h, None, None) for h in selected],
                           "checks": [], "covers": [], "summary": None, "diagnostics": [],
                           "contains_lines": [], "trivial_blocks": 0})
        elif mode in ("coverage-based", "cargo-coverage"):
            blocks, trivial = contains_blocks(expected_text)
            kinds.append("coverage-report")
            oracle.update({"run_verdict": None, "harnesses": [_harness_row(h, None, None) for h in selected],
                           "checks": [], "covers": [], "summary": None, "diagnostics": [],
                           "contains_lines": blocks, "trivial_blocks": trivial})
        else:
            parsed = parse_expected(expected_text)
            run, harness_rows = _derive_verdicts(parsed, selected)
            oracle.update({
                "run_verdict": run,
                "harnesses": harness_rows,
                "checks": parsed["checks"],
                "covers": parsed["covers"],
                "summary": {
                    "complete": parsed["complete"],
                    "check_summaries": parsed["check_summaries"],
                    "cover_summaries": parsed["cover_summaries"],
                    "partial_summaries": parsed["partial_summaries"],
                    "failed_checks": parsed["failed_checks"],
                    "verification_failed_for": parsed["verification_failed_for"],
                    "verification_lines": parsed["verification_lines"],
                    "unwinding_failure_banner": parsed["unwinding_failure_banner"],
                },
                "diagnostics": parsed["diagnostics"],
                "contains_lines": parsed["contains_lines"],
                "trivial_blocks": parsed["trivial_blocks"],
            })
            if parsed["verification_lines"] and any(l["harness"] is None for l in parsed["verification_lines"]):
                kinds.append("whole-run")
            if parsed["harness_lines"] or parsed["verification_failed_for"] or parsed["complete"]:
                kinds.append("per-harness")
            if any(c["status"] for c in parsed["checks"]):
                kinds.append("per-check")
            if parsed["covers"]:
                kinds.append("cover")
            if parsed["diagnostics"]:
                kinds.append("diagnostic")
            if not ({"whole-run", "per-harness", "per-check", "cover", "diagnostic"} & set(kinds)):
                kinds.append("text-only")
    oracle["oracle_kinds"] = kinds
    return oracle


def suite_of(unit):
    return unit["suite"]


def _harness_row(h, verdict, basis):
    return {"name": h["pretty_name"], "should_panic": h["should_panic"], "kind": h["kind"],
            "verdict": verdict, "basis": basis}


def _derive_verdicts(parsed, selected):
    stated = {}
    conflicts = []

    def put(name, verdict, basis, qualifier=None):
        prev = stated.get(name)
        if prev and prev["verdict"] != verdict:
            conflicts.append(name)
        if not prev or basis == "verification-line":
            stated[name] = {"verdict": verdict, "basis": basis, "qualifier": qualifier}

    for line in parsed["verification_lines"]:
        if line["harness"] is not None:
            put(line["harness"], line["verdict"], "verification-line", line["qualifier"])
    for name in parsed["verification_failed_for"]:
        put(name, "FAILED", "verification-failed-for")

    run_lines = [l for l in parsed["verification_lines"] if l["harness"] is None]
    complete = parsed["complete"][-1] if parsed["complete"] else None
    any_failed = (any(v["verdict"] == "FAILED" for v in stated.values())
                  or any(l["verdict"] == "FAILED" for l in run_lines)
                  or (complete is not None and complete["failed"] > 0))
    run = None
    if any_failed:
        basis = "summary-line" if complete and complete["failed"] > 0 else (
            "verification-failed-for" if parsed["verification_failed_for"] else "verification-line")
        run = {"verdict": "FAILED", "basis": basis, "complete": True}
    elif complete is not None:
        run = {"verdict": "SUCCESSFUL", "basis": "summary-line", "complete": True}
    elif run_lines or stated:
        single = len(selected) == 1
        run = {"verdict": "SUCCESSFUL",
               "basis": "single-harness-verification-line" if single else "verification-line",
               "complete": single}
    rows, matched = [], set()
    for h in selected:
        verdict, basis = None, None
        for name, st in stated.items():
            if h in _match_harness(name, selected):
                verdict, basis = st["verdict"], st["basis"]
                matched.add(name)
        if verdict is None and complete is not None and complete["unit"] == "harnesses":
            if complete["failed"] == 0:
                verdict, basis = "SUCCESSFUL", "summary-line"
            elif len(parsed["verification_failed_for"]) == complete["failed"]:
                verdict, basis = "SUCCESSFUL", "summary-line-minus-failed-for"
        if verdict is None and len(selected) == 1 and run_lines:
            verdict, basis = run_lines[-1]["verdict"], "single-harness-verification-line"
        rows.append(_harness_row(h, verdict, basis))
    for name, st in sorted(stated.items()):
        if name not in matched:
            rows.append({"name": name, "should_panic": None, "kind": None, "verdict": st["verdict"],
                         "basis": st["basis"] + ":unmatched-source-harness"})
    if run is not None and conflicts:
        run["conflicting_statements"] = sorted(set(conflicts))
    if run is not None and complete is not None:
        run["summary_unit"] = complete["unit"]
        run["summary_total"] = complete["total"]
        run["selected_source_harnesses"] = len(selected)
    return run, rows
