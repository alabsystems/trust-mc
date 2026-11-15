#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Mutants of the landing gate's selection, reuse, scaling and judgment: each
one weakens a rule the way a careless edit would, and each must fail a test.

A mutant is applied to a copy of scripts/ (the snippet must occur exactly
once, so a mutant cannot go stale silently), and the named test classes run
against that copy in a fresh interpreter. The unmutated copy must pass the
same classes first, so a mutant's failure is the mutation's doing."""

from __future__ import annotations

import dataclasses
import shutil
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent

SELECT = ("test_landing_select.py", ("SelectRules", "FailClosedTrees", "PathRefs"))
HOST = ("test_host_room.py", ("Plans", "Admission", "Runner"))
ENGINE = ("test_engine_suite_gate.py", ("ResourcePlanTests",))
RECORD = ("test_landing_gate.py", ("RunRecordCheckpoints",))
LIFECYCLE = ("test_landing_gate.py", ("InterruptedLegProcesses",))
GATE = ("test_landing_gate.py", ("DualJudgment", "CacheKeys", "LegInputsAgreeWithTheSelector",
                                 "ScriptTestFailures", "LegCommands", "BudgetBoundRuns", "LivePinChecks",
                                 "DualPoolNeed", "PinnedCliOutput", "LockedFetch"))
LIVE_MAIN = ("test_check_live_main.py", ("LiveMainTests",))


@dataclasses.dataclass(frozen=True)
class Mutant:
    name: str
    file: str
    old: str
    new: str
    tests: tuple[str, tuple[str, ...]]


MUTANTS = (
    Mutant("main observation returns to REST instead of authenticated Git refs", "check_live_main.py",
           '("repo", "refs", repository, "--ref", "refs/heads/main")',
           '("api", f"repos/{repository}/git/ref/heads/main")', LIVE_MAIN),
    Mutant("an advertisement may include extra references", "check_live_main.py",
           "if not isinstance(response, list) or len(response) != 1:",
           "if not isinstance(response, list) or not response:", LIVE_MAIN),
    Mutant("another advertised branch is accepted as main", "check_live_main.py",
           'if reference["ref"] != "refs/heads/main":', "if False:", LIVE_MAIN),
    Mutant("duplicate advertisement fields use the last value", "check_live_main.py",
           "json.loads(output, object_pairs_hook=unique_object)", "json.loads(output)", LIVE_MAIN),
    Mutant("an all-zero advertised oid is accepted", "check_live_main.py",
           'if COMMIT_RE.fullmatch(value) is None or value == "0" * 40:',
           'if COMMIT_RE.fullmatch(value) is None:', LIVE_MAIN),
    Mutant("a fetched noncommit object becomes main authority", "check_live_main.py",
           'if kind != "commit":', 'if False:', LIVE_MAIN),
    Mutant("main observations allow anonymous API fallback", "check_live_main.py",
           '[executable, *arguments, "--no-anonymous-api"]', '[executable, *arguments]', LIVE_MAIN),
    Mutant("main tracking refresh overwrites a concurrent update", "check_live_main.py",
           '("update-ref", tracking_ref, fetched, old)', '("update-ref", tracking_ref, fetched)', LIVE_MAIN),
    Mutant("a queued timeout signals after the child is reaped", "host_room.py",
           "                if not run.reaped:\n                    run.timed_out = True\n",
           "                if True:\n                    run.timed_out = True\n", HOST),
    Mutant("a direct pool keeps the default SIGTERM action", "host_room.py",
           "previous_signals[sig] = signal.signal(sig, request_stop)",
           "previous_signals[sig] = signal.signal(sig, signal.SIG_DFL)", LIFECYCLE),
    Mutant("the pinned CLI bypasses owned child cleanup", "landing-gate.py",
           '            with _owned_process(["scripts/build-pinned-ay-cli.sh"], cwd=tree, env=env, stderr=sink, text=False) as proc:\n',
           '            with subprocess.Popen(["scripts/build-pinned-ay-cli.sh"], cwd=tree, env=env, stdout=subprocess.PIPE, stderr=sink) as proc:\n',
           LIFECYCLE),
    Mutant("the pinned CLI accepts a failing build's stdout path", "landing-gate.py",
           "        if proc.returncode != 0 or not lines:\n",
           "        if not lines:\n", GATE),
    Mutant("setup leaves an older run verdict in place", "landing-gate.py",
           "    # Invalidate an older same-head pass before setup or a child can fail.\n"
           "    checkpoint_run(record_path, record)\n", "", RECORD),
    Mutant("the active leg is not checkpointed", "landing-gate.py",
           "            checkpoint_run(record_path, record, leg)\n", "", RECORD),
    Mutant("an incomplete run claims a pass", "landing-gate.py",
           '    record["verdict"] = "partial-incomplete" if record["partial"] else "incomplete"\n',
           '    record["verdict"] = "pass"\n', RECORD),
    Mutant("a failed record replacement overwrites the prior record", "landing-gate.py",
           "        os.replace(temporary, path)\n", "        path.write_text(temporary.read_text())\n", RECORD),
    # -- a selector that drops a check the change affects
    Mutant("an engine change no longer selects the engine suite", "landing_select.py",
           '            add("engine-suite", crate)\n', "", SELECT),
    Mutant("the reverse-dependency closure is skipped", "landing_select.py",
           "    affected = reverse_closure(packages, seeds)\n", "    affected = set(seeds)\n", SELECT),
    Mutant("a bundle crate no longer selects the BMC dual", "landing_select.py",
           "            for leg in DUAL_LEGS:\n                add(leg, crate)\n",
           '            add("dual-chc", crate)\n', SELECT),
    Mutant("CHC codegen selects the CHC dual only (the unsound lane split)", "landing_select.py",
           "        if _under(path, LANE_PORT_SOURCES):\n",
           '        if "/codegen_ay/chc/" in path:\n'
           '            return PathVerdict(legs=frozenset({"dual-chc", "engine-suite"}), rule="chc")\n'
           "        if _under(path, LANE_PORT_SOURCES):\n", SELECT),
    Mutant("crate literals are ignored", "landing_select.py",
           "    crates: set[str] = {crate for crate, targets in ctx.literal_refs.items()\n"
           "                        if any(_under(path, t) for t in targets)}\n",
           "    crates: set[str] = set()\n", SELECT),
    Mutant("a target root no longer owns its files (engine sources)", "landing_select.py",
           "        for root in pkg.roots:\n            if root:\n",
           "        for root in ():\n            if root:\n", SELECT),
    Mutant("a chc-only dual entry selects nothing", "landing_select.py",
           '            legs |= {f"dual-{lane}" for lane in ctx.dual_lanes[path]}\n', "", SELECT),
    Mutant("a slash-free Markdown literal is ignored", "landing_select.py",
           "                refs[crate].add(_norm(posixpath.join(base, literal)))\n",
           "                pass\n", SELECT),
    Mutant("what a leg's scripts read selects nothing", "landing_select.py",
           "    read_legs, read_tests = ctx.read_by(path)\n", "    read_legs, read_tests = set(), []\n", SELECT),
    Mutant("a script's code closure stops at the files it names directly", "landing_select.py",
           "            closure.add(cand)\n            stack.append(cand)\n", "            closure.add(cand)\n", SELECT),
    Mutant("a deleted file's name is not searched for", "landing_select.py",
           "    patterns = [pat for path in deleted for pat in _reference_patterns(path)]\n",
           "    patterns = []\n", SELECT),
    # -- a selector that maps an unknown path to anything less than everything
    Mutant("an unmapped path selects only the doc check", "landing_select.py",
           'return PathVerdict(everything=f"{path}: unmapped (no rule names an owner)", rule="unmapped")',
           'return PathVerdict(legs=frozenset({"docs-links"}), rule="unmapped")', SELECT),
    Mutant("Cargo.lock is no build input", "landing_select.py",
           '    "Cargo.toml", "Cargo.lock", "build.rs",', '    "Cargo.toml", "build.rs",', SELECT),
    Mutant("a gate script selects only the script tests", "landing_select.py",
           "    if path in ctx.gate_scripts:\n", "    if False:\n", SELECT),
    Mutant("a symbolic link in the diff is followed", "landing_select.py",
           '{change.old_mode, change.new_mode} & {"120000", "160000"}', "set()", SELECT),
    Mutant("an unreadable graph is ignored", "landing_select.py",
           "    if ctx.graph_error is not None:\n", "    if False:\n", SELECT),
    Mutant("a path joined by / is read segment by segment", "landing_select.py",
           """    text = _SLASH_JOINED.sub(lambda m: '"' + parts(m.group(0)) + '"', text)\n""", "", SELECT),
    Mutant("a case-folded twin is ignored", "landing_select.py",
           "    others = ctx.casefold.get(path.casefold(), set()) - {path}\n", "    others = set()\n", SELECT),
    # -- a cache keyed on fewer inputs
    Mutant("the leg key drops the toolchain", "landing-gate.py",
           '        "leg": leg,\n        "inputs": input_digest,\n        "toolchain": toolchain,\n',
           '        "leg": leg,\n        "inputs": input_digest,\n', GATE),
    Mutant("the leg key drops the merge base", "landing-gate.py",
           '        "base": base,\n        "extra": extra or {},\n', '        "extra": extra or {},\n', GATE),
    Mutant("the leg key drops the verdict environment", "landing-gate.py",
           '        "command": command,\n        "env": verdict_env(),\n', '        "command": command,\n', GATE),
    Mutant("the leg key drops a verdict argument", "landing-gate.py",
           'NON_VERDICT_ARGS = frozenset({"--report", "--history", "--record"})',
           'NON_VERDICT_ARGS = frozenset({"--report", "--history", "--record", "--base-ref"})', GATE),
    Mutant("the entry key drops the flags", "soundness-dual-gate.py",
           '        "flags": list(job.entry.flags),\n', "", GATE),
    Mutant("the entry key drops the inherited environment", "soundness-dual-gate.py",
           '        "inherited_env": dict(sorted(inherited_env.items())),\n', "", GATE),
    Mutant("the entry key drops the wall limit", "soundness-dual-gate.py",
           '        "wall_limit_s": wall_limit_s,\n', "", GATE),
    Mutant("the TSV growth rule's key ignores main's TSV", "landing-gate.py",
           '            out.append(f"{ENGINE_TSV}@{base_ref_blob}")\n', '            out.append(ENGINE_TSV)\n', GATE),
    Mutant("a budget-bound driver run is stored", "soundness-dual-gate.py",
           '                and not result["run"]["budget_bound"]):\n', "                ):\n", GATE),
    Mutant("an own-tree main report with budget-bound runs is reused", "landing-gate.py",
           '            and bool(runs) and all(run.get("budget_bound") is False for run in runs))\n',
           "            and bool(runs))\n", GATE),
    Mutant("the bundle identity drops the sibling checkouts", "landing-gate.py",
           '        "toolchain": toolchain,\n        "siblings": siblings,\n        "build":',
           '        "toolchain": toolchain,\n        "build":', GATE),
    Mutant("a leg's inputs omit the crates that select it", "landing-gate.py",
           "        out[path] = closure_legs[crates] | set(verdict.legs)\n",
           "        out[path] = set(verdict.legs)\n", GATE),
    # -- a scaler that oversubscribes
    Mutant("a timing-sensitive child ignores the load", "host_room.py",
           "    if timing_sensitive:\n", "    if False:\n", HOST),
    Mutant("each cap is the whole room", "host_room.py", "    cap = room // capacity\n", "    cap = room\n", HOST),
    Mutant("a busy start reserves the whole room", "host_room.py",
           "    cap = room // capacity\n", "    cap = room // jobs\n", HOST),
    Mutant("fixed libtest threads reserve unused pool growth", "engine-suite-gate.py",
           "                            max_jobs=max_jobs, reserve_growth=False,\n",
           "                            max_jobs=max_jobs, reserve_growth=True,\n", ENGINE),
    Mutant("jobs ignore the memory bound", "host_room.py",
           "    jobs = min(mem_jobs, cpu_jobs)\n", "    jobs = cpu_jobs\n", HOST),
    Mutant("the margin is dropped", "host_room.py",
           "    room = reading.available_mb - margin - max(0, reserve_mb)\n",
           "    room = reading.available_mb - max(0, reserve_mb)\n", HOST),
    Mutant("admission ignores the running children's growth", "host_room.py",
           "    return available_now_mb - margin_mb >= cap_mb + max(0, running_headroom_mb)\n",
           "    return available_now_mb - margin_mb >= cap_mb\n", HOST),
    Mutant("a capped-out run is scored", "host_room.py",
           "        if run.breached:\n            log(", "        if False:\n            log(", HOST),
    Mutant("launches skip the re-measured admission", "host_room.py",
           "                ok = n_running == 0 or (\n", "                ok = True or (\n", HOST),
    Mutant("a build-slot share is ignored", "host_room.py",
           "    share = slot_share()\n    if share is not None:\n        given",
           "    share = None\n    if share is not None:\n        given", HOST),
    Mutant("a task known to outgrow the pool never runs", "host_room.py",
           "    requeue: List[Task] = [t for t in tasks if t.alone]\n", "    requeue: List[Task] = []\n", HOST),
    Mutant("the dual pool's need is its largest peak", "soundness-dual-gate.py",
           "    at = min(len(peaks) - 1, int(POOL_NEED_QUANTILE * len(peaks)))\n",
           "    at = len(peaks) - 1\n", GATE),
    Mutant("a run known to outgrow the cap runs in the pool", "soundness-dual-gate.py",
           "    return isinstance(peak, int) and int(peak * 1.25) > cap_mb\n", "    return False\n", GATE),
    Mutant("more children than jobs", "host_room.py",
           "            if pending and (n_running < p.jobs or grow):\n", "            if pending:\n", HOST),
    Mutant("a run grows past the cores the load holds", "host_room.py",
           "    return running < bound and p.reading.logical_cores - load_now >= p.threads_per_child\n",
           "    return running < bound\n", HOST),
    Mutant("a run grows past max_jobs", "host_room.py",
           "    bound = p.growth_limit()\n",
           "    bound = p.mem_jobs\n", HOST),
    # -- a judgment weaker than the by-hand convention
    Mutant("an alone run excuses a missed bug", "landing-gate.py",
           '        if row["class"] in UNEXCUSABLE:\n            failures.append(',
           '        if False:\n            failures.append(', GATE),
    Mutant("known-red for any class excuses", "landing-gate.py",
           'if again.get("known_red") and again.get("known_red_class") == again["class"]:',
           'if again.get("known_red"):', GATE),
    Mutant("a script test's subtests collapse into one id", "landing-gate.py",
           '_UNITTEST_FAIL_RE = re.compile(r"^(?:FAIL|ERROR): (\\S+) \\(([^)]*)\\)(?: (.*))?$", re.M)',
           '_UNITTEST_FAIL_RE = re.compile(r"^(?:FAIL|ERROR): (\\S+) \\(([^)]*)\\)()", re.M)', GATE),
    Mutant("a script test re-run alone is judged by its first run", "landing-gate.py",
           "        judged = alone.get(name, ids)\n", "        judged = ids & alone.get(name, ids)\n", GATE),
    Mutant("the bundle identity drops a build input with the gate's code", "landing-gate.py",
           "    inputs = {p: v for p, v in by_path.items() if p not in gate_only}\n",
           "    inputs = {p: v for p, v in by_path.items() if v is not None}\n", GATE),
    Mutant("a pin check failing differently on main is excused", "landing-gate.py",
           "    return (rc != 0 and rc == main_rc\n",
           "    return (rc != 0 or rc == main_rc\n", GATE),
    Mutant("a row main gates less severely is not new", "landing-gate.py",
           'if gating and not (m_gating and severity(m_cls) <= severity(row["class"])):',
           "if gating and not m_gating:", GATE),
    Mutant("the change's live pin check runs on an unfetched Cargo home", "landing-gate.py",
           "            for note in self.fetch_locked(self.repo):\n"
           "                print(f\"[landing] {note}\", flush=True)\n", "", GATE),
    Mutant("main's live pin check runs on an unfetched Cargo home", "landing-gate.py",
           "        for note in self.fetch_locked(tmc):\n"
           "            print(f\"[landing] {note}\", flush=True)\n", "", GATE),
    Mutant("the host-setup fetch may re-resolve the lockfile", "landing-gate.py",
           'argv = [self.targo(), "fetch", "--locked", "--manifest-path"',
           'argv = [self.targo(), "fetch", "--manifest-path"', GATE),
    Mutant("a failed host-setup fetch is silent", "landing-gate.py",
           "        last = (result.stderr.strip().splitlines() or [\"no output\"])[-1]\n"
           "        return [f\"locked fetch in {tree} exited",
           "        return []\n"
           "        return [f\"locked fetch in {tree} exited", GATE),
)


def copy_scripts(dest: Path) -> Path:
    target = dest / "scripts"
    shutil.copytree(SCRIPTS, target, ignore=shutil.ignore_patterns("__pycache__"))
    return target


def run_all(cases: list[tuple[str, str | None, str | None, str, tuple[str, tuple[str, ...]]]]) -> dict[str, int]:
    """Run each (name, file, old, new, tests) case in its own copy of scripts/,
    as many at once as the host has room for (scripts/host_room.py), and
    return each case's exit status. ``file`` None is an unmutated control."""
    sys.path.insert(0, str(SCRIPTS))
    import host_room  # noqa: PLC0415

    plan = host_room.wait_for_plan(need_mb=512, label="landing mutants", log=lambda _line: None)
    if not plan.admitted:
        # No room even for one: run them one at a time, as before, rather than
        # not at all (the runner re-runs a child over its cap uncapped).
        plan = dataclasses.replace(plan, admitted=True, jobs=1, cap_mb=512, room_mb=512)
    status: dict[str, int] = {}
    tmp = tempfile.TemporaryDirectory(prefix="landing-mutants-")
    tasks = []
    for index, (name, file, old, new, tests) in enumerate(cases):
        scripts = copy_scripts(Path(tmp.name) / str(index))
        if file is not None:
            path = scripts / file
            text = path.read_text()
            if text.count(old) != 1:
                status[name] = -1000 - text.count(old)      # stale: the snippet must occur once
                continue
            path.write_text(text.replace(old, new))
        test_file, classes = tests

        def done(_output: str, outcome, name: str = name) -> None:
            status[name] = outcome.exit_code if outcome.exit_code is not None else -1

        tasks.append(host_room.Task(
            key=name, expected_s=None,
            prepare=lambda scripts=scripts, test_file=test_file, classes=classes: (
                [sys.executable, str(scripts / test_file), *classes], None, str(scripts), 900),
            done=done))
    try:
        host_room.run_tasks(tasks, plan, log=lambda _line: None)
    finally:
        tmp.cleanup()
    return status


class LandingMutants(unittest.TestCase):
    def test_controls_pass_and_every_mutant_fails_a_test(self) -> None:
        controls = [(f"control {tests[0]} {tests[1]}", None, None, "", tests)
                    for tests in (SELECT, HOST, GATE, ENGINE, RECORD, LIFECYCLE, LIVE_MAIN)]
        mutants = [(m.name, m.file, m.old, m.new, m.tests) for m in MUTANTS]
        status = run_all(controls + mutants)
        for name, *_ in controls:
            with self.subTest(case=name):
                self.assertEqual(status.get(name), 0, f"{name} failed: a mutant's failure would mean nothing")
        for name, *_ in mutants:
            with self.subTest(mutant=name):
                self.assertGreater(status.get(name, -1), -1000, f"stale mutant (snippet not found once): {name}")
                self.assertNotEqual(status.get(name), 0, f"mutant survived: {name}")


if __name__ == "__main__":
    unittest.main()
