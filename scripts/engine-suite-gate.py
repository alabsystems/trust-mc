#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""The engine lib suite as a gate: a shrink-only, flake-aware ratchet.

Runs the `trust-mc-engine` library tests (the ones no other standing gate
runs: `publish/config.sh` runs `trust-mc-core --lib` only) and holds their
failures to `tools/engine-suite/known-failures.tsv`:

    TRUST_MC_AY_TEST_TIMEOUT_SECS=120 targo --unverified test --locked \\
        -p trust-mc-engine --lib --features ay,compiler-corpus-tests

The TSV has the columns `test`, `class`, `stability` (`deterministic` or
`load-dependent`), `evidence` and `measured-at`. The rules (design
trust-mc-reds-final §7.3):

  1. A failing test NOT in the TSV is re-run once, alone (`--exact
     --test-threads 1`). The gate fails only if it fails again, and it reports
     both runs. One that passes alone is reported as a flake.
  2. A `deterministic` TSV row whose test passes FAILS the gate: the row is
     stale and the TSV must shrink in the same change.
  3. A `load-dependent` TSV row whose test passes is reported, not failed. A
     row may carry `load-dependent` only with evidence of both outcomes (its
     evidence names a pass and a failure); this script checks that the
     evidence says so, not that the runs happened.
  4. The TSV may not GAIN a row against the base ref's copy (default
     `origin/main`): a new failure is fixed, never ledgered. A row whose
     stability moves from `deterministic` to `load-dependent` counts as a
     gain too, unless its evidence changed with it.
  5. A TSV row naming a test the suite did not run fails the gate (the test
     was renamed or deleted; drop or rename the row).

The suite must COMPLETE: a run whose libtest summary is missing (a build
failure, a crash, a killed process) or whose counts disagree with the test
list exits 2 (NOT RUN), never 0.

Exit codes: 0 pass, 1 gate failure, 2 not run or refused input. A JSON report
is written to `--report`. This is test evidence about one development build;
it is no proof claim.
"""

from __future__ import annotations

import argparse
import dataclasses
import datetime as _dt
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Callable, Iterable, Sequence

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
TSV_REL = "tools/engine-suite/known-failures.tsv"
DEFAULT_TSV = REPO_ROOT / TSV_REL
DEFAULT_REPORT = REPO_ROOT / "target" / "engine-suite-gate" / "report.json"
REPORT_SCHEMA = "trust-mc.engine-suite-gate-report/v1"

HEADER = ("test", "class", "stability", "evidence", "measured-at")
STABILITIES = ("deterministic", "load-dependent")
# The failure classes of the design's §7 classification. A row names the one
# that explains it; `O` is "other, per test".
CLASSES = ("E1", "E2", "E3", "T2", "T3", "T4", "A", "S1", "S2", "O")
TIMEOUT_ENV = {"TRUST_MC_AY_TEST_TIMEOUT_SECS": "120"}
SUITE_ARGS = (
    "--unverified",
    "test",
    "--locked",
    "-p",
    "trust-mc-engine",
    "--lib",
    "--features",
    "ay,compiler-corpus-tests",
)

STATUS_LINE = re.compile(r"^test (\S+) \.\.\. (ok|FAILED|ignored)\b")
SUMMARY_LINE = re.compile(
    r"^test result: (ok|FAILED)\. (\d+) passed; (\d+) failed; (\d+) ignored; "
    r"(\d+) measured; (\d+) filtered out"
)
LIST_LINE = re.compile(r"^(\S+): test$")


class GateInputError(Exception):
    """Input the gate refuses (exit 2): a malformed TSV or an incomplete run."""


@dataclasses.dataclass(frozen=True)
class Row:
    test: str
    klass: str
    stability: str
    evidence: str
    measured_at: str
    line: int


@dataclasses.dataclass
class SuiteRun:
    """One libtest run: the failing and ignored names, and its summary."""

    failed: set[str]
    ignored: set[str]
    passed_count: int
    failed_count: int
    ignored_count: int
    filtered_count: int


def parse_tsv(text: str, *, source: str = TSV_REL) -> list[Row]:
    """Parse and validate the known-failures TSV. Raises GateInputError."""
    rows: list[Row] = []
    lines = text.splitlines()
    if not lines:
        raise GateInputError(f"{source}: empty file (the header is required)")
    header = tuple(lines[0].split("\t"))
    if header != HEADER:
        want = "\t".join(HEADER)
        raise GateInputError(f"{source}:1: header must be {want!r}, got {lines[0]!r}")
    seen: dict[str, int] = {}
    for number, line in enumerate(lines[1:], start=2):
        if not line.strip() or line.startswith("#"):
            continue
        cells = line.split("\t")
        if len(cells) != len(HEADER):
            raise GateInputError(
                f"{source}:{number}: {len(cells)} columns, expected {len(HEADER)} (tab-separated)"
            )
        test, klass, stability, evidence, measured_at = (c.strip() for c in cells)
        if not test:
            raise GateInputError(f"{source}:{number}: empty test name")
        if test in seen:
            raise GateInputError(f"{source}:{number}: {test} is listed twice (first at line {seen[test]})")
        seen[test] = number
        if klass not in CLASSES:
            raise GateInputError(f"{source}:{number}: class {klass!r} is not one of {', '.join(CLASSES)}")
        if stability not in STABILITIES:
            raise GateInputError(
                f"{source}:{number}: stability {stability!r} is not one of {', '.join(STABILITIES)}"
            )
        if not evidence:
            raise GateInputError(f"{source}:{number}: {test} has no evidence")
        if not measured_at:
            raise GateInputError(f"{source}:{number}: {test} has no measured-at")
        if stability == "load-dependent" and not has_both_outcomes(evidence):
            raise GateInputError(
                f"{source}:{number}: {test} is load-dependent, so its evidence must name both "
                "outcomes (a pass alone and a failure inside the suite run)"
            )
        rows.append(Row(test, klass, stability, evidence, measured_at, number))
    return rows


def has_both_outcomes(evidence: str) -> bool:
    lowered = evidence.lower()
    return bool(re.search(r"\bpass", lowered)) and bool(re.search(r"\bfail", lowered))


def parse_list(text: str) -> list[str]:
    """The test names of a `-- --list` run, in order and with multiplicity: a
    test that carries `#[test]` twice is listed, and run, twice."""
    return [m.group(1) for line in text.splitlines() if (m := LIST_LINE.match(line.strip()))]


def parse_suite(text: str) -> SuiteRun:
    """Parse a libtest run (pretty output). Raises GateInputError when the run
    did not complete: no summary line, or the failure list disagrees with it."""
    summaries = [m for line in text.splitlines() if (m := SUMMARY_LINE.match(line.strip()))]
    if not summaries:
        raise GateInputError("the libtest summary line is missing: the suite did not complete")
    if len(summaries) > 1:
        raise GateInputError(f"{len(summaries)} libtest summaries: expected one test binary")
    summary = summaries[0]
    failed_from_lines: set[str] = set()
    ignored: set[str] = set()
    for line in text.splitlines():
        m = STATUS_LINE.match(line.strip())
        if not m:
            continue
        if m.group(2) == "FAILED":
            failed_from_lines.add(m.group(1))
        elif m.group(2) == "ignored":
            ignored.add(m.group(1))
    failed = final_failure_list(text)
    if failed is None:
        failed = set()
    # The final `failures:` list is authoritative; a status line may be torn by
    # a child process writing to the inherited stdout, so it can only add.
    failed |= failed_from_lines
    run = SuiteRun(
        failed=failed,
        ignored=ignored,
        passed_count=int(summary.group(2)),
        failed_count=int(summary.group(3)),
        ignored_count=int(summary.group(4)),
        filtered_count=int(summary.group(6)),
    )
    if len(run.failed) != run.failed_count:
        raise GateInputError(
            f"the summary counts {run.failed_count} failures but {len(run.failed)} failing tests "
            "were named; the output is torn or truncated"
        )
    return run


def final_failure_list(text: str) -> set[str] | None:
    """The names in the LAST `failures:` block (the indented list libtest prints
    right before the summary), or None when the run printed none."""
    lines = text.splitlines()
    last = None
    for index, line in enumerate(lines):
        if line.rstrip() == "failures:":
            last = index
    if last is None:
        return None
    names: set[str] = set()
    for line in lines[last + 1 :]:
        if not line.strip():
            if names:
                break
            continue
        if not line.startswith("    "):
            break
        names.add(line.strip())
    return names


@dataclasses.dataclass
class Decision:
    failures: list[str]
    reports: list[str]
    reruns: dict[str, str]

    @property
    def ok(self) -> bool:
        return not self.failures


def decide(
    rows: Sequence[Row],
    base_rows: Sequence[Row] | None,
    listed: Sequence[str],
    run: SuiteRun,
    rerun_alone: Callable[[str], bool],
) -> Decision:
    """Apply the gate's rules. `rerun_alone(name)` re-runs one test alone and
    returns whether it passed."""
    failures: list[str] = []
    reports: list[str] = []
    reruns: dict[str, str] = {}
    by_name = {row.test: row for row in rows}

    universe = set(listed)
    expected_total = len(listed) - run.filtered_count
    counted = run.passed_count + run.failed_count + run.ignored_count
    if counted != expected_total:
        raise GateInputError(
            f"the run counted {counted} tests but the list has {expected_total}: "
            "the suite did not run whole"
        )
    for name, count in sorted(Counter(listed).items()):
        if count > 1:
            reports.append(f"{name} is listed {count} times, so libtest runs it {count} times")
    unknown_failed = run.failed - universe
    if unknown_failed:
        raise GateInputError(f"failing tests missing from the test list: {sorted(unknown_failed)}")

    for row in rows:
        if row.test not in universe:
            failures.append(
                f"{TSV_REL}:{row.line}: {row.test} is not a test of this suite (renamed or deleted): "
                "drop or rename the row"
            )
            continue
        if row.test in run.ignored:
            failures.append(f"{TSV_REL}:{row.line}: {row.test} is #[ignore]d: an ignored test is not a known failure")
            continue
        if row.test in run.failed:
            continue
        if row.stability == "deterministic":
            failures.append(
                f"{TSV_REL}:{row.line}: {row.test} PASSES but is listed deterministic: delete the row "
                "(the TSV only shrinks)"
            )
        else:
            reports.append(f"{row.test}: load-dependent row passed in this run (reported, not failed)")

    for name in sorted(run.failed - by_name.keys()):
        passed = rerun_alone(name)
        reruns[name] = "pass" if passed else "fail"
        if passed:
            reports.append(f"{name}: failed in the suite run, PASSED alone (flake; both runs reported)")
        else:
            failures.append(
                f"{name}: failed in the suite run AND alone, and is not in {TSV_REL}: fix it (a new "
                "failure is never ledgered)"
            )

    if base_rows is None:
        reports.append(f"base ref has no {TSV_REL}: the growth rule has nothing to compare against")
    else:
        failures.extend(growth_failures(rows, base_rows))
    return Decision(failures, reports, reruns)


def growth_failures(rows: Sequence[Row], base_rows: Sequence[Row]) -> list[str]:
    """Rule 4: the TSV may not gain a row against the base ref's copy, and a row
    may not relax deterministic -> load-dependent without new evidence."""
    failures = []
    base = {row.test: row for row in base_rows}
    for row in rows:
        old = base.get(row.test)
        if old is None:
            failures.append(
                f"{TSV_REL}:{row.line}: {row.test} is a row the base ref's TSV does not have: "
                "the TSV only shrinks"
            )
        elif (
            old.stability == "deterministic"
            and row.stability == "load-dependent"
            and old.evidence == row.evidence
        ):
            failures.append(
                f"{TSV_REL}:{row.line}: {row.test} moved deterministic -> load-dependent with no "
                "new evidence"
            )
    return failures


def resolve_targo() -> str:
    out = subprocess.run(
        [str(SCRIPTS_DIR / "resolve-trust-tool.sh"), "targo"],
        check=True,
        capture_output=True,
        text=True,
    )
    return out.stdout.strip()


def suite_env() -> dict[str, str]:
    env = dict(os.environ)
    env.update(TIMEOUT_ENV)
    for var in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RUSTC", "RUSTC_WRAPPER"):
        env.pop(var, None)
    return env


def run_cargo(targo: str, libtest_args: Iterable[str], log: Path) -> str:
    env = suite_env()
    command = [targo, *SUITE_ARGS, "--", *libtest_args]
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("w") as sink:
        sink.write("$ " + " ".join(command) + "\n")
        sink.flush()
        proc = subprocess.run(command, cwd=REPO_ROOT, env=env, stdout=subprocess.PIPE, stderr=sink, text=True)
        sink.write(proc.stdout)
    return proc.stdout


def _host_room():
    sys.path.insert(0, str(SCRIPTS_DIR))
    try:
        import host_room  # noqa: PLC0415
    finally:
        sys.path.pop(0)
    return host_room


# The libtest thread count the suite ran with before it was sized to the host
# (`.cargo/config.toml` forces RUST_TEST_THREADS=2 on every cargo-run process).
# Kept only as the history-free need of one thread's share; `--test-threads`
# decides the count.
HISTORY_FREE_NEED_MB = 2048


def plan_threads(requested: str, history: dict[str, object] | None):
    """The suite's libtest thread count, sized to the measured room.

    Each thread's need is the prior run's peak RSS divided by its threads
    (plus a quarter), at least HISTORY_FREE_NEED_MB; its CPU share is the prior
    run's CPU seconds per wall second per thread (at least 1). ``requested`` is
    'auto' or an upper bound."""
    hr = _host_room()
    need = HISTORY_FREE_NEED_MB
    per_thread_cpu = 1.0
    if history:
        peak, threads = history.get("peak_rss_mb"), history.get("test_threads")
        if isinstance(peak, int) and isinstance(threads, int) and threads > 0:
            need = max(need, int(peak / threads * 1.25))
        cpu, wall = history.get("cpu_s"), history.get("suite_seconds")
        if isinstance(cpu, (int, float)) and isinstance(wall, (int, float)) and wall > 0 and isinstance(threads, int):
            per_thread_cpu = max(1.0, round(cpu / wall / max(1, threads), 2))
    max_jobs = None if requested == "auto" else int(requested)
    return hr.wait_for_plan(need_mb=need, label="engine-suite", threads_per_child=per_thread_cpu,
                            max_jobs=max_jobs, reserve_growth=False,
                            log=lambda line: print(line, flush=True))


def run_suite_scaled(targo: str, threads_plan, log: Path) -> tuple[str, dict[str, object]]:
    """The full-suite run with ``--test-threads`` from the plan, the whole
    test process capped at threads x cap by the scaled runner (a breach is
    re-run uncapped, never scored)."""
    hr = _host_room()
    command = [targo, *SUITE_ARGS, "--", "--test-threads", str(threads_plan.jobs)]
    whole = dataclasses.replace(threads_plan, jobs=1, cap_mb=threads_plan.jobs * threads_plan.cap_mb,
                                need_mb=threads_plan.jobs * threads_plan.need_mb)
    out: dict[str, object] = {}

    def done(text: str, outcome) -> None:
        out["text"] = text
        out["outcome"] = outcome

    # stdout (libtest) is the parsed text; stderr (cargo, children) goes to the
    # log beside it, as run_cargo keeps them.
    log.parent.mkdir(parents=True, exist_ok=True)
    log.write_text("$ " + " ".join(command) + "\n")
    stdout_log = log.with_name(log.stem + ".stdout" + log.suffix)
    stdout_log.write_text("")
    task = hr.Task(key="engine-suite", expected_s=None,
                   prepare=lambda: (command, suite_env(), str(REPO_ROOT), 6 * 3600),
                   done=done, stderr_path=str(log), tee_path=str(stdout_log))
    hr.run_tasks([task], whole, log=lambda line: print(line, flush=True))
    text = str(out.get("text", ""))
    outcome = out.get("outcome")
    stats = {
        "test_threads": threads_plan.jobs,
        "suite_seconds": getattr(outcome, "wall_s", None),
        "cpu_s": getattr(outcome, "cpu_s", None),
        "peak_rss_mb": getattr(outcome, "peak_rss_mb", None),
        "rerun_uncapped": getattr(outcome, "attempts", 1) > 1,
        "scaling": threads_plan.record(),
    }
    return text, stats


def base_tsv(base_ref: str) -> list[Row] | None:
    proc = subprocess.run(
        ["git", "-C", str(REPO_ROOT), "show", f"{base_ref}:{TSV_REL}"],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        verify = subprocess.run(
            ["git", "-C", str(REPO_ROOT), "rev-parse", "--verify", "--quiet", f"{base_ref}^{{commit}}"],
            capture_output=True,
            text=True,
        )
        if verify.returncode != 0:
            raise GateInputError(f"base ref {base_ref!r} does not resolve (fetch it, or name another)")
        return None
    return parse_tsv(proc.stdout, source=f"{base_ref}:{TSV_REL}")


def git_provenance() -> dict[str, object]:
    def git(*args: str) -> str:
        proc = subprocess.run(["git", "-C", str(REPO_ROOT), *args], capture_output=True, text=True)
        return proc.stdout.strip()

    return {"head": git("rev-parse", "HEAD"), "dirty": bool(git("status", "--porcelain"))}


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--tsv", type=Path, default=DEFAULT_TSV)
    parser.add_argument("--base-ref", default="origin/main", help="ref whose TSV the growth rule compares with")
    parser.add_argument("--report", type=Path, default=DEFAULT_REPORT)
    parser.add_argument(
        "--from-log",
        type=Path,
        help="score a saved full-suite run (pretty libtest output) instead of running the suite; "
        "needs --list-log, and re-runs still execute",
    )
    parser.add_argument("--list-log", type=Path, help="saved `-- --list` output for --from-log")
    parser.add_argument("--validate", action="store_true", help="validate the TSV (and the growth rule) and exit")
    parser.add_argument("--test-threads", default="auto",
                        help="libtest threads for the full run: 'auto' (default) sizes them to the "
                             "measured room (scripts/host_room.py), or a number as an upper bound")
    parser.add_argument("--history", type=Path,
                        help="a prior report of this gate: its peak RSS and CPU size the threads")
    args = parser.parse_args(argv)

    try:
        rows = parse_tsv(args.tsv.read_text(), source=str(args.tsv))
        base_rows = base_tsv(args.base_ref)
        if args.validate:
            growth = [] if base_rows is None else growth_failures(rows, base_rows)
            for line in growth:
                print(f"engine-suite-gate: FAIL: {line}")
            print(f"engine-suite-gate: {len(rows)} rows valid; {len(growth)} growth failures")
            return 1 if growth else 0

        logs = args.report.parent
        targo = None
        scaling_stats: dict[str, object] | None = None
        if args.from_log:
            if not args.list_log:
                raise GateInputError("--from-log needs --list-log")
            suite_text = args.from_log.read_text()
            list_text = args.list_log.read_text()
        else:
            if args.test_threads != "auto" and not (args.test_threads.isdigit() and int(args.test_threads) > 0):
                raise GateInputError("--test-threads must be 'auto' or a positive number")
            history = None
            if args.history is not None:
                try:
                    history = json.loads(args.history.read_text()).get("scaling_stats")
                except (OSError, json.JSONDecodeError):
                    history = None
            targo = resolve_targo()
            # The list run builds the test binary; the suite run below only runs it,
            # so the cap measures the tests, not rustc.
            list_text = run_cargo(targo, ["--list"], logs / "list.log")
            threads_plan = plan_threads(args.test_threads, history)
            if not threads_plan.admitted:
                raise GateInputError(f"host room refused the suite: {threads_plan.reason}")
            suite_text, scaling_stats = run_suite_scaled(targo, threads_plan, logs / "suite.log")
        listed = parse_list(list_text)
        if not listed:
            raise GateInputError("the test list is empty: the suite was not built")
        run = parse_suite(suite_text)

        def rerun_alone(name: str) -> bool:
            nonlocal targo
            if targo is None:
                targo = resolve_targo()
            safe = re.sub(r"[^A-Za-z0-9_.-]", "_", name)
            text = run_cargo(targo, ["--exact", name, "--test-threads", "1"], logs / "reruns" / f"{safe}.log")
            try:
                alone = parse_suite(text)
            except GateInputError:
                return False
            # `--exact` runs every copy of a test listed twice.
            return alone.failed_count == 0 and alone.passed_count >= 1

        decision = decide(rows, base_rows, listed, run, rerun_alone)
    except GateInputError as error:
        print(f"engine-suite-gate: NOT RUN: {error}", file=sys.stderr)
        return 2

    report = {
        "schema": REPORT_SCHEMA,
        "generated": _dt.datetime.now(_dt.timezone.utc).isoformat(),
        "git": git_provenance(),
        "load_average": os.getloadavg(),
        "command": ["targo", *SUITE_ARGS],
        "env": TIMEOUT_ENV,
        "base_ref": args.base_ref,
        "tests": len(listed),
        "passed": run.passed_count,
        "failed": sorted(run.failed),
        "ignored": run.ignored_count,
        "tsv_rows": len(rows),
        "reruns": decision.reruns,
        "failures": decision.failures,
        "reports": decision.reports,
        "verdict": "pass" if decision.ok else "fail",
        "scaling_stats": scaling_stats,
    }
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    for line in decision.reports:
        print(f"engine-suite-gate: report: {line}")
    for line in decision.failures:
        print(f"engine-suite-gate: FAIL: {line}")
    print(
        f"engine-suite-gate: {run.passed_count} passed, {run.failed_count} failed "
        f"({len(rows)} known), {len(decision.failures)} gate failures; report {args.report}"
    )
    return 0 if decision.ok else 1


if __name__ == "__main__":
    sys.exit(main())
