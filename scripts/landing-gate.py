#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""trust-mc's landing gate: select what a change can reach, size it to the host,
reuse what was already judged, and judge the rest exactly as before.

    scripts/landing-gate.py            # plan, then run every selected leg
    scripts/landing-gate.py --plan     # print the selection and the host plan only

1. SELECT (scripts/landing_select.py): the diff from the merge base with
   ``--main`` (default ``origin/main``) to the working tree, mapped through the
   build graph to the legs it can reach. Unmapped paths, build inputs, gate
   scripts and an unreadable graph select everything. Every skipped leg is
   printed with its reason.
2. SCALE (scripts/host_room.py): every leg that starts children sizes them to
   the memory and cores measured at run time; nothing assumes this host.
3. REUSE: a leg whose complete input set (the tracked files that can select
   it, by blob id; the toolchain; the sibling pins; its command line and
   verdict-relevant environment; the merge base for the differential legs)
   already passed is not run again. The dual gate also reuses single driver
   outputs keyed on their complete inputs, so main's side of the side-by-side
   comparison is computed once per main bundle identity and a branch run
   computes only its own side. Nothing is reused from a dirty tree.
4. JUDGE: each leg is the gate it always was. The dual legs add the landing
   convention the commit messages applied by hand: no row gates on the branch
   that does not gate on main; every row in a worse class than main is re-run
   alone on the branch bundle, and must then match main's class or be recorded
   known-red for its class (a missed bug or false certificate worse than main
   fails outright: no re-run excuses it).

Exit 0 when every selected leg passed (or its pass was reused), 1 when one
failed, 2 when the gate could not run. The record (selection, host readings,
every leg's wall time, peak RSS and CPU, and what was reused) is written to
``target/landing-gate/<head>.json``. A development build and a green run are
test evidence, never a verification claim.
"""

from __future__ import annotations

import argparse
import contextlib
import dataclasses
import datetime as _dt
import hashlib
import importlib.util
import json
import locale
import os
import platform
import re
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time
from pathlib import Path
from typing import Any, Callable, Iterator

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
sys.path.insert(0, str(SCRIPTS_DIR))
import host_room  # noqa: E402
import landing_select as sel  # noqa: E402
from ay_cli_build_identity import PROTOCOL as AY_BUILD_PROTOCOL, compiler_identity, digest  # noqa: E402

_SPEC = importlib.util.spec_from_file_location("soundness_dual_gate", SCRIPTS_DIR / "soundness-dual-gate.py")
dual_gate = importlib.util.module_from_spec(_SPEC)
sys.modules["soundness_dual_gate"] = dual_gate
_SPEC.loader.exec_module(dual_gate)

RECORD_SCHEMA = "trust-mc.landing-gate-record/v1"
RESULT_SCHEMA = "trust-mc.landing-gate-result/v1"
# Verdict-relevant inherited environment (the dual gate's list, plus Cargo's).
ENV_PREFIXES = dual_gate.VERDICT_ENV_PREFIXES + ("CARGO_",)
# A rustc job's need. Builds that compile the engine: the measured peak of the
# trust-mc-engine rustc on seal 9192, 4.3 GiB (a property of the workspace, not
# the host). Others: ay's 2 GiB floor. A build whose measured peak per job was
# higher plans with that instead.
HEAVY_BUILD_NEED_MB = 4608
LIGHT_BUILD_NEED_MB = 2048
HEAVY_BUILDS = ("lane-build", "engine-suite", "bundle", "bundle-main")
# One Python unit-test process: measured peaks are well under this.
SCRIPT_TEST_NEED_MB = 512
# One libtest thread of a crate's tests, when nothing measured says more.
TEST_THREAD_NEED_MB = 1024
# Legs whose verdict depends on live remote state: never reused.
LIVE_LEGS = frozenset({"ay-pin", "shared-pins"})


def cache_root() -> Path:
    if os.environ.get("TRUST_MC_LANDING_CACHE"):
        return Path(os.environ["TRUST_MC_LANDING_CACHE"])
    if sys.platform == "darwin":
        return Path.home() / "Library" / "Caches" / "trust-mc-landing"
    return Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache")) / "trust-mc-landing"


CACHE_KEEP_DAYS = 14


def prune_cache(root: Path, keep_days: int = CACHE_KEEP_DAYS) -> int:
    """Delete cache files untouched for ``keep_days`` (a reuse refreshes a
    file's mtime). Pruning only ever costs a re-run, never a verdict."""
    cutoff = time.time() - keep_days * 86400
    removed = 0
    if not root.is_dir():
        return 0
    for path in root.rglob("*.json"):
        try:
            if path.stat().st_mtime < cutoff:
                path.unlink()
                removed += 1
        except OSError:
            continue
    return removed


def utc_now() -> str:
    return _dt.datetime.now(_dt.timezone.utc).replace(microsecond=0).isoformat()


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def git(repo: Path, *args: str, check: bool = True) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=check, capture_output=True,
                          text=True).stdout


# --------------------------------------------------------------------------
# Identities: the complete input set of a leg
# --------------------------------------------------------------------------


def blob_ids(repo: Path, rev: str | None) -> dict[str, str]:
    """path -> blob id at ``rev``, or of the index for the working tree."""
    out = git(repo, "ls-files", "-s", "-z") if rev is None else git(repo, "ls-tree", "-r", "-z", rev)
    ids = {}
    for rec in out.split("\0"):
        if not rec:
            continue
        meta, path = rec.split("\t", 1)
        parts = meta.split()
        ids[path] = parts[1] if rev is None else parts[2]
    return ids


def tree_is_clean(repo: Path) -> bool:
    return not git(repo, "status", "--porcelain", "--untracked-files=normal").strip()


def legs_by_path(ctx: sel.Context, files: list[str]) -> dict[str, set[str] | None]:
    """path -> the legs a change to it would select (None: every leg)."""
    closure_legs: dict[frozenset[str], set[str]] = {}
    out: dict[str, set[str] | None] = {}
    for path in files:
        verdict = sel.classify_path(path, ctx)
        if verdict.everything:
            out[path] = None
            continue
        crates = frozenset(verdict.crates)
        if crates not in closure_legs:
            affected = sel.reverse_closure(ctx.packages, crates)
            closure_legs[crates] = set(sel.legs_for_crates(affected, ctx.packages))
        out[path] = closure_legs[crates] | set(verdict.legs)
    return out


def leg_input_digest(leg: str, by_path: dict[str, set[str] | None], blobs: dict[str, str],
                     exclude_prefix: str | None = None) -> str:
    """Digest of every tracked file whose change would select ``leg``."""
    h = hashlib.sha256()
    for path in sorted(by_path):
        legs = by_path[path]
        if legs is not None and leg not in legs:
            continue
        if exclude_prefix and path.startswith(exclude_prefix):
            continue
        h.update(path.encode() + b"\0" + blobs.get(path, "?").encode() + b"\n")
    return h.hexdigest()


SEAL_STORE = Path.home() / "Library" / "Application Support" / "aterm" / "pkg" / "store" / "trust"


def hold_the_tuple_seal(repo: Path) -> str | None:
    """Pin every leg to the numbered seal tools/tuple.toml names, as the lane
    build requires (CLAUDE.md: "Set TRUST_MC_TRUST_TOOLCHAIN to the numbered
    seal in tools/tuple.toml"): the rustup `trust` toolchain follows the moving
    seal, so a run that spans a seal move would judge two compilers. An explicit
    TRUST_MC_TRUST_TOOLCHAIN wins; a missing seal directory leaves it unset, and
    the legs' own checks (tuple-check) refuse."""
    if os.environ.get("TRUST_MC_TRUST_TOOLCHAIN"):
        return os.environ["TRUST_MC_TRUST_TOOLCHAIN"]
    import tomllib
    try:
        build = tomllib.loads((repo / "tools" / "tuple.toml").read_text()).get("trust", {}).get("build")
    except (OSError, tomllib.TOMLDecodeError):
        return None
    seal = SEAL_STORE / str(build)
    if build is None or not seal.is_dir() or seal.is_symlink():
        return None
    os.environ["TRUST_MC_TRUST_TOOLCHAIN"] = str(seal)
    return str(seal)


def toolchain_identity(repo: Path) -> dict[str, str]:
    try:
        def resolve(name):
            return subprocess.run([str(SCRIPTS_DIR / "resolve-trust-tool.sh"), name], cwd=repo,
                                  check=True, capture_output=True, text=True).stdout.strip()
        sysroot, trustc, targo = resolve("sysroot"), resolve("trustc"), resolve("targo")
        return compiler_identity(sysroot, trustc, targo, targo)["toolchain"]
    except (OSError, ValueError, subprocess.CalledProcessError) as err:
        raise GateError(f"the Trust toolchain cannot be resolved: {err}") from err


def tuple_pins(tree: sel.Tree) -> dict[str, str]:
    import tomllib
    text = tree.read("tools/tuple.toml") or ""
    try:
        data = tomllib.loads(text)
    except tomllib.TOMLDecodeError as err:
        raise GateError(f"tools/tuple.toml does not parse: {err}") from err
    return {"ay": data.get("ay", {}).get("rev", ""), "trust_ir": data.get("trust_ir", {}).get("rev", "")}


def sibling_identity(repo: Path, pins: dict[str, str]) -> dict[str, Any]:
    """The ../ay and ../trust-ir checkouts the [patch] table builds from."""
    out: dict[str, Any] = {}
    for name, key in (("ay", "ay"), ("trust-ir", "trust_ir")):
        path = repo.parent / name
        try:
            head = git(path, "rev-parse", "HEAD").strip()
            status = git(path, "status", "--porcelain", "--untracked-files=normal")
        except subprocess.CalledProcessError:
            out[name] = {"missing": True}
            continue
        entry: dict[str, Any] = {"rev": head}
        if status.strip():
            entry["dirty_sha256"] = sha256_text(status + git(path, "diff"))
        out[name] = entry
        if head != pins.get(key):
            entry["pin_mismatch"] = pins.get(key)
    return out


def pinned_sibling_identity(pins: dict[str, str]) -> dict[str, Any]:
    """The identity the main tree's siblings have once checked out at the pins."""
    return {"ay": {"rev": pins["ay"]}, "trust-ir": {"rev": pins["trust_ir"]}}


def verdict_env() -> dict[str, str]:
    """The inherited environment that can change a verdict, for cache keys. A
    secret-looking name keys by its value's digest: it still changes the key,
    and no secret is written to the cache."""
    out = {}
    for k, v in sorted(os.environ.items()):
        if not k.startswith(ENV_PREFIXES) or k == "CARGO_BUILD_JOBS":
            continue
        out[k] = "sha256:" + sha256_text(v) if dual_gate.SECRET_ENV_RE.search(k) else v
    return out


def gate_only_paths(ctx: sel.Context) -> set[str]:
    """The landing legs' own code that no crate of the bundle reads: it
    selects every leg (a changed judge judges again), but the development
    bundle is not built from it. The dual gate's own code is keyed per driver
    run instead (``entry_cache_key``'s gate digest), and a gate script the
    sources of a crate the bundle reaches name stays a bundle input."""
    feeds_bundle = {crate for crate in ctx.literal_refs
                    if set(sel.DUAL_LEGS) & set(sel.legs_for_crates(sel.reverse_closure(ctx.packages, {crate}),
                                                                    ctx.packages))}
    named = {t for crate in feeds_bundle for t in ctx.literal_refs[crate]}
    return {p for p in ctx.gate_scripts if not any(sel._under(p, t) for t in named)}


def bundle_identity(by_path: dict[str, set[str] | None], blobs: dict[str, str], toolchain: dict[str, str],
                    siblings: dict[str, Any], gate_only: set[str] | frozenset[str] = frozenset()) -> str:
    """What the development bundle is built from: every file that can select a
    dual leg except the dual data (an entry's source is keyed per run) and the
    gate's own code no crate reads (``gate_only_paths``), the toolchain, the
    sibling checkouts and the build command."""
    inputs = {p: v for p, v in by_path.items() if p not in gate_only}
    payload = {
        "inputs": leg_input_digest("dual-chc", inputs, blobs, exclude_prefix=sel.DUALS_DIR)
        + leg_input_digest("dual-bmc", inputs, blobs, exclude_prefix=sel.DUALS_DIR),
        "toolchain": toolchain,
        "siblings": siblings,
        "build": "targo --unverified build-dev",
        "ay_build_protocol": AY_BUILD_PROTOCOL,
        "platform": platform.platform(),
        "env": verdict_env(),
    }
    return sha256_text(json.dumps(payload, sort_keys=True))


def leg_key(leg: str, *, input_digest: str, toolchain: dict[str, str], siblings: dict[str, Any],
            command: list[str], base: str | None, extra: dict[str, Any] | None = None) -> str:
    """The cache key of one leg's verdict. Every element is required: a key
    without one would let a pass stand for inputs it never saw."""
    payload = {
        "schema": RESULT_SCHEMA,
        "leg": leg,
        "inputs": input_digest,
        "toolchain": toolchain,
        "siblings": siblings,
        "command": command,
        "env": verdict_env(),
        "python": sys.version,
        "platform": platform.platform(),
        "base": base,
        "extra": extra or {},
    }
    return sha256_text(json.dumps(payload, sort_keys=True))


class GateError(RuntimeError):
    """The landing gate cannot run (exit 2)."""


_TMP_PATH_RE = re.compile(r"/(?:private/)?(?:var/folders|tmp)/[^\s'\"]*")


def normalize_live_output(text: str, tree: Path) -> list[str]:
    """A pin check's output with the checkout's own paths made generic."""
    for path, token in ((tree.resolve(), "<tree>"), (tree.resolve().parent, "<siblings>"),
                        (tree, "<tree>"), (tree.parent, "<siblings>")):
        text = text.replace(str(path), token)
    return _TMP_PATH_RE.sub("<tmp>", text).splitlines()


def same_live_failure(rc: int, out: str, tree: Path, main_rc: int, main_out: str, main_tree: Path) -> bool:
    """Both failed, with one status and one output: the failure is main's too."""
    return (rc != 0 and rc == main_rc
            and normalize_live_output(out, tree) == normalize_live_output(main_out, main_tree))


def reusable_main_report(report: dict[str, Any], execution: dict[str, Any]) -> bool:
    """Only current compiler/AY-bound reports with no budget-bound runs stand."""
    runs = report.get("runs") or []
    return (report.get("ay_execution") == execution
            and execution.get("protocol") == AY_BUILD_PROTOCOL
            and bool(runs) and all(run.get("budget_bound") is False for run in runs))


# --------------------------------------------------------------------------
# Dual comparison (pure; tested in scripts/test_landing_gate.py)
# --------------------------------------------------------------------------

UNEXCUSABLE = frozenset({"missed-bug", "false-certificate"})


def severity(cls: str) -> int:
    return dual_gate.SEVERITY.index(cls)


def row_id(row: dict[str, Any]) -> tuple[str, str, str]:
    return (row["path"], row["harness"], row["lane"])


def compare_dual(branch_rows: list[dict[str, Any]], main_rows: list[dict[str, Any]]) -> dict[str, list]:
    """Branch rows against main's: ``new_gating`` gates here and not (as
    severely) on main; ``worse`` sits in a more severe class than main (a row
    main lacks counts as main matching); ``better`` improved."""
    main = {row_id(r): r for r in main_rows}
    new_gating, worse, better = [], [], []
    for row in branch_rows:
        m = main.get(row_id(row))
        m_cls = m["class"] if m else "match"
        gating = dual_gate.is_gating(row)
        m_gating = m is not None and dual_gate.is_gating(m)
        if gating and not (m_gating and severity(m_cls) <= severity(row["class"])):
            new_gating.append({"row": row, "main_class": m_cls})
        elif severity(row["class"]) < severity(m_cls):
            worse.append({"row": row, "main_class": m_cls})
        elif severity(row["class"]) > severity(m_cls):
            better.append({"row": row, "main_class": m_cls})
    return {"new_gating": new_gating, "worse": worse, "better": better}


def judge_dual(comparison: dict[str, list], alone: dict[tuple[str, str, str], dict[str, Any]]) -> dict[str, Any]:
    """The landing verdict of one dual lane, given the alone re-runs of every
    flagged row (``alone[row_id] = the row from a run of its file alone``)."""
    failures, resolved, recorded = [], [], []
    for item in comparison["new_gating"] + comparison["worse"]:
        row, m_cls = item["row"], item["main_class"]
        rid = row_id(row)
        label = f"{rid[0]}::{rid[1]} [{rid[2]}] {m_cls} -> {row['class']}"
        if row["class"] in UNEXCUSABLE:
            failures.append(f"{label}: soundness/false-certificate class worse than main (no re-run excuses it)")
            continue
        again = alone.get(rid)
        if again is None:
            failures.append(f"{label}: not re-run alone")
            continue
        if again["class"] in UNEXCUSABLE:
            failures.append(f"{label}: alone -> {again['class']}")
            continue
        if severity(again["class"]) >= severity(m_cls):
            resolved.append(f"{label}: alone {again['class']} (a load flip; matches main's class alone)")
            continue
        if dual_gate.is_gating(again):
            failures.append(f"{label}: alone still {again['class']}, which gates")
            continue
        if again.get("known_red") and again.get("known_red_class") == again["class"]:
            recorded.append(f"{label}: alone still {again['class']}, recorded known-red "
                            f"({again.get('evidence')})")
            continue
        failures.append(f"{label}: alone still {again['class']} and not recorded known-red for that class")
    return {"pass": not failures, "failures": failures, "resolved": resolved, "recorded": recorded}


# --------------------------------------------------------------------------
# Running legs
# --------------------------------------------------------------------------


@dataclasses.dataclass
class LegResult:
    leg: str
    status: str                  # pass | fail | not-run | reused
    wall_s: float = 0.0
    peak_rss_mb: int | None = None
    cpu_s: float | None = None
    key: str | None = None
    detail: list[str] = dataclasses.field(default_factory=list)
    reused_from: dict[str, Any] | None = None


def _request_stop(signum: int, _frame: Any) -> None:
    raise SystemExit(128 + signum)


def _stop_owned_process(proc: subprocess.Popen, grace_s: float = 5.0) -> str | bytes:
    """Let the leg reap its separate-session workers, then bound shutdown.

    Runner created this process group. Keep its leader unreaped until either
    communicate finishes or we kill the group, so escalation cannot target a
    reused process-group id. SIGINT lets the Python pool's finally blocks run.
    """
    if proc.returncode is None:
        try:
            os.killpg(proc.pid, signal.SIGINT)
        except ProcessLookupError:
            pass
    try:
        output, _ = proc.communicate(timeout=grace_s)
    except subprocess.TimeoutExpired:
        if proc.returncode is None:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        output, _ = proc.communicate()
    return output or ""


@contextlib.contextmanager
def _owned_process(argv: list[str], *, cwd: Path, env: dict[str, str], stderr: Any, text: bool = True,
                   interrupted_stdout: Callable[[str], Any] | None = None) -> Iterator[subprocess.Popen]:
    """Own a child session from launch through normal or interrupted reaping.

    Callers choose how stdout and stderr are consumed. Cancellation and the
    launch race stay identical for streamed legs and captured helper output.
    """
    grace_s = host_room.cleanup_grace(default=5.0)
    child_env = host_room.child_cleanup_env(env, grace_s)
    on_main_thread = threading.current_thread() is threading.main_thread()
    launch_complete = [False]
    pending_stop = [None]
    previous_signals = {}

    def request_stop(signum, frame):
        if launch_complete[0]:
            _request_stop(signum, frame)
        else:
            pending_stop[0] = signum

    if on_main_thread:
        for sig in (signal.SIGINT, signal.SIGTERM):
            previous_signals[sig] = signal.signal(sig, request_stop)
    try:
        proc = subprocess.Popen(argv, cwd=str(cwd), env=child_env, stdout=subprocess.PIPE,
                                stderr=stderr, text=text, errors="replace" if text else None,
                                start_new_session=True)
        assert proc.stdout is not None
        try:
            launch_complete[0] = True
            if pending_stop[0] is not None:
                _request_stop(pending_stop[0], None)
            yield proc
            proc.wait()
        except BaseException:
            # Repeated stop requests must not interrupt the bounded reap.
            saved = {}
            if on_main_thread:
                for sig in (signal.SIGINT, signal.SIGTERM):
                    saved[sig] = signal.signal(sig, signal.SIG_IGN)
            try:
                tail = _stop_owned_process(proc, grace_s)
                if interrupted_stdout is not None:
                    interrupted_stdout(tail)
            finally:
                for sig, handler in saved.items():
                    signal.signal(sig, handler)
            raise
        finally:
            proc.stdout.close()
    finally:
        for sig, handler in previous_signals.items():
            signal.signal(sig, handler)


def write_run_record(path: Path, record: dict[str, Any]) -> None:
    """Replace a complete JSON record atomically, retaining the prior one on failure."""
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix=f".{path.name}.", suffix=".tmp", delete=False) as sink:
            temporary = Path(sink.name)
            json.dump(record, sink, indent=2, sort_keys=True)
            sink.write("\n")
        os.replace(temporary, path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)


def checkpoint_run(path: Path, record: dict[str, Any], active_leg: str | None = None) -> None:
    record["verdict"] = "partial-incomplete" if record["partial"] else "incomplete"
    record["updated_at_utc"] = utc_now()
    if active_leg is None:
        record.pop("active_leg", None)
    else:
        record["active_leg"] = active_leg
    write_run_record(path, record)


class Runner:
    def __init__(self, args: argparse.Namespace, repo: Path):
        self.args = args
        self.repo = repo
        self.out_dir = repo / "target" / "landing-gate"
        self.out_dir.mkdir(parents=True, exist_ok=True)
        self.logs = self.out_dir / "logs"
        self.logs.mkdir(exist_ok=True)
        self.cache = cache_root()
        self.python = sys.executable
        self.state: dict[str, Any] = {}

    # -- process helpers ---------------------------------------------------

    def run(self, label: str, argv: list[str], *, env: dict[str, str] | None = None,
            cwd: Path | None = None, quiet: bool = False) -> tuple[int, str]:
        log = self.logs / f"{label}.log"
        print(f"[landing] {label}: $ {' '.join(shlex.quote(a) for a in argv)}", flush=True)
        full_env = dict(os.environ)
        full_env.update(env or {})
        with log.open("w", encoding="utf-8") as sink:
            with _owned_process(argv, cwd=cwd or self.repo, env=full_env, stderr=subprocess.STDOUT,
                                interrupted_stdout=sink.write) as proc:
                lines: list[str] = []
                for line in proc.stdout:
                    sink.write(line)
                    lines.append(line)
                    if not quiet:
                        print(f"  {label}| {line}", end="", flush=True)
        if quiet and proc.returncode != 0:
            for line in lines[-25:]:
                print(f"  {label}| {line}", end="")
        return proc.returncode, "".join(lines)

    def build_needs(self) -> dict[str, int]:
        try:
            return json.loads((self.cache / "build-needs.json").read_text())
        except (OSError, json.JSONDecodeError):
            return {}

    def record_build_need(self, label: str, peak_mb: int | None) -> None:
        """Feed a build's measured peak per job back as its next need."""
        jobs = self.state.get("build_jobs", {}).get(label)
        if not peak_mb or not jobs:
            return
        needs = self.build_needs()
        needs[label] = max(int(needs.get(label, 0)), -(-peak_mb // jobs))
        self.cache.mkdir(parents=True, exist_ok=True)
        (self.cache / "build-needs.json").write_text(json.dumps(needs, indent=1, sort_keys=True))

    def build_jobs(self, label: str = "build") -> str:
        if os.environ.get("CARGO_BUILD_JOBS"):
            return os.environ["CARGO_BUILD_JOBS"]
        default = HEAVY_BUILD_NEED_MB if label in HEAVY_BUILDS else LIGHT_BUILD_NEED_MB
        # History only raises a build's need: a no-op rebuild's small peak must
        # not size the next cold build.
        need = max(default, int(self.build_needs().get(label, 0)))
        plan = host_room.wait_for_plan(need_mb=need, label=f"cargo build ({label})", timing_sensitive=False,
                                       log=lambda line: print(line, flush=True))
        if not plan.admitted:
            raise GateError(f"host room refused a build: {plan.reason}")
        self.state.setdefault("build_jobs", {})[label] = plan.jobs
        return str(plan.jobs)

    def toolchain_env(self, label: str = "build") -> dict[str, str]:
        env = {"CARGO_BUILD_JOBS": self.build_jobs(label)}
        if not os.environ.get("TRUST_MC_TRUST_CHECKOUT") and (Path.home() / "trust").is_dir():
            env["TRUST_MC_TRUST_CHECKOUT"] = str(Path.home() / "trust")
        return env

    def targo(self) -> str:
        return subprocess.run([str(SCRIPTS_DIR / "resolve-trust-tool.sh"), "targo"], cwd=self.repo,
                              check=True, capture_output=True, text=True).stdout.strip()

    # -- the legs ----------------------------------------------------------

    def leg_command(self, leg: str) -> list[str]:
        py = self.python
        # The TSV growth rule reads main's TSV: name main's tip by its sha, so
        # a fetch during the run cannot change what it compares with (the key
        # reads that TSV's blob: key_command).
        main_tip = self.state.get("main_tip", self.args.main)
        if leg == "docs-links":
            return [py, "scripts/check_doc_links.py", "--base", self.state["base"]]
        if leg == "dual-validate":
            return [py, "scripts/soundness-dual-gate.py", "--validate"]
        if leg == "tsv-validate":
            return [py, "scripts/engine-suite-gate.py", "--validate", "--base-ref", main_tip]
        if leg == "lane-port":
            return ["scripts/check-trust-lane-port.sh"]
        if leg == "ay-pin":
            return ["scripts/check-ay-pin.sh"]
        if leg == "shared-pins":
            return ["scripts/check-shared-pins.sh"]
        if leg == "lane-build":
            return ["scripts/check-trust-lane-build.sh"]
        if leg == "engine-suite":
            argv = [py, "scripts/engine-suite-gate.py", "--base-ref", main_tip,
                    "--report", str(self.out_dir / "engine-suite.json")]
            history = self.cache / "engine-suite-last.json"
            return argv + (["--history", str(history)] if history.is_file() else [])
        if leg == "kani-domination-tests":
            return [self.targo(), "--unverified", "test", "--locked", "--manifest-path",
                    "tools/kani-domination/Cargo.toml"]
        if leg == "port-tests":
            return [py, "tools/port/test_trust_only_arms.py"]
        if leg == "kani-spec-tests":
            return [py, "-m", "unittest"]
        if leg == "script-tests":
            return [py, "-m", "unittest", "<each scripts/test_*.py>"]
        if leg.startswith("crate-tests:"):
            return [self.targo(), "--unverified", "test", "--locked", "-p", leg.split(":", 1)[1]]
            # (--test-threads is appended at run time, sized by the host)
        if leg in sel.DUAL_LEGS:
            return [py, "scripts/soundness-dual-gate.py", "--lane", leg.split("-", 1)[1],
                    "--timeout", str(self.args.harness_timeout)]
        raise GateError(f"no command for leg {leg}")

    def leg_cwd(self, leg: str) -> Path:
        if leg == "kani-spec-tests":
            # unittest discovery of tools/kani-spec/tests/test_*.py.
            return self.repo / "tools" / "kani-spec" / "tests"
        return self.repo

    def ensure_pin_siblings(self, tree: Path | None = None) -> list[str]:
        """The pin checks read ../trust-vc and ../clean beside the checkout
        (this one, or the main tree). A missing one is added as a detached
        worktree of ~/<name> at the revision that checkout's tools/tuple.toml
        names (an existing one is left exactly as it is: the checks judge it)."""
        import tomllib
        tree = tree or self.repo
        notes = []
        tuple_ = tomllib.loads((tree / "tools" / "tuple.toml").read_text())
        for name, key in (("trust-vc", "trust_vc"), ("clean", "clean")):
            sib = tree.parent / name
            rev = tuple_.get(key, {}).get("rev")
            source = Path.home() / name
            if sib.exists() or not rev or not (source / ".git").exists():
                continue
            git(source, "worktree", "add", "--detach", str(sib), rev)
            notes.append(f"added {sib} at {rev[:12]} from {source}")
        return notes

    def fetch_locked(self, tree: Path) -> list[str]:
        """Host setup for the live pin checks, which ask Cargo about the locked
        graph offline (`--frozen`). Every package that tree's Cargo.lock names,
        for every platform, must already be in this host's Cargo home, and a
        shared host prunes that cache. So fetch exactly the lockfile's packages
        first: `--locked` re-resolves nothing, and Cargo checks each download
        against the lockfile's checksum. The fetch decides nothing. When it
        fails, the check still runs and reports its own refusal."""
        argv = [self.targo(), "fetch", "--locked", "--manifest-path", str(tree / "Cargo.toml")]
        result = subprocess.run(argv, cwd=tree, capture_output=True, text=True)
        if result.returncode == 0:
            return []
        last = (result.stderr.strip().splitlines() or ["no output"])[-1]
        return [f"locked fetch in {tree} exited {result.returncode}; the check judges what is missing: {last}"]

    def run_leg(self, leg: str) -> LegResult:
        argv = self.leg_command(leg)
        if leg in ("ay-pin", "shared-pins"):
            for note in self.ensure_pin_siblings():
                print(f"[landing] {note}", flush=True)
            for note in self.fetch_locked(self.repo):
                print(f"[landing] {note}", flush=True)
        if leg in sel.DUAL_LEGS:
            return self.run_dual(leg)
        if leg == "script-tests":
            return self.run_script_tests()
        env: dict[str, str] = {}
        cwd = self.leg_cwd(leg)
        if leg in ("lane-build", "engine-suite", "kani-domination-tests") or leg.startswith("crate-tests:"):
            env.update(self.toolchain_env(leg))
            if leg == "lane-build" and "engine-suite" in self.state["selected"]:
                # One engine test binary for the lints and the suite.
                env["TRUST_MC_LANE_LINT_FEATURES"] = "ay,compiler-corpus-tests"
        if leg.startswith("crate-tests:"):
            # libtest's --test-threads outranks the RUST_TEST_THREADS=2 that
            # .cargo/config.toml forces; size it to the host instead.
            plan = host_room.wait_for_plan(need_mb=TEST_THREAD_NEED_MB, label=f"{leg} test threads",
                                           log=lambda line: print(line, flush=True))
            if not plan.admitted:
                return LegResult(leg, "not-run", detail=[plan.reason])
            argv = argv + ["--", "--test-threads", str(plan.jobs)]
        rc, out = self.run(leg.replace(":", "_"), argv, env=env, cwd=cwd,
                           quiet=leg in ("dual-validate", "tsv-validate", "docs-links"))
        if leg == "engine-suite" and rc in (0, 1) and (self.out_dir / "engine-suite.json").is_file():
            shutil.copyfile(self.out_dir / "engine-suite.json", self.cache / "engine-suite-last.json")
        if rc != 0 and leg in LIVE_LEGS:
            return self.live_leg_against_main(leg, argv, rc, out)
        return LegResult(leg, "pass" if rc == 0 else "fail", detail=[f"exit {rc}"])

    def live_leg_against_main(self, leg: str, argv: list[str], rc: int, out: str) -> LegResult:
        """A pin check judges the tree's pins against live remote state (the
        upstream mains), which no change here moves. Its failure is the
        change's unless main's own copy of the check, run now in the main
        worktree with main's pins and siblings, fails with the same status and
        the same output (checkout paths normalized): then upstream moved past
        a pin main shares, and the failure is reported, not failed. A change
        that moves a pin or the exclusions changes the output, so it must pass."""
        tmc = self.ensure_main_tree()
        for note in self.ensure_pin_siblings(tmc):
            print(f"[landing] {note}", flush=True)
        for note in self.fetch_locked(tmc):
            print(f"[landing] {note}", flush=True)
        main_rc, main_out = self.run(f"{leg}-main", argv, cwd=tmc, quiet=True)
        tail = [line for line in out.strip().splitlines()[-3:]]
        if same_live_failure(rc, out, self.repo, main_rc, main_out, tmc):
            return LegResult(leg, "pass", detail=[
                f"exit {rc}, and main's own check exits {main_rc} with the same output: upstream moved past "
                "a pin main shares (reported, not failed)", *tail])
        return LegResult(leg, "fail", detail=[
            f"exit {rc}; main's own check exits {main_rc}"
            + (" with different output" if main_rc != 0 else " (it passes on main)"), *tail])

    def script_test_files(self) -> list[Path]:
        """The scripts/test_*.py files the change can reach
        (``landing_select.script_tests_reached``): all of them when it selects
        everything; otherwise each test whose inputs (its code closure and
        every path that code names) hold a changed path."""
        return [self.repo / rel for rel in self.state["script_tests"]]

    def run_script_tests(self) -> LegResult:
        tests = self.script_test_files()
        if not tests:
            return LegResult("script-tests", "pass", detail=["no test file names a changed script"])
        plan = host_room.wait_for_plan(need_mb=SCRIPT_TEST_NEED_MB, label="script-tests",
                                       log=lambda line: print(line, flush=True))
        if not plan.admitted:
            return LegResult("script-tests", "not-run", detail=[plan.reason])
        failed: dict[str, set[str]] = {}

        def task(path: Path, cwd: Path, sink: dict[str, set[str]], label: str) -> host_room.Task:
            def done(text: str, outcome: host_room.Outcome) -> None:
                (self.logs / f"{label}_{path.stem}.log").write_text(text)
                if outcome.exit_code != 0:
                    sink[path.name] = failing_test_ids(text) or {crash_id(text)}
                status = "ok" if outcome.exit_code == 0 else f"FAILED (exit {outcome.exit_code})"
                print(f"  {label}| {path.name}: {status} in {outcome.wall_s}s", flush=True)
            return host_room.Task(key=path.name, expected_s=None,
                                  prepare=lambda: ([self.python, str(path)], dict(os.environ), str(cwd), 3600),
                                  done=done)

        host_room.run_tasks([task(p, self.repo, failed, "script-tests") for p in tests], plan,
                            log=lambda l: print(l, flush=True))
        detail = [f"{len(tests)} test files"]
        if not failed:
            return LegResult("script-tests", "pass", detail=detail)
        # A failure is the change's only if main's copy of the same file does
        # not fail the same way: run it in the main worktree (main's side).
        # Main's copies run one at a time, and a file failing a test main does
        # not is re-run alone: files running at once can disturb each other
        # through what they share (TMPDIR, the host's load, its timers), and an
        # inflated main set would excuse a real failure. One at a time is how
        # the by-hand protocol ran them.
        alone_plan = dataclasses.replace(plan, jobs=1)
        tmc = self.ensure_main_tree()
        on_main: dict[str, set[str]] = {}
        main_tests = [tmc / "scripts" / name for name in failed if (tmc / "scripts" / name).is_file()]
        host_room.run_tasks([task(p, tmc, on_main, "script-tests-main") for p in main_tests], alone_plan,
                            log=lambda l: print(l, flush=True))
        alone: dict[str, set[str]] = {}
        rerun = [self.repo / "scripts" / name for name in failed if failed[name] - on_main.get(name, set())]
        if rerun:
            sink: dict[str, set[str]] = {}
            host_room.run_tasks([task(p, self.repo, sink, "script-tests-alone") for p in rerun], alone_plan,
                                log=lambda l: print(l, flush=True))
            alone = {p.name: sink.get(p.name, set()) for p in rerun}
        verdict = judge_script_failures(failed, alone, on_main)
        detail += verdict["detail"]
        return LegResult("script-tests", "pass" if verdict["pass"] else "fail", detail=detail)

    # -- the dual legs -------------------------------------------------------

    def pinned_ay_cli(self, tree: Path, label: str) -> Path:
        """scripts/build-pinned-ay-cli.sh in ``tree``: it prints the binary's
        path on stdout (its notes go to stderr, kept in the log)."""
        log = self.logs / f"{label}.log"
        env = dict(os.environ)
        env["CARGO_BUILD_JOBS"] = self.build_jobs(label)
        # Older baseline helpers accept an ambient frontend/compiler override.
        # Give both helpers the held seal, including when they reuse their cache.
        env["TRUST_MC_TARGO"] = self.targo()
        frontend = Path(env["TRUST_MC_TARGO"])
        suffix = ".exe" if frontend.suffix == ".exe" else ""
        env["RUSTC"] = str(frontend.with_name("trustc" + suffix))
        for key in ("RUSTC_WRAPPER", "RUSTC_WORKSPACE_WRAPPER",
                    "CARGO_BUILD_RUSTC_WRAPPER", "CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER"):
            env.pop(key, None)
        # Namespace BOTH sides by the held compiler, including a baseline whose
        # older helper only keys by AY pin. Never reuse its old-seal global cache.
        compiler_key = sha256_text(json.dumps(self.state["toolchain"], sort_keys=True))
        env["TRUST_MC_AY_CLI_CACHE_ROOT"] = str(
            dual_gate.ay_cli_cache_root(env) / f"compiler-{compiler_key}")
        print(f"[landing] {label}: scripts/build-pinned-ay-cli.sh (in {tree})", flush=True)
        with log.open("w", encoding="utf-8") as sink:
            with _owned_process(["scripts/build-pinned-ay-cli.sh"], cwd=tree, env=env, stderr=sink, text=False) as proc:
                stdout, _ = proc.communicate()
        # Decode only after reaping: invalid helper output remains an error,
        # but a decoder exception cannot interrupt ownership of a live child.
        lines = stdout.decode(locale.getpreferredencoding(False)).strip().splitlines()
        if proc.returncode != 0 or not lines:
            raise GateError(f"the pinned ay CLI could not be built (logs/{label}.log)")
        return Path(lines[-1]).parent

    def ensure_ay_cli(self) -> Path:
        if "ay_dir" not in self.state:
            self.state["ay_dir"] = self.pinned_ay_cli(self.repo, "ay-cli")
        return self.state["ay_dir"]

    def ensure_bundle(self, tree: Path, label: str) -> Path:
        key = f"bundle:{tree}"
        if key not in self.state:
            with host_room.TreePeak(os.getpid()) as peak:
                rc, _ = self.run(label, [self.targo(), "--unverified", "build-dev"],
                                 env=self.toolchain_env(label), cwd=tree, quiet=True)
            self.record_build_need(label, peak.peak_mb)
            if rc != 0:
                raise GateError(f"build-dev failed in {tree} (logs/{label}.log)")
            self.state[key] = tree / "target" / "trust-mc"
        return self.state[key]

    def ensure_main_tree(self) -> Path:
        """A persistent, clean worktree of the merge base (and its pinned
        siblings), so main's bundle builds incrementally across landings."""
        root = self.args.main_tree
        base = self.state["base"]
        pins = self.state["main_pins"]
        tmc = root / "trust-mc"
        root.mkdir(parents=True, exist_ok=True)
        if not tmc.exists():
            git(self.repo, "worktree", "add", "--detach", str(tmc), base)
        else:
            if git(tmc, "status", "--porcelain", "--untracked-files=normal").strip():
                raise GateError(f"the main tree {tmc} is dirty; it is the gate's, clean it")
            git(tmc, "checkout", "-q", "--detach", base)
        for name, rev in (("ay", pins["ay"]), ("trust-ir", pins["trust_ir"])):
            sib = root / name
            source = self.repo.parent / name
            if not sib.exists():
                git(source, "worktree", "add", "--detach", str(sib), rev)
            else:
                if git(sib, "status", "--porcelain", "--untracked-files=normal").strip():
                    raise GateError(f"the main tree's {name} checkout {sib} is dirty")
                git(sib, "checkout", "-q", "--detach", rev)
        return tmc

    def dual_report(self, lane: str, *, bundle: Path | None, identity: str, report: Path,
                    history: Path | None, cache_only: bool = False, only: list[str] | None = None,
                    jobs: str = "auto", entry_cache: bool = True) -> tuple[int, dict[str, Any] | None]:
        argv = [self.python, "scripts/soundness-dual-gate.py", "--lane", lane,
                "--timeout", str(self.args.harness_timeout), "--jobs", jobs,
                "--ay-dir", str(self.ensure_ay_cli()), "--report", str(report)]
        if bundle is not None:
            argv += ["--bundle", str(bundle)]
        if entry_cache and not self.args.no_reuse:
            argv += ["--entry-cache", str(self.cache / "dual-entries"), "--bundle-identity", identity]
        if cache_only:
            argv.append("--cache-only")
        if history is not None and history.is_file():
            argv += ["--history", str(history)]
        for token in only or []:
            argv += ["--only", token]
        label = report.stem
        report.parent.mkdir(parents=True, exist_ok=True)
        report.unlink(missing_ok=True)      # a report on disk is this run's or none
        rc, _ = self.run(label, argv, quiet=cache_only or bool(only))
        try:
            return rc, json.loads(report.read_text())
        except (OSError, json.JSONDecodeError):
            return rc, None

    def main_side_own_tree(self, lane: str, report: Path) -> tuple[int, dict[str, Any] | None]:
        # Resolve/validate this exact AY artifact before accepting any cached
        # report, including reports produced by an older baseline helper.
        tmc = self.ensure_main_tree()
        ay_dir = self.pinned_ay_cli(tmc, "ay-cli-main")
        execution = {"protocol": AY_BUILD_PROTOCOL, "toolchain": self.state["toolchain"],
                     "ay_binary_sha256": digest(ay_dir / "ay")}
        if not self.args.no_reuse and report.is_file():
            try:
                prior = json.loads(report.read_text())
            except (OSError, json.JSONDecodeError):
                prior = {}
            if reusable_main_report(prior, execution):
                print(f"[landing] main side ({lane}) reused: {report}", flush=True)
                return 0, prior
            print(f"[landing] main side ({lane}): stale provenance or budget-bound runs, recomputed",
                  flush=True)
        bundle = self.ensure_bundle(tmc, "bundle-main")
        plan = host_room.wait_for_plan(need_mb=host_room.AY_MIN_CAP_MB, label=f"main side {lane} (main's own gate)",
                                       log=lambda line: print(line, flush=True))
        if not plan.admitted:
            raise GateError(f"host room refused main's side: {plan.reason}")
        tmp = report.with_suffix(".partial.json")
        rc, _ = self.run(f"main-own-{lane}", [self.python, "scripts/soundness-dual-gate.py", "--lane", lane,
                                             "--bundle", str(bundle), "--ay-dir", str(ay_dir),
                                             "--jobs", str(plan.jobs), "--timeout", str(self.args.harness_timeout),
                                             "--report", str(tmp)], cwd=tmc, quiet=True)
        try:
            data = json.loads(tmp.read_text())
        except (OSError, json.JSONDecodeError):
            return rc, None
        if rc in (0, 1):
            if toolchain_identity(self.repo) != self.state["toolchain"]:
                raise GateError("the compiler changed during main's AY run")
            data["ay_execution"] = execution
            tmp.write_text(json.dumps(data), encoding="utf-8")
            os.replace(tmp, report)
        return rc, data

    def run_dual(self, leg: str) -> LegResult:
        lane = leg.split("-", 1)[1]
        main_id = self.state["main_bundle_identity"]
        branch_id = self.state["branch_bundle_identity"]
        if self.state["dirty"]:
            raise GateError("the dual legs need a committed tree: their cache keys read blob ids")
        side = self.cache / "main-side"
        side.mkdir(parents=True, exist_ok=True)
        # This run's re-scoring of main's side (per worktree; the reusable part
        # is the entry cache, shared by every worktree).
        main_report = self.out_dir / f"main-{leg}.json"
        if self.state["main_pins"]["ay"] != self.state["head_pins"]["ay"]:
            # The branch moves the ay pin: main's bundle refuses the branch's ay
            # CLI, so main's side is main's own gate, manifest and ay CLI (the
            # by-hand protocol), cached per main bundle identity.
            rc, main = self.main_side_own_tree(lane, side / f"{lane}-{main_id[:20]}-own-tree.json")
        else:
            # Main's side: every driver output is keyed on main's bundle
            # identity, so it is computed once per main tree and re-scored
            # under this branch's manifest. Only a miss needs main's bundle.
            # (The path names where main's bundle lives; a cache-only run starts no driver.)
            main_bundle_path = self.args.main_tree / "trust-mc" / "target" / "trust-mc"
            if self.args.no_reuse:
                rc, main = 3, None
            else:
                rc, main = self.dual_report(lane, bundle=main_bundle_path, identity=main_id,
                                            report=main_report, history=None, cache_only=True)
            if rc == 3:
                tmc = self.ensure_main_tree()
                bundle = self.ensure_bundle(tmc, "bundle-main")
                rc, main = self.dual_report(lane, bundle=bundle, identity=main_id, report=main_report,
                                            history=None)
        if main is None or rc not in (0, 1):
            return LegResult(leg, "not-run", detail=[f"main side did not complete (exit {rc})"])
        if branch_id == main_id:
            bundle = None
            if self.args.no_reuse:
                branch_rc, branch = 3, None
            else:
                branch_rc, branch = self.dual_report(
                    lane, bundle=self.repo / "target" / "trust-mc", identity=branch_id,
                    report=self.out_dir / f"{leg}.json",
                    history=main_report, cache_only=True)
            if branch_rc == 3:
                bundle = self.ensure_bundle(self.repo, "bundle")
                branch_rc, branch = self.dual_report(
                    lane, bundle=bundle, identity=branch_id, report=self.out_dir / f"{leg}.json",
                    history=main_report)
        else:
            bundle = self.ensure_bundle(self.repo, "bundle")
            branch_rc, branch = self.dual_report(lane, bundle=bundle, identity=branch_id,
                                                 report=self.out_dir / f"{leg}.json", history=main_report)
        if branch is None or branch_rc not in (0, 1):
            return LegResult(leg, "not-run", detail=[f"branch side did not complete (exit {branch_rc})"])
        comparison = compare_dual(branch["rows"], main["rows"])
        flagged = comparison["new_gating"] + comparison["worse"]
        alone: dict[tuple[str, str, str], dict[str, Any]] = {}
        files = sorted({item["row"]["path"] for item in flagged if item["row"]["class"] not in UNEXCUSABLE})
        for path in files:
            bundle = bundle or self.ensure_bundle(self.repo, "bundle")
            safe = path.replace("/", "_")
            _, again = self.dual_report(lane, bundle=bundle, identity=branch_id,
                                        report=self.out_dir / "alone" / f"{lane}-{safe}.json",
                                        history=None, only=[path], jobs="1", entry_cache=False)
            for row in (again or {}).get("rows", []):
                if row["path"] == path:
                    alone[row_id(row)] = row
        verdict = judge_dual(comparison, alone)
        detail = [
            f"main: {main['summary']['per_lane'][lane]}",
            f"branch: {branch['summary']['per_lane'][lane]}",
            f"new gating {len(comparison['new_gating'])}, worse {len(comparison['worse'])}, "
            f"better {len(comparison['better'])}; re-run alone: {len(files)} files",
            *verdict["failures"], *verdict["resolved"], *verdict["recorded"],
        ]
        return LegResult(leg, "pass" if verdict["pass"] else "fail", detail=detail)


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0],
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--main", default="origin/main", help="the ref this change lands on")
    parser.add_argument("--main-tree", type=Path, default=Path.home() / ".trust-mc-landing" / "main",
                        help="persistent home of the merge base's worktree and its pinned siblings")
    parser.add_argument("--plan", action="store_true", help="print the selection and plan only")
    parser.add_argument("--legs", nargs="+", help="run only these selected legs (a partial run is "
                        "no landing verdict)")
    parser.add_argument("--no-reuse", action="store_true", help="run every selected leg afresh")
    parser.add_argument("--harness-timeout", type=int, default=30)
    parser.add_argument("--record", type=Path, help="where to write the run record")
    args = parser.parse_args(argv)
    repo = REPO_ROOT
    started = time.monotonic()
    started_utc = utc_now()
    try:
        base = sel.merge_base(repo, args.main, "HEAD")
        head = git(repo, "rev-parse", "HEAD").strip()
        main_tip = git(repo, "rev-parse", args.main).strip()
    except subprocess.CalledProcessError as err:
        print(f"[landing] NOT RUN: cannot resolve {args.main} or the merge base: {err}", file=sys.stderr)
        return 2
    dirty = not tree_is_clean(repo)
    changes = sel.diff_changes(repo, base, None)
    metadata = sel.targo_metadata(repo)
    worktree = sel.Tree(repo, None)
    ctx = sel.build_context(worktree, metadata)
    if metadata is None and ctx.graph_error is None:
        ctx.graph_error = "targo metadata unavailable: the manifests cannot be cross-checked"
    selection = sel.select(changes, ctx, base, head)
    reading = host_room.read_host()
    print(f"[landing] head {head[:12]}{' (dirty)' if dirty else ''}, merge base {base[:12]}, "
          f"{args.main} {main_tip[:12]}")
    if base != main_tip:
        print(f"[landing] NOTE: {args.main} moved past the merge base; merge it and re-run before "
              "pushing (the cache makes the re-run cost only what the merge changed)")
    print("\n".join(selection.report_lines()))
    print(f"[landing] host: {json.dumps(reading.record(), sort_keys=True)}")
    legs = list(selection.selected)
    if args.legs:
        unknown = [leg for leg in args.legs if leg not in legs]
        if unknown:
            print(f"[landing] --legs names legs this change does not select: {unknown}", file=sys.stderr)
            return 2
        legs = [leg for leg in legs if leg in args.legs]
    record: dict[str, Any] = {
        "schema": RECORD_SCHEMA,
        "started_at_utc": started_utc,
        "head": head,
        "dirty": dirty,
        "base": base,
        "main": {"ref": args.main, "tip": main_tip},
        "selection": selection.record(),
        "host_start": reading.record(),
        "partial": bool(args.legs),
        "legs": [],
    }
    record_path = args.record or (repo / "target" / "landing-gate" / f"{head[:12]}.json")
    if args.plan:
        print(f"[landing] plan only: {len(legs)} legs would run")
        return 0

    # Invalidate an older same-head pass before setup or a child can fail.
    checkpoint_run(record_path, record)
    runner = Runner(args, repo)
    share = host_room.adopt_slot_share()
    if share is not None:
        print(f"[landing] inside a build-slot job: at most {share} children of any leg at once "
              "(memory still sizes them)", flush=True)
    seal = hold_the_tuple_seal(repo)
    print(f"[landing] Trust toolchain: {seal or 'rust-toolchain.toml channel (no numbered seal found)'}")
    try:
        toolchain = toolchain_identity(repo)
        head_pins = tuple_pins(sel.Tree(repo, None))
        main_pins = tuple_pins(sel.Tree(repo, base))
        siblings = sibling_identity(repo, head_pins)
    except GateError as err:
        print(f"[landing] NOT RUN: {err}", file=sys.stderr)
        return 2
    files = worktree.files()
    by_path = legs_by_path(ctx, files)
    blobs = blob_ids(repo, None)
    runner.state.update({
        "base": base, "dirty": dirty, "toolchain": toolchain, "main_pins": main_pins, "head_pins": head_pins,
        "everything": bool(selection.everything), "changed_paths": [c.path for c in changes],
        "selected": legs, "main_tip": main_tip,
        "script_tests": sel.script_tests_reached(ctx, changes, worktree) if "script-tests" in legs else [],
    })
    main_tsv_blob = blob_at(repo, main_tip, ENGINE_TSV)
    if any(leg in sel.DUAL_LEGS for leg in legs):
        base_tree = sel.Tree(repo, base)
        base_ctx = sel.build_context(base_tree)
        base_by_path = legs_by_path(base_ctx, base_tree.files())
        runner.state["main_bundle_identity"] = bundle_identity(
            base_by_path, blob_ids(repo, base), toolchain, pinned_sibling_identity(main_pins),
            gate_only_paths(base_ctx))
        runner.state["branch_bundle_identity"] = bundle_identity(by_path, blobs, toolchain, siblings,
                                                                 gate_only_paths(ctx))
        print(f"[landing] bundle identity: main {runner.state['main_bundle_identity'][:16]}, "
              f"branch {runner.state['branch_bundle_identity'][:16]}"
              + (" (same: only changed dual entries run)" if runner.state['main_bundle_identity']
                 == runner.state['branch_bundle_identity'] else ""))

    pruned = prune_cache(runner.cache)
    if pruned:
        print(f"[landing] pruned {pruned} cache files untouched for {CACHE_KEEP_DAYS} days")
    results_dir = runner.cache / "results"
    results_dir.mkdir(parents=True, exist_ok=True)
    overall = "pass"
    with host_room.TreePeak(os.getpid()) as gate_peak:
        for leg in legs:
            checkpoint_run(record_path, record, leg)
            command = runner.leg_command(leg)
            key = None
            if not dirty and leg not in LIVE_LEGS:
                differential = leg in ("docs-links", "tsv-validate", "script-tests", *sel.DUAL_LEGS)
                extra: dict[str, Any] | None = None
                if leg in sel.DUAL_LEGS:
                    extra = {"main_bundle": runner.state.get("main_bundle_identity")}
                elif leg == "script-tests":
                    # Which test files run is part of what a pass covers.
                    extra = {"tests": runner.state["script_tests"]}
                key = leg_key(leg, input_digest=sel_digest(leg, by_path, blobs), toolchain=toolchain,
                              siblings=siblings, command=key_command(command, main_tsv_blob),
                              base=base if differential else None, extra=extra)
                cached = results_dir / f"{key}.json"
                if not args.no_reuse and cached.is_file():
                    prior = json.loads(cached.read_text())
                    os.utime(cached)
                    result = LegResult(leg, "reused", key=key, reused_from=prior,
                                       detail=[f"passed at {prior.get('head', '?')[:12]} on "
                                               f"{prior.get('finished_utc')} with the same inputs"])
                    print(f"[landing] REUSE {leg}: {result.detail[0]}", flush=True)
                    record["legs"].append(dataclasses.asdict(result))
                    checkpoint_run(record_path, record)
                    continue
            t0 = time.monotonic()
            usage0 = resource.getrusage(resource.RUSAGE_CHILDREN)
            with host_room.TreePeak(os.getpid()) as peak:
                try:
                    result = runner.run_leg(leg)
                except GateError as err:
                    result = LegResult(leg, "not-run", detail=[str(err)])
            usage1 = resource.getrusage(resource.RUSAGE_CHILDREN)
            result.wall_s = round(time.monotonic() - t0, 1)
            result.peak_rss_mb = peak.peak_mb
            if result.status in ("pass", "fail") and leg not in sel.DUAL_LEGS:
                runner.record_build_need(leg, peak.peak_mb)
            result.cpu_s = round((usage1.ru_utime - usage0.ru_utime) + (usage1.ru_stime - usage0.ru_stime), 1)
            result.key = key
            print(f"[landing] {result.status.upper()} {leg} in {result.wall_s}s "
                  f"(peak {result.peak_rss_mb} MiB, cpu {result.cpu_s}s)"
                  + "".join(f"\n[landing]   {line}" for line in result.detail[:12]), flush=True)
            record["legs"].append(dataclasses.asdict(result))
            checkpoint_run(record_path, record)
            if result.status == "pass" and key is not None:
                (results_dir / f"{key}.json").write_text(json.dumps({
                    "leg": leg, "head": head, "base": base, "finished_utc": utc_now(),
                    "wall_s": result.wall_s, "peak_rss_mb": result.peak_rss_mb}))
            if result.status == "fail":
                overall = "fail"
            elif result.status == "not-run" and overall == "pass":
                overall = "not-run"
    record["skipped"] = selection.skipped
    record["wall_s"] = round(time.monotonic() - started, 1)
    record["peak_rss_mb"] = gate_peak.peak_mb
    record["host_end"] = host_room.read_host().record()
    record["verdict"] = overall if not args.legs else f"partial-{overall}"
    record.pop("active_leg", None)
    write_run_record(record_path, record)
    ran = sum(1 for leg in record["legs"] if leg["status"] in ("pass", "fail", "not-run"))
    reused = sum(1 for leg in record["legs"] if leg["status"] == "reused")
    print(f"[landing] {record['verdict'].upper()}: {ran} legs ran, {reused} reused, "
          f"{len(selection.skipped)} skipped; wall {record['wall_s']}s, peak RSS {gate_peak.peak_mb} MiB; "
          f"record {record_path}")
    return {"pass": 0, "fail": 1}.get(overall, 2)


# Arguments that name where a leg writes its report or reads scheduling
# history: they cannot change a verdict, and keying on them would make a pass
# in one worktree useless in another.
NON_VERDICT_ARGS = frozenset({"--report", "--history", "--record"})


def key_command(argv: list[str], base_ref_blob: str | None = None) -> list[str]:
    """The verdict-relevant command line. ``base_ref_blob`` replaces the
    ``--base-ref`` revision by what the leg reads at it (the blob id of main's
    TSV): main moving without touching the TSV keeps the key, and the TSV
    moving changes it."""
    out: list[str] = []
    skip = False
    replace = False
    for arg in argv:
        if skip:
            skip = False
            continue
        if replace:
            out.append(f"{ENGINE_TSV}@{base_ref_blob}")
            replace = False
            continue
        if arg in NON_VERDICT_ARGS:
            skip = True
            continue
        out.append(arg)
        if arg == "--base-ref" and base_ref_blob is not None:
            replace = True
    return out


ENGINE_TSV = "tools/engine-suite/known-failures.tsv"


def blob_at(repo: Path, rev: str, path: str) -> str:
    """The blob id of ``path`` at ``rev``, or ``absent``."""
    proc = subprocess.run(["git", "-C", str(repo), "rev-parse", "--verify", "--quiet", f"{rev}:{path}"],
                          capture_output=True, text=True)
    return proc.stdout.strip() if proc.returncode == 0 and proc.stdout.strip() else "absent"


_UNITTEST_FAIL_RE = re.compile(r"^(?:FAIL|ERROR): (\S+) \(([^)]*)\)(?: (.*))?$", re.M)


def failing_test_ids(text: str) -> set[str]:
    """unittest's failing test ids: ``Class.test::name``, with the subTest
    parameters when there are any (two subtests of one test are two ids, so a
    branch failing one main does not fail is a new failure)."""
    return {f"{where}::{name}" + (f" {params.strip()}" if params and params.strip() else "")
            for name, where, params in _UNITTEST_FAIL_RE.findall(text)}


def judge_script_failures(first: dict[str, set[str]], alone: dict[str, set[str]],
                          main: dict[str, set[str]]) -> dict[str, Any]:
    """The script-tests verdict. ``first``: each failing file's failure ids
    in the scaled run; ``alone``: the ids of the files re-run alone (a file
    re-run alone is judged by that run only); ``main``: main's copies' ids,
    run one at a time. A file fails the leg when it fails a test main does
    not."""
    detail: list[str] = []
    ok = True
    for name, ids in sorted(first.items()):
        judged = alone.get(name, ids)
        new = judged - main.get(name, set())
        how = " (alone)" if name in alone else ""
        if new:
            ok = False
            detail.append(f"FAILED {name}{how}: {len(new)} failing here and not on main: {sorted(new)[:5]}")
        elif not judged:
            detail.append(f"{name}: failed beside other files, passes alone (a concurrency flip): reported")
        else:
            detail.append(f"{name}{how}: fails on main too, the same way ({len(judged)}): reported, not failed")
    return {"pass": ok, "detail": detail}


def crash_id(text: str) -> str:
    """A test file that failed without a unittest failure line: keyed by its
    last line (the exception), so main crashing differently is no excuse."""
    lines = [line.strip() for line in text.splitlines() if line.strip()]
    return "<the file failed to run: %s>" % (lines[-1][:200] if lines else "no output")


def sel_digest(leg: str, by_path: dict[str, set[str] | None], blobs: dict[str, str]) -> str:
    if leg == "script-tests":
        # Every path a chosen test reads selects the leg; all of scripts/ is
        # keyed besides (the test files and every helper they can import).
        return leg_input_digest(leg, {p: (v if not p.startswith("scripts/") else None)
                                      for p, v in by_path.items()}, blobs)
    return leg_input_digest(leg, by_path, blobs)


if __name__ == "__main__":
    sys.exit(main())
