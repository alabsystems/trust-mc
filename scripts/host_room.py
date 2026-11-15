#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""The one host-room helper of trust-mc's gates: measure, then size.

Every gate that starts more than one child (the soundness dual gate's driver
processes, the engine suite's test threads, a cargo build's rustc jobs) asks
this module how many to start and how much memory each may hold, instead of
carrying a constant sized for one host. It reads, at run time:

  * cores: logical (``os.cpu_count``) and physical (``hw.physicalcpu`` on
    macOS, unique (package, core) ids on Linux);
  * physical RAM (``hw.memsize`` / ``SC_PHYS_PAGES``);
  * memory available right now: on macOS ``vm_stat`` free + speculative +
    inactive + purgeable pages (the rule ay's ``scripts/_oom_guard.py``
    states and argues: speculative pages are free pages read ahead into,
    inactive and purgeable are reclaimable, anonymous active pages are not);
    on Linux ``MemAvailable`` from ``/proc/meminfo``;
  * the kernel's memory-pressure state (``kern.memorystatus_vm_pressure_level``
    on macOS: 1 normal, 2 warn, 4 critical; Linux PSI ``full avg10`` >= 60 %
    counts as critical);
  * the 1-minute load average.

From one reading and a workload's measured per-child need it derives a
:class:`Plan`:

    margin  = ceil(MARGIN_FRACTION * physical RAM)   room for peers to grow
    room    = available - margin - reserve           reserve: the parent's own share
    mem_jobs = floor(room / need)
    cpu_jobs = floor(max(1, logical cores - load) / threads_per_child)
               (a child no timeout judges: floor(logical cores / threads_per_child))
    jobs    = min(mem_jobs, cpu_jobs, max_jobs)        at least 1
    capacity = min(mem_jobs, floor(logical cores / threads_per_child), max_jobs)
    cap     = min(ceiling, floor(room / capacity))     never below need

The initial load controls ``jobs``, while the cap reserves room for later
growth into idle cores. Both ``jobs * cap`` and the growth capacity's total
fit within ``room <= available`` (``plan_is_sound``), and
the plan REFUSES only when not even one child of ``need`` fits (``mem_jobs ==
0``) or memory cannot be measured at all, or the kernel already reports
critical pressure. The fraction is the only tuning constant and it is a
fraction: nothing here is sized for one host. ``need`` is the workload's own
measured peak (each gate records its children's peaks and feeds the largest
back in), never a host property.

Fixed internal thread pools set ``reserve_growth=False`` and retain the
original ``cap = room // jobs``; their thread count cannot grow mid-run.

Admission does not replace the existing pressure watches (the driver's
``session/memory.rs`` warnings, ay's in-process RSS guard, the per-child RSS
sampler in the gates): they stay as the backstop for what happens after the
reading.

CLI (for shell gates):

    scripts/host_room.py plan --need-mb 2048 [--threads-per-child 1]
        [--max-jobs N] [--reserve-mb M] [--ceiling-mb C] [--json]
    scripts/host_room.py env --need-mb 2048 ...   # prints JOBS=, CAP_MB=, ...

Exit 0 with a plan, 2 when admission refuses. Every invocation prints (to
stderr) one line with what it measured and what it chose.

Python floor: 3.9 (a bare ``python3`` on macOS), so no PEP 604 at runtime.
"""

from __future__ import annotations

import argparse
import dataclasses
import errno
import json
import math
import os
import queue
import re
import select
import signal
import subprocess
import sys
import threading
import time
from typing import Callable, Dict, List, Optional

# Room for peers (another lane's build, an agent, an editor) to GROW after the
# reading, as a share of physical RAM. A fraction, so it scales with the host:
# 2.9 GiB on 24 GiB, 15.4 GiB on 128 GiB. ay's _oom_guard.py uses the same
# fraction with a 16 GiB floor; a floor sized for a 128 GiB host would leave
# a 24 GiB host no room at all, so this helper has none.
MARGIN_FRACTION = 0.12
# ay's usable minimum per process (trust-mc-driver/src/memory_limit.rs
# MIN_LIMIT_BYTES): below it ay's guard trips before anything is solved. A
# property of the solver, not of the host.
AY_MIN_CAP_MB = 2048

DARWIN_PRESSURE = {1: "normal", 2: "warn", 4: "critical"}
LINUX_PSI_FULL_CRITICAL_PCT = 60.0

AVAILABLE_SOURCE = (
    "vm_stat: Pages free + speculative + inactive + purgeable"
    if sys.platform == "darwin"
    else "/proc/meminfo MemAvailable"
)


@dataclasses.dataclass(frozen=True)
class HostReading:
    """One measurement of the host. ``None`` fields could not be measured."""

    platform: str
    logical_cores: int
    physical_cores: Optional[int]
    physical_mb: Optional[int]
    available_mb: Optional[int]
    available_source: str
    pressure: Optional[str]
    load1: Optional[float]
    taken_at: float

    def record(self) -> Dict[str, object]:
        return dataclasses.asdict(self)


def _run(cmd: List[str]) -> Optional[str]:
    try:
        return subprocess.run(cmd, capture_output=True, text=True, timeout=15, check=True).stdout
    except (OSError, subprocess.SubprocessError):
        return None


def _sysctl_int(name: str) -> Optional[int]:
    out = _run(["sysctl", "-n", name])
    try:
        return int(out.strip()) if out else None
    except ValueError:
        return None


def parse_vm_stat(text: str) -> Optional[int]:
    """Available MiB from ``vm_stat`` output: free + speculative + inactive +
    purgeable pages. ``None`` when no counted row is present."""
    page = 4096
    header = re.search(r"page size of (\d+) bytes", text)
    if header:
        page = int(header.group(1))
    pages = 0
    found = False
    for key in ("Pages free", "Pages inactive", "Pages speculative", "Pages purgeable"):
        row = re.search(r"^%s:\s+(\d+)\." % re.escape(key), text, re.MULTILINE)
        if row:
            pages += int(row.group(1))
            found = True
    return (pages * page) // (1024 * 1024) if found else None


def parse_meminfo(text: str) -> Optional[int]:
    for line in text.splitlines():
        if line.startswith("MemAvailable:"):
            try:
                return int(line.split()[1]) // 1024
            except (IndexError, ValueError):
                return None
    return None


def physical_mb() -> Optional[int]:
    if sys.platform == "darwin":
        total = _sysctl_int("hw.memsize")
        return total // (1024 * 1024) if total else None
    try:
        return (os.sysconf("SC_PAGE_SIZE") * os.sysconf("SC_PHYS_PAGES")) // (1024 * 1024)
    except (OSError, ValueError):
        return None


def available_mb() -> Optional[int]:
    if sys.platform == "darwin":
        out = _run(["vm_stat"])
        return parse_vm_stat(out) if out else None
    try:
        with open("/proc/meminfo", encoding="utf-8") as handle:
            return parse_meminfo(handle.read())
    except OSError:
        return None


def physical_cores() -> Optional[int]:
    if sys.platform == "darwin":
        return _sysctl_int("hw.physicalcpu")
    try:
        with open("/proc/cpuinfo", encoding="utf-8") as handle:
            text = handle.read()
    except OSError:
        return None
    ids = set()
    package = core = None
    for line in text.splitlines() + [""]:
        if line.startswith("physical id"):
            package = line.split(":", 1)[1].strip()
        elif line.startswith("core id"):
            core = line.split(":", 1)[1].strip()
        elif not line.strip():
            if core is not None:
                ids.add((package, core))
            package = core = None
    return len(ids) or None


def pressure() -> Optional[str]:
    if sys.platform == "darwin":
        return DARWIN_PRESSURE.get(_sysctl_int("kern.memorystatus_vm_pressure_level") or -1)
    try:
        with open("/proc/pressure/memory", encoding="utf-8") as handle:
            text = handle.read(4096)
    except OSError:
        return None
    share = re.search(r"^full avg10=([0-9]+(?:\.[0-9]+)?)\b", text, re.MULTILINE)
    if share is None:
        return None
    return "critical" if float(share.group(1)) >= LINUX_PSI_FULL_CRITICAL_PCT else "normal"


def load1() -> Optional[float]:
    try:
        return float(os.getloadavg()[0])
    except OSError:
        return None


def read_host() -> HostReading:
    return HostReading(
        platform=sys.platform,
        logical_cores=os.cpu_count() or 1,
        physical_cores=physical_cores(),
        physical_mb=physical_mb(),
        available_mb=available_mb(),
        available_source=AVAILABLE_SOURCE,
        pressure=pressure(),
        load1=load1(),
        taken_at=time.time(),
    )


def _capacity_jobs(mem_jobs: int, cores: int, threads: float, max_jobs: Optional[int]) -> int:
    bound = min(mem_jobs, max(1, int(math.floor(cores / threads))))
    return bound if max_jobs is None else min(bound, max_jobs)


@dataclasses.dataclass(frozen=True)
class Plan:
    """What a gate may start, derived from one :class:`HostReading`."""

    admitted: bool
    reason: str
    jobs: int
    cap_mb: int
    need_mb: int
    threads_per_child: float
    margin_mb: int
    reserve_mb: int
    room_mb: int
    mem_jobs: int
    cpu_jobs: int
    max_jobs: Optional[int]
    ceiling_mb: Optional[int]
    reading: HostReading
    # Children a wall-clock timeout judges: the load bounds them, at the
    # start (``cpu_jobs``) and again before each launch beyond ``jobs``.
    timing_sensitive: bool = True
    reserve_growth: bool = True

    def growth_limit(self) -> int:
        """Maximum pool width covered by the fixed per-child reservations.

        The room/cap bound also covers callers that deliberately transform
        a multi-thread plan into one larger, serial child.
        """
        if not self.admitted or self.cap_mb <= 0:
            return 0
        if not self.reserve_growth:
            return min(self.jobs, self.room_mb // self.cap_mb)
        return min(_capacity_jobs(self.mem_jobs, self.reading.logical_cores,
                                  self.threads_per_child, self.max_jobs),
                   self.room_mb // self.cap_mb)

    def record(self) -> Dict[str, object]:
        out = dataclasses.asdict(self)
        out["reading"] = self.reading.record()
        out["growth_jobs"] = self.growth_limit()
        out["rule"] = (
            "margin=ceil(%s*physical); room=available-margin-reserve; "
            "jobs=min(floor(room/need), floor(max(1,cores-load1)/threads_per_child), max_jobs); "
            "capacity=min(floor(room/need), floor(cores/threads_per_child), max_jobs); "
            "capacity=jobs when reserve_growth=false; "
            "cap=min(ceiling, floor(room/capacity))" % MARGIN_FRACTION
        )
        return out

    def log_line(self, label: str) -> str:
        r = self.reading
        measured = (
            "cores=%s/%s phys=%sMiB avail=%sMiB pressure=%s load1=%s"
            % (r.logical_cores, r.physical_cores, r.physical_mb, r.available_mb, r.pressure,
               None if r.load1 is None else round(r.load1, 2))
        )
        chosen = (
            "jobs=%d cap=%dMiB need=%dMiB margin=%dMiB reserve=%dMiB room=%dMiB "
            "(mem_jobs=%d cpu_jobs=%d max_jobs=%s growth_jobs=%d)"
            % (self.jobs, self.cap_mb, self.need_mb, self.margin_mb, self.reserve_mb,
               self.room_mb, self.mem_jobs, self.cpu_jobs, self.max_jobs, self.growth_limit())
        )
        verdict = "admitted" if self.admitted else "REFUSED: " + self.reason
        return "[host-room] %s: measured %s; chose %s; %s" % (label, measured, chosen, verdict)


def plan(
    reading: HostReading,
    *,
    need_mb: int,
    threads_per_child: float = 1.0,
    max_jobs: Optional[int] = None,
    reserve_mb: int = 0,
    ceiling_mb: Optional[int] = None,
    timing_sensitive: bool = True,
    reserve_growth: bool = True,
) -> Plan:
    """Size ``jobs`` and the per-child ``cap_mb`` into the measured room.

    Refuses only when memory or physical RAM is unmeasurable, the kernel
    reports critical pressure, or not even one child of ``need_mb`` fits.
    A fixed internal thread pool sets ``reserve_growth=False``: its count
    cannot grow during the run, so its initial children share the whole room.
    """
    if need_mb < 1:
        raise ValueError("need_mb must be positive")
    if threads_per_child <= 0:
        raise ValueError("threads_per_child must be positive")
    if max_jobs is not None and max_jobs < 1:
        raise ValueError("max_jobs must be positive")

    def refuse(reason: str, margin: int = 0, room: int = 0, mem_jobs: int = 0, cpu_jobs: int = 0) -> Plan:
        return Plan(False, reason, 0, 0, need_mb, threads_per_child, margin, reserve_mb, room,
                    mem_jobs, cpu_jobs, max_jobs, ceiling_mb, reading, timing_sensitive, reserve_growth)

    if reading.available_mb is None or reading.physical_mb is None:
        return refuse("available or physical memory could not be measured (%s)" % reading.available_source)
    margin = int(math.ceil(MARGIN_FRACTION * reading.physical_mb))
    room = reading.available_mb - margin - max(0, reserve_mb)
    mem_jobs = max(0, room // need_mb)
    if timing_sensitive:
        # Children whose verdicts carry wall-clock timeouts take only the cores
        # the load leaves idle, so none of them is started onto a core another
        # lane holds.
        busy = reading.load1 if reading.load1 is not None else float(reading.logical_cores)
        cpu_room = max(1.0, reading.logical_cores - busy)
    else:
        # No timeout judges them (a compiler, a unit test with no clock): more
        # of them only share the CPU, so memory alone bounds them.
        cpu_room = float(reading.logical_cores)
    cpu_jobs = max(1, int(math.floor(cpu_room / threads_per_child)))
    if reading.pressure == "critical":
        return refuse("the kernel reports critical memory pressure", margin, room, mem_jobs, cpu_jobs)
    if mem_jobs < 1:
        return refuse(
            "not even one child fits: room %d MiB (available %d - margin %d - reserve %d) < need %d MiB"
            % (room, reading.available_mb, margin, reserve_mb, need_mb),
            margin, room, mem_jobs, cpu_jobs,
        )
    jobs = min(mem_jobs, cpu_jobs)
    if max_jobs is not None:
        jobs = min(jobs, max_jobs)
    jobs = max(1, jobs)
    capacity = (_capacity_jobs(mem_jobs, reading.logical_cores, threads_per_child, max_jobs)
                if reserve_growth else jobs)
    cap = room // capacity
    if ceiling_mb is not None:
        cap = min(cap, ceiling_mb)
    cap = max(cap, need_mb)
    # Size reservations for the maximum possible pool, not the busy host's
    # initial width. Otherwise one initial child reserves the entire room and
    # launch_admits can never fit another after the CPU load falls.
    return Plan(True, "fits", jobs, cap, need_mb, threads_per_child, margin, reserve_mb, room,
                mem_jobs, cpu_jobs, max_jobs, ceiling_mb, reading, timing_sensitive, reserve_growth)


def slot_share(environ: Optional[Dict[str, str]] = None) -> Optional[int]:
    """The CPU share a machine-wide admission gate granted this process tree,
    or ``None`` outside one. ``build-slot -- <cmd>`` (AGENTS.md, "Shared
    machine") runs its child with BUILD_SLOT_HELD=1 and its share as
    CARGO_BUILD_JOBS; a gate that re-plans its builds moves that share to
    HOST_ROOM_SLOT_JOBS (``adopt_slot_share``) so its children still see it.
    The share bounds how many children start; memory still sizes them."""
    env = os.environ if environ is None else environ
    for name in ("HOST_ROOM_SLOT_JOBS",) + (("CARGO_BUILD_JOBS",) if env.get("BUILD_SLOT_HELD") == "1" else ()):
        try:
            n = int(env.get(name, ""))
        except ValueError:
            continue
        if n > 0:
            return n
    return None


def adopt_slot_share(environ: Optional[Dict[str, str]] = None) -> Optional[int]:
    """Inside a build-slot job, turn the CARGO_BUILD_JOBS it injected into
    HOST_ROOM_SLOT_JOBS, a ceiling: an injected CARGO_BUILD_JOBS would
    otherwise read as an explicit job count and skip the memory sizing (seven
    4.5 GiB engine rustc jobs on a 24 GiB host)."""
    env = os.environ if environ is None else environ
    if env.get("BUILD_SLOT_HELD") == "1" and not env.get("HOST_ROOM_SLOT_JOBS"):
        share = slot_share(env)
        if share is not None:
            env["HOST_ROOM_SLOT_JOBS"] = str(share)
            env.pop("CARGO_BUILD_JOBS", None)
    return slot_share(env)


def wait_for_plan(
    *,
    need_mb: int,
    label: str,
    max_wait_s: Optional[float] = None,
    interval_s: float = 15.0,
    reader: Callable[[], HostReading] = None,  # type: ignore[assignment]
    log: Callable[[str], None] = lambda line: print(line, file=sys.stderr, flush=True),
    **kw: object,
) -> Plan:
    """Admission that waits for room instead of failing a busy moment.

    Re-measures every ``interval_s`` (no event announces another lane's memory
    coming free) until a plan is admitted or ``max_wait_s`` passes
    (``HOST_ROOM_WAIT_S``, default 900 s); then returns the refusal. The name
    is outside the TRUST_/AY_/CARGO_ prefixes on purpose: it schedules, it
    cannot change a verdict, so no cache key reads it.
    """
    read = reader or read_host
    share = slot_share()
    if share is not None:
        given = kw.get("max_jobs")
        kw["max_jobs"] = share if given is None else min(int(given), share)  # type: ignore[arg-type]
    if max_wait_s is None:
        try:
            max_wait_s = float(os.environ.get("HOST_ROOM_WAIT_S", "900"))
        except ValueError:
            max_wait_s = 900.0
    deadline = time.monotonic() + max_wait_s
    last_logged = 0.0
    while True:
        p = plan(read(), need_mb=need_mb, **kw)  # type: ignore[arg-type]
        now = time.monotonic()
        if p.admitted or now >= deadline:
            log(p.log_line(label))
            return p
        if now - last_logged >= 60:
            log(p.log_line(label) + "; waiting for room (up to %ds more)" % int(deadline - now))
            last_logged = now
        time.sleep(min(interval_s, max(0.0, deadline - now)))


def plan_is_sound(p: Plan) -> bool:
    """The invariant every admitted plan keeps: it never oversubscribes."""
    if not p.admitted:
        return p.jobs == 0
    r = p.reading
    return (
        p.jobs >= 1
        and p.jobs <= p.growth_limit()
        and p.cap_mb >= p.need_mb
        and p.jobs * p.cap_mb <= p.room_mb
        and r.available_mb is not None
        and p.room_mb <= r.available_mb
        and (p.max_jobs is None or p.jobs <= p.max_jobs)
    )


def launch_admits(available_now_mb: Optional[int], margin_mb: int, cap_mb: int,
                  running_headroom_mb: int, running: int) -> bool:
    """Run-time admission for ONE more child, re-measured before each launch.

    ``running_headroom_mb`` is what the running children may still grow by
    (sum of cap - current RSS). The child fits when the room left after the
    margin covers its cap plus that growth. With nothing running one child is
    always admitted: the plan already refused when not even one fits, and the
    pressure watches are the backstop from there.
    """
    if running == 0:
        return True
    if available_now_mb is None:
        return False
    return available_now_mb - margin_mb >= cap_mb + max(0, running_headroom_mb)


# --------------------------------------------------------------------------
# Process-group RSS (the per-child cap's sampler)
# --------------------------------------------------------------------------


def group_rss_mb(pgids: List[int]) -> Optional[Dict[int, int]]:
    """Resident MiB per process group for ``pgids``, from ONE process walk.

    ``None`` when the walk failed (never zeros: a failed measurement must not
    read as an empty group).
    """
    wanted = set(int(p) for p in pgids)
    totals: Dict[int, int] = {p: 0 for p in wanted}
    if os.path.exists("/proc/self/stat"):
        try:
            page_kb = os.sysconf("SC_PAGE_SIZE") // 1024
            for name in os.listdir("/proc"):
                if not name.isdigit():
                    continue
                try:
                    with open("/proc/%s/stat" % name) as fh:
                        fields = fh.read().rsplit(")", 1)[1].split()
                    pgid = int(fields[2])
                    if pgid not in wanted:
                        continue
                    with open("/proc/%s/statm" % name) as fh:
                        totals[pgid] += int(fh.read().split()[1]) * page_kb
                except (FileNotFoundError, ProcessLookupError, IndexError, ValueError):
                    continue
        except OSError:
            return None
        return {p: kb // 1024 for p, kb in totals.items()}
    out = _run(["ps", "-ax", "-o", "pgid=,rss="])
    if out is None:
        return None
    for line in out.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        try:
            pgid, rss_kb = int(parts[0]), int(parts[1])
        except ValueError:
            continue
        if pgid in wanted:
            totals[pgid] += rss_kb
    return {p: kb // 1024 for p, kb in totals.items()}


def tree_rss_mb(root_pid: int) -> Optional[int]:
    """Resident MiB of ``root_pid`` and every descendant (across sessions and
    process groups), from one ``ps`` walk; ``None`` when the walk failed."""
    out = _run(["ps", "-ax", "-o", "pid=,ppid=,rss="])
    if out is None:
        return None
    children: Dict[int, List[int]] = {}
    rss: Dict[int, int] = {}
    for line in out.splitlines():
        parts = line.split()
        if len(parts) != 3:
            continue
        try:
            pid, ppid, kb = int(parts[0]), int(parts[1]), int(parts[2])
        except ValueError:
            continue
        children.setdefault(ppid, []).append(pid)
        rss[pid] = kb
    total = 0
    stack = [root_pid]
    seen = set()
    while stack:
        pid = stack.pop()
        if pid in seen:
            continue
        seen.add(pid)
        total += rss.get(pid, 0)
        stack.extend(children.get(pid, []))
    return total // 1024


class TreePeak:
    """Samples the RSS of a process tree once per tick until stopped; the
    landing gate's peak-RSS measurement."""

    def __init__(self, root_pid: int, sample_s: float = 1.0):
        self.root_pid = root_pid
        self.sample_s = sample_s
        self.peak_mb = 0
        self.samples = 0
        self.failed = 0
        self._stop = threading.Event()
        self._thread = threading.Thread(target=self._loop, daemon=True)

    def _loop(self) -> None:
        while True:
            mb = tree_rss_mb(self.root_pid)
            if mb is None:
                self.failed += 1
            else:
                self.samples += 1
                self.peak_mb = max(self.peak_mb, mb)
            if self._stop.wait(self.sample_s):
                return

    def __enter__(self) -> "TreePeak":
        self._thread.start()
        return self

    def __exit__(self, *exc: object) -> None:
        self._stop.set()
        self._thread.join()


# --------------------------------------------------------------------------
# The scaled runner: jobs from the plan, a cap per child, admission per launch
# --------------------------------------------------------------------------


@dataclasses.dataclass
class Outcome:
    """How one child ran. ``breached`` children were killed at their cap and
    are re-run uncapped; their output is never scored."""

    exit_code: Optional[int]
    timed_out: bool
    wall_s: float
    cpu_s: Optional[float]
    peak_rss_mb: Optional[int]
    cap_mb: Optional[int]
    breached: bool = False
    attempts: int = 1


@dataclasses.dataclass
class Task:
    """One child. ``prepare`` is called per attempt and returns (argv, env,
    cwd, timeout_s); ``cleanup`` after each attempt; ``done`` once, with the
    output and outcome of the attempt that counts."""

    key: str
    expected_s: Optional[float]
    prepare: Callable[[], tuple]
    done: Callable[[str, Outcome], None]
    cleanup: Callable[[], None] = lambda: None
    # Where the child's stderr goes: None merges it into the output.
    stderr_path: Optional[str] = None
    # A file the output is also appended to as it arrives (progress of a long child).
    tee_path: Optional[str] = None
    # Known (from its own history) to outgrow the pool's cap: run after the
    # pool, alone and uncapped, as a child that crossed its cap is re-run.
    alone: bool = False


class _Running:
    def __init__(self, task: Task, proc: "subprocess.Popen[bytes]", cap_mb: Optional[int],
                 timeout_s: float, started: float, attempt: int):
        self.task = task
        self.proc = proc
        self.cap_mb = cap_mb
        self.timeout_s = timeout_s
        self.started = started
        self.attempt = attempt
        self.chunks: List[bytes] = []
        self.peak_mb: Optional[int] = None
        self.rss_mb = 0
        self.breached = False
        self.timed_out = False
        self.status: Optional[int] = None
        self.cpu_s: Optional[float] = None
        self.ended: Optional[float] = None
        self.reaped = False
        self.wait_error: Optional[BaseException] = None


def _kill_group(pid: int) -> None:
    try:
        os.killpg(pid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def _wait_child_exit(pid: int) -> None:
    """Observe exit without releasing the owned child's PID or process group."""
    if hasattr(os, "waitid"):
        os.waitid(os.P_PID, pid, os.WEXITED | os.WNOWAIT)
        return
    if hasattr(select, "kqueue"):
        # macOS Python exposes wait4 but not waitid. NOTE_EXIT observes the
        # child without reaping it; ESRCH means it exited before registration.
        # This function's caller remains its only reaper in either case.
        events = select.kqueue()
        try:
            try:
                ready = events.control([select.kevent(
                    pid, filter=select.KQ_FILTER_PROC,
                    flags=select.KQ_EV_ADD | select.KQ_EV_ONESHOT,
                    fflags=select.KQ_NOTE_EXIT)], 1, None)
            except ProcessLookupError:
                return
            if ready and ready[0].flags & select.KQ_EV_ERROR:
                if ready[0].data == errno.ESRCH:
                    return
                raise OSError(ready[0].data, "cannot observe owned child exit")
            if (len(ready) != 1 or ready[0].ident != pid
                    or not ready[0].fflags & select.KQ_NOTE_EXIT):
                raise RuntimeError("owned child exit notification was not established")
        finally:
            events.close()
        return
    raise RuntimeError("host-room requires nonreaping child exit notification")


CLEANUP_GRACE_ENV = "HOST_ROOM_CLEANUP_GRACE_SECONDS"
MIN_CLEANUP_GRACE_S = 0.05


def cleanup_grace(environ=None, *, default=4.0) -> float:
    """Bound cooperative nesting; malformed or exhausted budgets refuse work."""
    env = os.environ if environ is None else environ
    if CLEANUP_GRACE_ENV not in env:
        return default
    try:
        seconds = float(env[CLEANUP_GRACE_ENV])
    except (ValueError, TypeError) as error:
        raise ValueError("invalid inherited cleanup grace") from error
    if not math.isfinite(seconds) or not MIN_CLEANUP_GRACE_S < seconds <= 4.0:
        raise ValueError("inherited cleanup grace is exhausted or outside (0.05, 4] seconds")
    return seconds


def child_cleanup_env(environ, grace_s: float) -> dict:
    env = dict(os.environ if environ is None else environ)
    env[CLEANUP_GRACE_ENV] = str(grace_s / 2)
    return env


# A launch beyond the plan's job count waits this long after the previous
# one: the 1-minute load average needs about that long to show a new child,
# so faster growth would overshoot the idle cores it measured.
GROWTH_INTERVAL_S = 60.0


def growth_admits(p: Plan, running: int, load_now: Optional[float]) -> bool:
    """One more timing-sensitive child beyond ``p.jobs``: only while the load,
    re-read now (it counts the children already running), leaves a whole idle
    child's worth of cores, and never past the memory bound or ``max_jobs``.
    The plan sized ``jobs`` from the load when the leg started; other lanes'
    work finishing while a long leg runs frees cores this lets it use."""
    if not p.timing_sensitive or load_now is None:
        return False
    bound = p.growth_limit()
    return running < bound and p.reading.logical_cores - load_now >= p.threads_per_child


def lpt_order(tasks: List[Task]) -> List[Task]:
    """Longest expected first; a task with no history counts as longest."""
    return sorted(tasks, key=lambda t: (-(t.expected_s if t.expected_s is not None else float("inf")), t.key))


def run_tasks(
    tasks: List[Task],
    p: Plan,
    *,
    log: Callable[[str], None] = lambda line: print(line, file=sys.stderr, flush=True),
    sample_s: float = 1.0,
    sampler: Optional[Callable[[List[int]], Optional[Dict[int, int]]]] = None,
    available: Callable[[], Optional[int]] = available_mb,
    pressure_now: Callable[[], Optional[str]] = pressure,
    load_now: Callable[[], Optional[float]] = load1,
    grow_every_s: float = GROWTH_INTERVAL_S,
) -> Dict[str, Outcome]:
    """Run a pool with cooperative TERM handling, also when no Runner owns it."""
    on_main_thread = threading.current_thread() is threading.main_thread()
    requested = [None]
    previous_signals = {}

    def request_stop(signum, _frame):
        # Never unwind Popen before its child is in the ownership inventory.
        requested[0] = signum

    def check_stop():
        if requested[0] is not None:
            raise SystemExit(128 + requested[0])

    if on_main_thread:
        for sig in (signal.SIGINT, signal.SIGTERM):
            previous_signals[sig] = signal.signal(sig, request_stop)
    try:
        return _run_tasks(tasks, p, log=log, sample_s=sample_s, sampler=sampler,
                          available=available, pressure_now=pressure_now,
                          load_now=load_now, grow_every_s=grow_every_s, check_stop=check_stop)
    finally:
        for sig, handler in previous_signals.items():
            signal.signal(sig, handler)


def _run_tasks(
    tasks: List[Task],
    p: Plan,
    *,
    log: Callable[[str], None],
    sample_s: float,
    sampler: Optional[Callable[[List[int]], Optional[Dict[int, int]]]],
    available: Callable[[], Optional[int]],
    pressure_now: Callable[[], Optional[str]],
    load_now: Callable[[], Optional[float]],
    grow_every_s: float,
    check_stop: Callable[[], None],
) -> Dict[str, Outcome]:
    """Run ``tasks`` under plan ``p``: at most ``p.jobs`` at once, longest
    expected first, each capped at ``p.cap_mb`` by a process-group RSS sampler
    (one process walk per tick for every child). A launch waits for an event (a
    child exiting, or the sampler's tick) until the re-measured room admits it
    (``launch_admits``) and the kernel is not at critical pressure. A child that
    crosses its cap is killed and re-run after the capped phase, alone and
    uncapped, so every scored verdict comes from a run no cap of this runner
    cut short: the caps change when work runs, never what it judges.
    """
    if not p.admitted:
        raise ValueError("run_tasks needs an admitted plan")
    if not hasattr(os, "waitid") and not hasattr(select, "kqueue"):
        raise RuntimeError("host-room requires nonreaping child exit notification")
    grace_s = cleanup_grace()
    sample = sampler or group_rss_mb
    pending: List[Task] = lpt_order([t for t in tasks if not t.alone])
    requeue: List[Task] = [t for t in tasks if t.alone]
    planned_alone = len(requeue)
    outcomes: Dict[str, Outcome] = {}
    running: Dict[int, _Running] = {}
    waiters: List[threading.Thread] = []
    finished: "queue.Queue[_Running]" = queue.Queue()
    cond = threading.Condition()
    stop = threading.Event()
    unmeasured = [0]
    max_running = [0]
    last_growth = [time.monotonic()]

    def launch(task: Task, cap: Optional[int], attempt: int) -> None:
        argv, env, cwd, timeout_s = task.prepare()
        if task.stderr_path is None:
            err_sink = subprocess.STDOUT
        else:
            err_sink = open(task.stderr_path, "ab")  # noqa: SIM115 - closed below, once the child has it
        try:
            proc = subprocess.Popen(argv, cwd=cwd, env=child_cleanup_env(env, grace_s), stdout=subprocess.PIPE,
                                    stderr=err_sink, start_new_session=True)
        finally:
            if task.stderr_path is not None:
                err_sink.close()
        run = _Running(task, proc, cap, float(timeout_s), time.monotonic(), attempt)

        def read() -> None:
            assert proc.stdout is not None
            tee = open(task.tee_path, "ab") if task.tee_path else None  # noqa: SIM115
            try:
                with proc.stdout:
                    for chunk in iter(lambda: proc.stdout.read1(65536), b""):
                        run.chunks.append(chunk)
                        if tee is not None:
                            tee.write(chunk)
                            tee.flush()
            finally:
                if tee is not None:
                    tee.close()

        def expire() -> None:
            with cond:
                if not run.reaped:
                    run.timed_out = True
                    _kill_group(proc.pid)

        def wait() -> None:
            timer = threading.Timer(run.timeout_s, expire)
            timer.daemon = True
            timer.start()
            try:
                _wait_child_exit(proc.pid)
                # Timers, cancellation and the sampler use this same lock.
                # No signal may follow the final wait4 that releases the PID.
                with cond:
                    _kill_group(proc.pid)
                    try:
                        _, status, usage = os.wait4(proc.pid, 0)
                    finally:
                        run.reaped = True
                    proc.returncode = os.waitstatus_to_exitcode(status)
                    run.status = proc.returncode
                    run.cpu_s = round(usage.ru_utime + usage.ru_stime, 2)
            except BaseException as error:
                run.wait_error = error
                with cond:
                    if not run.reaped:
                        try:
                            # The observer never reaps. A registration failure
                            # therefore retains ownership, unlike ECHILD. Kill
                            # the group before releasing even an exited leader:
                            # a descendant may still hold our output pipe.
                            if not isinstance(error, ChildProcessError):
                                _kill_group(proc.pid)
                            _, status, _ = os.wait4(proc.pid, 0)
                            proc.returncode = os.waitstatus_to_exitcode(status)
                        except ChildProcessError:
                            # Another reaper makes identity uncertain: no signal.
                            pass
                        finally:
                            run.reaped = True
            finally:
                timer.cancel()
            run.ended = time.monotonic()
            reader.join()
            with cond:
                running.pop(proc.pid, None)
                finished.put(run)
                cond.notify_all()

        reader = threading.Thread(target=read, daemon=True)
        reader.start()
        with cond:
            running[proc.pid] = run
            max_running[0] = max(max_running[0], len(running))
        waiter = threading.Thread(target=wait, daemon=True)
        waiters.append(waiter)
        waiter.start()

    def sample_loop() -> None:
        while not stop.wait(sample_s):
            with cond:
                pids = list(running)
            if pids:
                rss = sample(pids)
                with cond:
                    if rss is None:
                        unmeasured[0] += 1
                    else:
                        for pid, run in running.items():
                            mb = rss.get(pid, 0)
                            run.rss_mb = mb
                            run.peak_mb = mb if run.peak_mb is None else max(run.peak_mb, mb)
                            if (not run.reaped and run.cap_mb is not None
                                    and mb > run.cap_mb and not run.breached):
                                run.breached = True
                                _kill_group(pid)
            with cond:
                cond.notify_all()

    def finish(run: _Running) -> None:
        if run.wait_error is not None:
            raise RuntimeError("host-room lost its owned child exit notification") from run.wait_error
        output = b"".join(run.chunks).decode("utf-8", "replace")
        outcome = Outcome(
            exit_code=None if (run.timed_out or run.breached) else run.status,
            timed_out=run.timed_out and not run.breached,
            wall_s=round((run.ended or time.monotonic()) - run.started, 1),
            cpu_s=run.cpu_s,
            peak_rss_mb=run.peak_mb,
            cap_mb=run.cap_mb,
            breached=run.breached,
            attempts=run.attempt,
        )
        run.task.cleanup()
        outcomes[run.task.key] = outcome
        if run.breached:
            log("[host-room] %s crossed its %d MiB cap (peak %s MiB): re-run uncapped after the capped phase"
                % (run.task.key, run.cap_mb or 0, run.peak_mb))
            requeue.append(run.task)
            return
        run.task.done(output, outcome)

    def drain() -> None:
        while True:
            try:
                finish(finished.get_nowait())
            except queue.Empty:
                return

    sampler_thread = threading.Thread(target=sample_loop, daemon=True)
    sampler_thread.start()
    try:
        while True:
            check_stop()
            drain()
            with cond:
                n_running = len(running)
                headroom = sum(max(0, p.cap_mb - r.rss_mb) for r in running.values())
            if not pending and n_running == 0 and finished.empty():
                break
            grow = (pending and n_running >= p.jobs
                    and time.monotonic() - last_growth[0] >= grow_every_s
                    and growth_admits(p, n_running, load_now()))
            if pending and (n_running < p.jobs or grow):
                ok = n_running == 0 or (
                    launch_admits(available(), p.margin_mb, p.cap_mb, headroom, n_running)
                    and pressure_now() != "critical"
                )
                if ok:
                    if n_running >= p.jobs:
                        last_growth[0] = time.monotonic()
                    launch(pending.pop(0), p.cap_mb, 1)
                    continue
            with cond:
                if finished.empty():
                    cond.wait(timeout=sample_s)
        # Capped-out children: alone, uncapped, as the gate ran before.
        for task in requeue:
            check_stop()
            log("[host-room] %s %s alone without a cap"
                % ("running" if task.alone else "re-running", task.key))
            launch(task, None, 1 if task.alone else 2)
            while True:
                check_stop()
                try:
                    completed = finished.get(timeout=sample_s)
                except queue.Empty:
                    continue
                finish(completed)
                break
    finally:
        stop.set()
        saved_signals = {}
        if threading.current_thread() is threading.main_thread():
            for sig in (signal.SIGINT, signal.SIGTERM):
                saved_signals[sig] = signal.signal(sig, signal.SIG_IGN)
        try:
            with cond:
                for pid, run in running.items():
                    if not run.reaped:
                        try:
                            os.killpg(pid, signal.SIGINT)
                        except ProcessLookupError:
                            pass
                deadline = time.monotonic() + grace_s
                while any(not run.reaped for run in running.values()):
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        break
                    cond.wait(timeout=remaining)
                for pid, run in running.items():
                    if not run.reaped:
                        _kill_group(pid)
            # Waiters reap owned leaders. Cooperative nested pools use smaller
            # budgets; arbitrarily stopped descendants are outside this scope.
            for waiter in waiters:
                waiter.join()
            sampler_thread.join()
        finally:
            for sig, handler in saved_signals.items():
                signal.signal(sig, handler)
    check_stop()
    if unmeasured[0]:
        log("[host-room] RSS could not be measured on %d sampler ticks: caps were not enforced then"
            % unmeasured[0])
    log("[host-room] ran %d tasks, at most %d at once (plan: %d), %d alone and uncapped "
        "(%d by their history, %d after crossing the cap)"
        % (len(tasks), max_running[0], p.jobs, len(requeue), planned_alone, len(requeue) - planned_alone))
    return outcomes


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = parser.add_subparsers(dest="command", required=True)
    for name in ("plan", "env", "measure"):
        p = sub.add_parser(name)
        if name == "measure":
            continue
        p.add_argument("--need-mb", type=int, required=True, help="measured per-child peak, MiB")
        p.add_argument("--threads-per-child", type=float, default=1.0)
        p.add_argument("--max-jobs", type=int)
        p.add_argument("--reserve-mb", type=int, default=0)
        p.add_argument("--ceiling-mb", type=int)
        p.add_argument("--not-timing-sensitive", action="store_true",
                       help="the children carry no wall-clock timeout (a build): load does not bound them")
        p.add_argument("--label", default="gate")
        p.add_argument("--json", action="store_true")
    return parser


def main(argv: Optional[List[str]] = None, reader: Callable[[], HostReading] = read_host) -> int:
    args = _parser().parse_args(argv)
    if args.command == "measure":
        print(json.dumps(reader().record(), indent=2, sort_keys=True))
        return 0
    p = wait_for_plan(need_mb=args.need_mb, label=args.label, reader=reader,
                      threads_per_child=args.threads_per_child, max_jobs=args.max_jobs,
                      reserve_mb=args.reserve_mb, ceiling_mb=args.ceiling_mb,
                      timing_sensitive=not args.not_timing_sensitive)
    if args.command == "env":
        print("HOST_ROOM_ADMITTED=%d" % (1 if p.admitted else 0))
        print("HOST_ROOM_JOBS=%d" % p.jobs)
        print("HOST_ROOM_CAP_MB=%d" % p.cap_mb)
        print("HOST_ROOM_MARGIN_MB=%d" % p.margin_mb)
    elif args.json:
        print(json.dumps(p.record(), indent=2, sort_keys=True))
    else:
        print(p.jobs)
    return 0 if p.admitted else 2


if __name__ == "__main__":
    sys.exit(main())
