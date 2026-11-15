#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unit tests for scripts/host_room.py: the readings, the plan's invariant
(it never oversubscribes), run-time admission, and the scaled runner (caps,
the uncapped re-run, longest-first order).

Tests read the module under test from ``mod``; scripts/test_landing_mutants.py
re-runs them against mutated copies."""

from __future__ import annotations

import importlib.util
import itertools
import math
import os
import sys
import threading
import time
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS = Path(__file__).resolve().parent
_SPEC = importlib.util.spec_from_file_location("host_room", SCRIPTS / "host_room.py")
host_room = importlib.util.module_from_spec(_SPEC)
sys.modules["host_room"] = host_room
_SPEC.loader.exec_module(host_room)

VM_STAT = """Mach Virtual Memory Statistics: (page size of 16384 bytes)
Pages free:                                    94951.
Pages active:                                 537138.
Pages inactive:                               519644.
Pages speculative:                             16067.
Pages throttled:                                   0.
Pages wired down:                             225979.
Pages purgeable:                                2758.
"""


def reading(mod, *, cores=14, phys=24576, avail=13000, load=2.0, pressure="normal"):
    return mod.HostReading(platform="test", logical_cores=cores, physical_cores=cores, physical_mb=phys,
                           available_mb=avail, available_source="test", pressure=pressure, load1=load,
                           taken_at=0.0)


class Readings(unittest.TestCase):
    mod = host_room

    def test_vm_stat_counts_free_speculative_inactive_purgeable(self) -> None:
        pages = 94951 + 519644 + 16067 + 2758
        self.assertEqual(self.mod.parse_vm_stat(VM_STAT), pages * 16384 // (1024 * 1024))

    def test_vm_stat_without_rows_is_unmeasured(self) -> None:
        self.assertIsNone(self.mod.parse_vm_stat("nothing here"))

    def test_meminfo(self) -> None:
        self.assertEqual(self.mod.parse_meminfo("MemTotal: 100 kB\nMemAvailable:   2097152 kB\n"), 2048)
        self.assertIsNone(self.mod.parse_meminfo("MemTotal: 100 kB\n"))

    def test_live_reading_is_complete_here(self) -> None:
        r = self.mod.read_host()
        self.assertGreaterEqual(r.logical_cores, 1)
        self.assertIsNotNone(r.physical_mb)
        self.assertIsNotNone(r.available_mb)


class Plans(unittest.TestCase):
    mod = host_room

    def test_plan_never_oversubscribes(self) -> None:
        grid = itertools.product((4, 14, 64), (8192, 24576, 131072), (0, 1500, 9000, 60000, 120000),
                                 (0.0, 3.0, 30.0), (256, 2048, 4608), (None, 1, 3), (None, 1024, 65536),
                                 (0, 700), (True, False))
        for cores, phys, avail, load, need, max_jobs, ceiling, reserve, timed in grid:
            avail = min(avail, phys)
            p = self.mod.plan(reading(self.mod, cores=cores, phys=phys, avail=avail, load=load), need_mb=need,
                              max_jobs=max_jobs, ceiling_mb=ceiling, reserve_mb=reserve, timing_sensitive=timed)
            with self.subTest(cores=cores, phys=phys, avail=avail, load=load, need=need, max_jobs=max_jobs,
                              ceiling=ceiling, reserve=reserve, timed=timed):
                self.assertTrue(self.mod.plan_is_sound(p), p.log_line("t"))
                if p.admitted:
                    self.assertLessEqual(p.jobs * p.cap_mb, avail)
                    self.assertGreaterEqual(p.cap_mb, need)
                    self.assertLessEqual(p.jobs, p.growth_limit())
                    self.assertLessEqual(p.growth_limit() * p.cap_mb, p.room_mb)

    def test_refuses_only_when_not_one_child_fits(self) -> None:
        phys = 24576
        margin = math.ceil(self.mod.MARGIN_FRACTION * phys)
        fits = self.mod.plan(reading(self.mod, phys=phys, avail=margin + 2048), need_mb=2048)
        self.assertTrue(fits.admitted)
        self.assertEqual(fits.jobs, 1)
        short = self.mod.plan(reading(self.mod, phys=phys, avail=margin + 2047), need_mb=2048)
        self.assertFalse(short.admitted)
        self.assertIn("not even one child fits", short.reason)

    def test_unmeasured_memory_and_critical_pressure_refuse(self) -> None:
        self.assertFalse(self.mod.plan(reading(self.mod, avail=None), need_mb=1).admitted)
        self.assertFalse(self.mod.plan(reading(self.mod, pressure="critical"), need_mb=1).admitted)

    def test_cores_left_by_the_load_bound_jobs(self) -> None:
        idle = self.mod.plan(reading(self.mod, cores=14, load=0.0, avail=200000, phys=262144), need_mb=1024)
        self.assertEqual(idle.jobs, 14)
        busy = self.mod.plan(reading(self.mod, cores=14, load=12.0, avail=200000, phys=262144), need_mb=1024)
        self.assertEqual(busy.jobs, 2)
        saturated = self.mod.plan(reading(self.mod, cores=14, load=40.0, avail=200000, phys=262144), need_mb=1024)
        self.assertEqual(saturated.jobs, 1)
        two_threads = self.mod.plan(reading(self.mod, cores=14, load=0.0, avail=200000, phys=262144),
                                    need_mb=1024, threads_per_child=2.0)
        self.assertEqual(two_threads.jobs, 7)

    def test_a_child_no_timeout_judges_is_bounded_by_memory_alone(self) -> None:
        busy = reading(self.mod, cores=14, load=40.0, avail=200000, phys=262144)
        self.assertEqual(self.mod.plan(busy, need_mb=1024).jobs, 1)
        self.assertEqual(self.mod.plan(busy, need_mb=1024, timing_sensitive=False).jobs, 14)
        tight = reading(self.mod, cores=14, load=40.0, avail=12000, phys=24576)
        p = self.mod.plan(tight, need_mb=4608, timing_sensitive=False)
        self.assertEqual(p.jobs, (12000 - math.ceil(0.12 * 24576)) // 4608)
        self.assertTrue(self.mod.plan_is_sound(p))

    def test_memory_bounds_jobs_and_sizes_caps_into_the_room(self) -> None:
        p = self.mod.plan(reading(self.mod, cores=64, load=0.0, phys=131072, avail=100000), need_mb=4096)
        room = 100000 - math.ceil(self.mod.MARGIN_FRACTION * 131072)
        self.assertEqual(p.jobs, room // 4096)
        self.assertEqual(p.cap_mb, room // p.jobs)

    def test_max_jobs_is_an_upper_bound(self) -> None:
        p = self.mod.plan(reading(self.mod, cores=64, load=0.0, phys=131072, avail=100000), need_mb=1024,
                          max_jobs=3)
        self.assertEqual(p.jobs, 3)

    def test_busy_start_reserves_room_for_the_later_pool(self) -> None:
        p = self.mod.plan(reading(self.mod, cores=28, phys=98304, avail=71000, load=26.78),
                          need_mb=2048, threads_per_child=4, max_jobs=7)
        self.assertEqual(p.jobs, 1)
        self.assertEqual(p.growth_limit(), 7)
        self.assertEqual(p.cap_mb, p.room_mb // 7)
        self.assertTrue(self.mod.launch_admits(p.reading.available_mb, p.margin_mb,
                                             p.cap_mb, p.cap_mb - 1, 1))
        self.assertTrue(self.mod.plan_is_sound(p))
        self.assertEqual(p.record()["growth_jobs"], 7)

    def test_explicit_serial_plan_retains_the_whole_room(self) -> None:
        p = self.mod.plan(reading(self.mod, load=100), need_mb=2048, max_jobs=1)
        self.assertEqual(p.jobs, 1)
        self.assertEqual(p.cap_mb, p.room_mb)
        self.assertEqual(p.growth_limit(), 1)
        self.assertFalse(self.mod.growth_admits(p, 1, 0.0))

    def test_fixed_internal_thread_pool_keeps_its_initial_memory_share(self) -> None:
        p = self.mod.plan(reading(self.mod, cores=28, phys=98304, avail=71000, load=26.78),
                          need_mb=2048, threads_per_child=4, max_jobs=7, reserve_growth=False)
        self.assertEqual(p.jobs, 1)
        self.assertEqual(p.cap_mb, p.room_mb)
        self.assertEqual(p.growth_limit(), 1)
        self.assertFalse(self.mod.growth_admits(p, 1, 0.0))

    def test_serial_whole_suite_reservation_does_not_admit_another_child(self) -> None:
        import dataclasses
        p = self.mod.plan(reading(self.mod, load=0), need_mb=64, max_jobs=3)
        whole = dataclasses.replace(p, jobs=1, cap_mb=p.jobs * p.cap_mb,
                                    need_mb=p.jobs * p.need_mb)
        self.assertEqual(whole.growth_limit(), 1)
        self.assertTrue(self.mod.plan_is_sound(whole))
        self.assertFalse(self.mod.growth_admits(whole, 1, 0.0))

    def test_margin_scales_with_the_host(self) -> None:
        small = self.mod.plan(reading(self.mod, phys=24576, avail=20000), need_mb=1024)
        large = self.mod.plan(reading(self.mod, phys=131072, avail=20000), need_mb=1024)
        self.assertLess(small.margin_mb, large.margin_mb)
        self.assertEqual(small.margin_mb, math.ceil(0.12 * 24576))


class Admission(unittest.TestCase):
    mod = host_room

    def test_waiting_admission_takes_the_first_room_and_gives_up_at_the_deadline(self) -> None:
        readings = iter([reading(self.mod, avail=100), reading(self.mod, avail=100), reading(self.mod, avail=13000)])
        p = self.mod.wait_for_plan(need_mb=2048, label="t", reader=lambda: next(readings), max_wait_s=30,
                                   interval_s=0.01, log=lambda _l: None)
        self.assertTrue(p.admitted)
        p = self.mod.wait_for_plan(need_mb=2048, label="t", reader=lambda: reading(self.mod, avail=100),
                                   max_wait_s=0.05, interval_s=0.01, log=lambda _l: None)
        self.assertFalse(p.admitted)

    def test_a_build_slot_share_bounds_the_children(self) -> None:
        # build-slot -- <gate>: its CARGO_BUILD_JOBS is a share, adopted as a
        # ceiling; memory still sizes the plan under it.
        import os
        saved = {k: os.environ.get(k) for k in ("BUILD_SLOT_HELD", "CARGO_BUILD_JOBS", "HOST_ROOM_SLOT_JOBS")}
        try:
            os.environ.update({"BUILD_SLOT_HELD": "1", "CARGO_BUILD_JOBS": "2"})
            os.environ.pop("HOST_ROOM_SLOT_JOBS", None)
            self.assertEqual(self.mod.adopt_slot_share(), 2)
            self.assertNotIn("CARGO_BUILD_JOBS", os.environ)
            roomy = reading(self.mod, avail=60000, load=0.0)
            p = self.mod.wait_for_plan(need_mb=1024, label="t", reader=lambda: roomy, max_wait_s=0,
                                       log=lambda _l: None, timing_sensitive=False)
            self.assertEqual(p.jobs, 2)
            p = self.mod.wait_for_plan(need_mb=1024, label="t", reader=lambda: roomy, max_wait_s=0,
                                       log=lambda _l: None, max_jobs=1)
            self.assertEqual(p.jobs, 1)
            tight = reading(self.mod, avail=4000, load=0.0)
            p = self.mod.wait_for_plan(need_mb=1024, label="t", reader=lambda: tight, max_wait_s=0,
                                       log=lambda _l: None)
            self.assertEqual(p.jobs, 1, "memory still bounds under the share")
        finally:
            for k, v in saved.items():
                if v is None:
                    os.environ.pop(k, None)
                else:
                    os.environ[k] = v

    def test_one_child_is_always_admitted(self) -> None:
        self.assertTrue(self.mod.launch_admits(None, 1000, 4096, 0, 0))

    def test_running_growth_is_reserved(self) -> None:
        # 10 GiB free less a 2 GiB margin holds a 4 GiB child only while the
        # running children cannot grow by more than 4 GiB.
        self.assertTrue(self.mod.launch_admits(10240, 2048, 4096, 4096, 1))
        self.assertFalse(self.mod.launch_admits(10240, 2048, 4096, 4097, 1))

    def test_unmeasured_memory_admits_nothing_beyond_one(self) -> None:
        self.assertFalse(self.mod.launch_admits(None, 0, 1, 0, 1))


def task(mod, key, argv, expected=None, done=None):
    return mod.Task(key=key, expected_s=expected,
                    prepare=lambda: (argv, None, None, 60),
                    done=done or (lambda _o, _x: None))


class Runner(unittest.TestCase):
    mod = host_room

    def plan(self, jobs=2, cap=10_000):
        p = self.mod.plan(reading(self.mod, cores=64, load=0.0, phys=262144, avail=200000), need_mb=64,
                          max_jobs=jobs)
        import dataclasses
        return dataclasses.replace(p, cap_mb=cap)

    def test_runs_everything_and_reports_output(self) -> None:
        seen = {}
        tasks = [task(self.mod, f"t{i}", [sys.executable, "-c", f"print({i})"],
                      done=lambda out, o, i=i: seen.__setitem__(i, (out.strip(), o.exit_code)))
                 for i in range(5)]
        outcomes = self.mod.run_tasks(tasks, self.plan(jobs=3), log=lambda _l: None, sample_s=0.05)
        self.assertEqual(seen, {i: (str(i), 0) for i in range(5)})
        self.assertEqual(set(outcomes), {f"t{i}" for i in range(5)})

    def test_never_more_than_jobs_at_once(self) -> None:
        live = [0, 0]
        lock = threading.Lock()
        # Each child sleeps; the sampler sees how many groups are alive.
        def sampler(pids):
            with lock:
                live[1] = max(live[1], len(pids))
            return {pid: 1 for pid in pids}
        tasks = [task(self.mod, f"t{i}", [sys.executable, "-c", "import time; time.sleep(0.3)"]) for i in range(6)]
        # Room for everything: only the job count may bound concurrency.
        self.mod.run_tasks(tasks, self.plan(jobs=2), log=lambda _l: None, sample_s=0.02, sampler=sampler,
                           available=lambda: 10 ** 9, pressure_now=lambda: "normal")
        self.assertEqual(live[1], 2)

    def busy_plan(self, max_jobs=None):
        # Started while the load held every core: one child, memory for many.
        return self.mod.plan(reading(self.mod, cores=64, load=64.0, phys=262144, avail=200000), need_mb=64,
                             max_jobs=max_jobs)

    def peak_live(self, plan, load):
        live = [0]
        def sampler(pids):
            live[0] = max(live[0], len(pids))
            return {pid: 1 for pid in pids}
        tasks = [task(self.mod, f"t{i}", [sys.executable, "-c", "import time; time.sleep(0.3)"]) for i in range(6)]
        self.mod.run_tasks(tasks, plan, log=lambda _l: None, sample_s=0.02, sampler=sampler,
                           available=lambda: plan.reading.available_mb,
                           pressure_now=lambda: "normal", load_now=lambda: load,
                           grow_every_s=0.0)
        return live[0]

    def test_a_long_run_grows_into_cores_the_load_frees(self) -> None:
        p = self.busy_plan()
        self.assertEqual(p.jobs, 1)
        self.assertGreater(self.peak_live(p, load=0.0), 1)

    def test_no_growth_while_the_load_holds_the_cores(self) -> None:
        self.assertEqual(self.peak_live(self.busy_plan(), load=64.0), 1)

    def test_growth_stops_at_max_jobs(self) -> None:
        self.assertEqual(self.peak_live(self.busy_plan(max_jobs=2), load=0.0), 2)
        self.assertFalse(self.mod.growth_admits(self.busy_plan(max_jobs=2), 2, 0.0))

    def test_admission_holds_launches_when_the_room_is_gone(self) -> None:
        live = [0]
        def sampler(pids):
            live[0] = max(live[0], len(pids))
            return {pid: 1 for pid in pids}
        tasks = [task(self.mod, f"t{i}", [sys.executable, "-c", "import time; time.sleep(0.2)"]) for i in range(4)]
        # Jobs allow 3, but the re-measured room never fits a second child.
        self.mod.run_tasks(tasks, self.plan(jobs=3), log=lambda _l: None, sample_s=0.02, sampler=sampler,
                           available=lambda: 0, pressure_now=lambda: "normal")
        self.assertEqual(live[0], 1)

    def test_critical_pressure_holds_launches(self) -> None:
        live = [0]
        def sampler(pids):
            live[0] = max(live[0], len(pids))
            return {pid: 1 for pid in pids}
        tasks = [task(self.mod, f"t{i}", [sys.executable, "-c", "import time; time.sleep(0.2)"]) for i in range(4)]
        self.mod.run_tasks(tasks, self.plan(jobs=3), log=lambda _l: None, sample_s=0.02, sampler=sampler,
                           available=lambda: 10 ** 9, pressure_now=lambda: "critical")
        self.assertEqual(live[0], 1)

    def test_a_child_over_its_cap_is_rerun_uncapped_and_scored_once(self) -> None:
        done = []
        caps = []
        def sampler(pids):
            return {pid: 500 for pid in pids}   # every child "holds" 500 MiB
        argv = [sys.executable, "-c", "import time; time.sleep(0.4); print('finished')"]
        t = task(self.mod, "big", argv, done=lambda out, o: (done.append(out.strip()), caps.append(o.cap_mb)))
        outcomes = self.mod.run_tasks([t], self.plan(jobs=1, cap=100), log=lambda _l: None, sample_s=0.02,
                                      sampler=sampler)
        self.assertEqual(done, ["finished"])          # scored once, from the uncapped run
        self.assertEqual(caps, [None])
        self.assertEqual(outcomes["big"].attempts, 2)

    def test_a_task_known_to_outgrow_the_pool_runs_after_it_alone_and_uncapped(self) -> None:
        order, caps = [], {}
        def sampler(pids):
            return {pid: 1 for pid in pids}
        def mark(name):
            return lambda out, o: (order.append(name), caps.__setitem__(name, o.cap_mb))
        argv = [sys.executable, "-c", "import time; time.sleep(0.2)"]
        tasks = [task(self.mod, f"t{i}", argv, done=mark(f"t{i}")) for i in range(3)]
        big = task(self.mod, "big", argv, done=mark("big"))
        big.alone = True
        self.mod.run_tasks([big] + tasks, self.plan(jobs=3), log=lambda _l: None, sample_s=0.02,
                           sampler=sampler, available=lambda: 10 ** 9, pressure_now=lambda: "normal")
        self.assertEqual(order[-1], "big")
        self.assertIsNone(caps["big"])
        self.assertTrue(all(caps[f"t{i}"] is not None for i in range(3)))

    def test_longest_expected_first(self) -> None:
        order = [t.key for t in self.mod.lpt_order([
            task(self.mod, "short", [], expected=1.0), task(self.mod, "unknown", []),
            task(self.mod, "long", [], expected=600.0)])]
        self.assertEqual(order, ["unknown", "long", "short"])

    def test_timeout_is_reported(self) -> None:
        got = []
        t = self.mod.Task(key="slow", expected_s=None,
                          prepare=lambda: ([sys.executable, "-c", "import time; time.sleep(30)"], None, None, 0.3),
                          done=lambda out, o: got.append(o))
        started = time.monotonic()
        self.mod.run_tasks([t], self.plan(jobs=1), log=lambda _l: None, sample_s=0.05)
        self.assertLess(time.monotonic() - started, 10)
        self.assertTrue(got[0].timed_out)
        self.assertIsNone(got[0].exit_code)

    def test_queued_expiration_cannot_signal_after_final_reap(self) -> None:
        reaped, late_signals = set(), []
        real_wait4, real_killpg = os.wait4, os.killpg

        def wait4(pid, options):
            result = real_wait4(pid, options)
            if result[0]:
                reaped.add(pid)
            return result

        def killpg(pid, sig):
            if pid in reaped:
                late_signals.append((pid, sig))
                return
            real_killpg(pid, sig)

        class QueuedExpiration:
            def __init__(self, _seconds, callback):
                self.callback = callback

            def start(self):
                pass

            def cancel(self):
                # A callback already queued when cancel runs must observe the
                # ownership state, not signal the now-reusable process group.
                self.callback()

        with mock.patch.object(self.mod.os, "wait4", side_effect=wait4), \
                mock.patch.object(self.mod.os, "killpg", side_effect=killpg), \
                mock.patch.object(self.mod.threading, "Timer", QueuedExpiration):
            outcomes = self.mod.run_tasks(
                [task(self.mod, "quick", [sys.executable, "-c", "print('done')"])],
                self.plan(jobs=1), log=lambda _line: None,
                sampler=lambda pids: {pid: 1 for pid in pids})
        self.assertTrue(reaped)
        self.assertEqual(late_signals, [])
        self.assertEqual(outcomes["quick"].exit_code, 0)

    def test_failed_exit_notification_reaps_child_and_refuses_result(self) -> None:
        children = []
        real_popen = self.mod.subprocess.Popen

        def popen(*args, **kwargs):
            child = real_popen(*args, **kwargs)
            children.append(child)
            return child

        with mock.patch.object(self.mod.subprocess, "Popen", side_effect=popen), \
                mock.patch.object(self.mod, "_wait_child_exit", side_effect=OSError("fixture notification failure")):
            with self.assertRaisesRegex(RuntimeError, "owned child exit notification"):
                self.mod.run_tasks(
                    [task(self.mod, "slow", [sys.executable, "-c", "import time; time.sleep(30)"])],
                    self.plan(jobs=1), log=lambda _line: None,
                    sampler=lambda pids: {pid: 1 for pid in pids})
        self.assertEqual(len(children), 1)
        self.assertIsNotNone(children[0].returncode)
        with self.assertRaises(ProcessLookupError):
            os.kill(children[0].pid, 0)

    def test_lost_reaping_authority_never_signals_reused_group(self) -> None:
        children, signals = {}, []
        real_popen = self.mod.subprocess.Popen

        def popen(*args, **kwargs):
            child = real_popen(*args, **kwargs)
            children[child.pid] = child
            return child

        def foreign_reap(pid):
            _, status, _ = os.wait4(pid, 0)
            children[pid].returncode = os.waitstatus_to_exitcode(status)
            raise ChildProcessError("fixture foreign reaper")

        with mock.patch.object(self.mod.subprocess, "Popen", side_effect=popen), \
                mock.patch.object(self.mod, "_wait_child_exit", side_effect=foreign_reap), \
                mock.patch.object(self.mod.os, "killpg", side_effect=lambda *args: signals.append(args)):
            with self.assertRaisesRegex(RuntimeError, "owned child exit notification"):
                self.mod.run_tasks(
                    [task(self.mod, "quick", [sys.executable, "-c", "pass"])],
                    self.plan(jobs=1), log=lambda _line: None,
                    sampler=lambda pids: {pid: 1 for pid in pids})
        self.assertEqual(signals, [])
        self.assertEqual(len(children), 1)

    def test_invalid_or_exhausted_cleanup_budget_starts_no_child(self) -> None:
        for value in ("", "nan", "inf", "5", "-1", "0", "0.05", "nonsense"):
            with self.subTest(value=value), \
                    mock.patch.dict(os.environ, {self.mod.CLEANUP_GRACE_ENV: value}), \
                    mock.patch.object(self.mod.subprocess, "Popen") as spawn:
                with self.assertRaises(ValueError):
                    self.mod.run_tasks([task(self.mod, "unused", [])], self.plan(jobs=1))
                spawn.assert_not_called()

    def test_children_receive_smaller_cleanup_budget(self) -> None:
        output = []
        with mock.patch.dict(os.environ, {self.mod.CLEANUP_GRACE_ENV: "0.5"}):
            self.mod.run_tasks(
                [task(self.mod, "budget", [sys.executable, "-c",
                    "import os; print(os.environ['HOST_ROOM_CLEANUP_GRACE_SECONDS'])"],
                    done=lambda text, outcome: output.append(text.strip()))],
                self.plan(jobs=1), log=lambda _line: None,
                sampler=lambda pids: {pid: 1 for pid in pids})
        self.assertEqual(output, ["0.25"])


if __name__ == "__main__":
    unittest.main()
