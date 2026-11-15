#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unit tests for scripts/engine-suite-gate.py: the TSV, libtest parsing, and
the ratchet's rules. Each rule is checked on a run it must fail and on one it
must pass, so a gate that fails everything (or nothing) is caught."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from unittest import mock
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
_SPEC = importlib.util.spec_from_file_location("engine_suite_gate", SCRIPTS / "engine-suite-gate.py")
gate = importlib.util.module_from_spec(_SPEC)
sys.modules["engine_suite_gate"] = gate
_SPEC.loader.exec_module(gate)

HEADER = "test\tclass\tstability\tevidence\tmeasured-at\n"


def tsv(*rows: str) -> list:
    return gate.parse_tsv(HEADER + "".join(r + "\n" for r in rows))


def suite(passed: list[str], failed: list[str], ignored: list[str] = ()) -> str:
    lines = ["", f"running {len(passed) + len(failed) + len(ignored)} tests"]
    lines += [f"test {n} ... ok" for n in passed]
    lines += [f"test {n} ... FAILED" for n in failed]
    lines += [f"test {n} ... ignored" for n in ignored]
    if failed:
        lines += ["", "failures:", ""]
        for n in failed:
            lines += [f"---- {n} stdout ----", "thread panicked", ""]
        lines += ["", "failures:"] + [f"    {n}" for n in failed] + [""]
    verdict = "FAILED" if failed else "ok"
    lines.append(
        f"test result: {verdict}. {len(passed)} passed; {len(failed)} failed; {len(ignored)} ignored; "
        "0 measured; 0 filtered out; finished in 1.00s"
    )
    return "\n".join(lines) + "\n"


def listing(names: list[str]) -> list[str]:
    return gate.parse_list("\n".join(f"{n}: test" for n in names) + f"\n\n{len(names)} tests, 0 benchmarks\n")


def never(_name: str) -> bool:
    raise AssertionError("no re-run expected")


ROW_A = "m::a\tE1\tdeterministic\tz3 by name, refused by the aterm reroute\t2026-10-13 main a3bce3397"
ROW_B_LOAD = "m::b\tS2\tload-dependent\tpasses alone (--test-threads 1); fails inside the suite run at load 30\t2026-10-13"


class ResourcePlanTests(unittest.TestCase):
    def test_fixed_libtest_threads_do_not_reserve_dynamic_pool_growth(self) -> None:
        with mock.patch.object(gate, "_host_room") as get_room:
            get_room.return_value.AY_MIN_CAP_MB = 2048
            gate.plan_threads("auto", None)
            self.assertFalse(get_room.return_value.wait_for_plan.call_args.kwargs["reserve_growth"])


class TsvTests(unittest.TestCase):
    def test_valid_rows_parse(self) -> None:
        rows = tsv(ROW_A, ROW_B_LOAD)
        self.assertEqual([r.test for r in rows], ["m::a", "m::b"])
        self.assertEqual(rows[1].stability, "load-dependent")

    def test_header_is_required(self) -> None:
        with self.assertRaises(gate.GateInputError):
            gate.parse_tsv("name\tclass\n" + ROW_A + "\n")

    def test_bad_class_stability_and_columns_refused(self) -> None:
        for bad in (
            "m::a\tZZ\tdeterministic\tev\t2026",
            "m::a\tE1\tflaky\tev\t2026",
            "m::a\tE1\tdeterministic\tev",
            "m::a\tE1\tdeterministic\t\t2026",
            "m::a\tE1\tdeterministic\tev\t",
        ):
            with self.subTest(bad=bad), self.assertRaises(gate.GateInputError):
                tsv(bad)

    def test_duplicate_refused(self) -> None:
        with self.assertRaises(gate.GateInputError):
            tsv(ROW_A, ROW_A)

    def test_load_dependent_needs_both_outcomes(self) -> None:
        with self.assertRaises(gate.GateInputError):
            tsv("m::b\tS2\tload-dependent\tslow under load\t2026")
        tsv(ROW_B_LOAD)


class ParseTests(unittest.TestCase):
    def test_suite_run_names_failures(self) -> None:
        run = gate.parse_suite(suite(["m::ok"], ["m::a", "m::c"], ["m::i"]))
        self.assertEqual(run.failed, {"m::a", "m::c"})
        self.assertEqual(run.ignored, {"m::i"})
        self.assertEqual((run.passed_count, run.failed_count, run.ignored_count), (1, 2, 1))

    def test_missing_summary_is_not_run(self) -> None:
        text = suite(["m::ok"], ["m::a"])
        truncated = text[: text.index("test result:")]
        with self.assertRaises(gate.GateInputError):
            gate.parse_suite(truncated)

    def test_torn_status_line_is_recovered_from_the_final_list(self) -> None:
        text = suite(["m::ok"], ["m::a"]).replace("test m::a ... FAILED", "test m::a ... child output\nFAILED")
        self.assertEqual(gate.parse_suite(text).failed, {"m::a"})

    def test_count_mismatch_is_not_run(self) -> None:
        text = suite(["m::ok"], ["m::a"]).replace("1 failed", "2 failed")
        with self.assertRaises(gate.GateInputError):
            gate.parse_suite(text)


class DecideTests(unittest.TestCase):
    universe = ["m::a", "m::b", "m::ok", "m::new"]

    def decide(self, rows, failed, rerun=never, base="same", passed=None):
        universe = listing(self.universe)
        if passed is None:
            passed = [n for n in self.universe if n not in failed]
        run = gate.parse_suite(suite(passed, failed))
        base_rows = rows if base == "same" else base
        return gate.decide(rows, base_rows, universe, run, rerun)

    def test_known_failures_pass(self) -> None:
        self.assertTrue(self.decide(tsv(ROW_A, ROW_B_LOAD), ["m::a", "m::b"]).ok)

    def test_deterministic_row_that_passes_fails_the_gate(self) -> None:
        d = self.decide(tsv(ROW_A), [])
        self.assertFalse(d.ok)
        self.assertIn("delete the row", d.failures[0])

    def test_load_dependent_row_that_passes_is_reported(self) -> None:
        d = self.decide(tsv(ROW_A, ROW_B_LOAD), ["m::a"])
        self.assertTrue(d.ok)
        self.assertTrue(any("load-dependent row passed" in r for r in d.reports))

    def test_unlisted_failure_that_fails_alone_fails_the_gate(self) -> None:
        d = self.decide(tsv(ROW_A), ["m::a", "m::new"], rerun=lambda _n: False)
        self.assertFalse(d.ok)
        self.assertEqual(d.reruns, {"m::new": "fail"})

    def test_unlisted_failure_that_passes_alone_is_a_reported_flake(self) -> None:
        d = self.decide(tsv(ROW_A), ["m::a", "m::new"], rerun=lambda _n: True)
        self.assertTrue(d.ok)
        self.assertEqual(d.reruns, {"m::new": "pass"})
        self.assertTrue(any("flake" in r for r in d.reports))

    def test_row_for_a_test_that_does_not_exist_fails(self) -> None:
        rows = tsv(ROW_A, "m::gone\tO\tdeterministic\tev\t2026")
        d = self.decide(rows, ["m::a"])
        self.assertFalse(d.ok)
        self.assertIn("not a test of this suite", d.failures[0])

    def test_growth_against_base_fails(self) -> None:
        d = self.decide(tsv(ROW_A, ROW_B_LOAD), ["m::a", "m::b"], base=tsv(ROW_A))
        self.assertFalse(d.ok)
        self.assertIn("only shrinks", d.failures[0])

    def test_shrink_against_base_passes(self) -> None:
        d = self.decide(tsv(ROW_A), ["m::a"], base=tsv(ROW_A, ROW_B_LOAD))
        self.assertTrue(d.ok)

    def test_relaxing_stability_without_new_evidence_fails(self) -> None:
        base = tsv("m::b\tS2\tdeterministic\tpasses alone; fails in the suite\t2026")
        rows = tsv("m::b\tS2\tload-dependent\tpasses alone; fails in the suite\t2026")
        d = self.decide(rows, ["m::b"], base=base)
        self.assertFalse(d.ok)
        self.assertIn("no new evidence", d.failures[0])

    def test_missing_base_is_reported_not_failed(self) -> None:
        d = self.decide(tsv(ROW_A), ["m::a"], base=None)
        self.assertTrue(d.ok)
        self.assertTrue(any("growth rule" in r for r in d.reports))

    def test_a_test_listed_twice_counts_twice(self) -> None:
        # A test carrying `#[test]` twice is listed and run twice; the run is
        # whole, and the duplicate is reported.
        universe = listing(self.universe + ["m::ok"])
        run = gate.parse_suite(suite(["m::ok", "m::ok", "m::b", "m::new"], ["m::a"]))
        d = gate.decide(tsv(ROW_A), tsv(ROW_A), universe, run, never)
        self.assertTrue(d.ok)
        self.assertTrue(any("m::ok is listed 2 times" in r for r in d.reports))

    def test_incomplete_run_is_refused(self) -> None:
        universe = listing(self.universe + ["m::extra"])
        run = gate.parse_suite(suite(["m::ok", "m::b", "m::new"], ["m::a"]))
        with self.assertRaises(gate.GateInputError):
            gate.decide(tsv(ROW_A), tsv(ROW_A), universe, run, never)


if __name__ == "__main__":
    unittest.main()
