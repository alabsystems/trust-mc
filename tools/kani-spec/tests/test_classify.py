# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Classification must not move a verdict-bearing unit out of verdict-spec on a no-op flag."""
import unittest

from fixture import TOOL_DIR  # noqa: F401
from kani_spec.classify import classify, expected_features


def ctx(rel, suite="expected", mode="expected", flags="", cbmc_flags=(), expected=None, verdict=None):
    expd = expected_features(expected)
    if expd is not None:
        expd["verdict"] = verdict
    return {"rel": rel, "suite": suite, "mode": mode, "flags": flags, "src": "", "exp": expected, "expd": expd,
            "script": "", "cbmc_flags": list(cbmc_flags), "stage": None, "ext_deps": 0, "workspace": False,
            "has_c_files": False, "path": rel, "unit": "single-file"}


class ClassifyTests(unittest.TestCase):
    def test_default_output_format_keeps_a_verdict_unit_in_verdict_spec(self):
        c = ctx("src/getting-started/verification-results/failure_example.expected", suite="kani-docs",
                mode="cargo-kani", flags="--output-format regular",
                expected='FAILURE\\\nDescription: "assertion failed: arr.len() != 3"\n', verdict="FAIL")
        self.assertEqual(classify(c)[0], "verdict-spec")
        c = ctx("assert-reach/test.expected", suite="cargo-kani", mode="cargo-kani", flags="--output-format=regular",
                expected='UNREACHABLE\\\nDescription: "assertion failed: z == x - 1"\n')
        self.assertEqual(classify(c)[0], "verdict-spec")

    def test_output_format_tests_and_other_formats_stay_cli_surface(self):
        self.assertEqual(classify(ctx("regular-output-format-fail/fail.rs", suite="ui",
                                      flags="--output-format regular"))[0], "cli-surface")
        self.assertEqual(classify(ctx("assert-location/assert-false/main.rs", flags="--output-format old"))[0],
                         "cli-surface")

    def test_kani_native_cbmc_checks_are_not_cbmc_specific(self):
        c = ctx("array/main.rs", cbmc_flags=["--bounds-check"],
                expected="FAILURE\\\nindex out of bounds: the length is less than or equal to the given index\n",
                verdict="FAIL")
        self.assertEqual(classify(c)[0], "verdict-spec")
        c = ctx("Count/Unstable/Ctlz/bounds.rs", suite="kani", mode="kani", cbmc_flags=["--pointer-check"])
        self.assertEqual(classify(c)[0], "verdict-spec")

    def test_cbmc_native_instrumentation_stays_cbmc_specific(self):
        c = ctx("overflow/check_message.rs", suite="ui", cbmc_flags=["--unsigned-overflow-check"])
        self.assertEqual(classify(c)[0], "cbmc-specific")
        c = ctx("x/main.rs", cbmc_flags=["--bounds-check", "--float-overflow-check"])
        self.assertEqual(classify(c)[0], "cbmc-specific")


if __name__ == "__main__":
    unittest.main()
