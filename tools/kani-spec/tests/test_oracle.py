# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
import unittest

from fixture import TOOL_DIR  # noqa: F401
from kani_spec.oracle import build_oracle, contains_blocks, parse_expected
from kani_spec.overlay import effective_oracle_fields, legacy_expected_verdict


def unit(mode="expected", harnesses=(), step=None, should_fail=False, ignored=None, exit_code=0):
    return {
        "id": "suite/x.rs", "suite": "suite", "mode": mode, "ignored": ignored, "should_fail": should_fail,
        "expected_path": "tests/suite/x.expected",
        "directives": {"kani_fail_step": step, "kani_flags": [], "compile_flags": [], "cbmc_flags": []},
        "harnesses": [{"name": n.split("::")[-1], "pretty_name": n, "should_panic": sp, "kind": "proof",
                       "macro_template": False, "selected": True} for n, sp in harnesses],
        "exec": {"exit_code": exit_code},
    }


class ContainsLinesTests(unittest.TestCase):
    def test_backslash_joins_consecutive_lines(self):
        blocks, trivial = contains_blocks("Check 1: main.assertion.1\\\n  - Status: SUCCESS\\\n - Description: \"x\"\n\nVERIFICATION:- SUCCESSFUL\n")
        self.assertEqual(blocks, [["Check 1: main.assertion.1", "- Status: SUCCESS", "- Description: \"x\""],
                                  ["VERIFICATION:- SUCCESSFUL"]])
        self.assertEqual(trivial, 2)

    def test_trailing_backslash_at_end_of_file_is_still_a_block(self):
        blocks, _ = contains_blocks("a\\\nb\\")
        self.assertEqual(blocks, [["a", "b"]])

    def test_empty_line_inside_a_joined_block_is_kept(self):
        blocks, _ = contains_blocks("Checking harness a...\\\n\\\nStatus: SATISFIED\n")
        self.assertEqual(blocks, [["Checking harness a...", "", "Status: SATISFIED"]])


class ExpectedParsingTests(unittest.TestCase):
    def test_regular_format_per_check_status(self):
        text = ("Check 1: check_invariant_fail_mut.assertion.1\\\n"
                "         - Status: SUCCESS\\\n"
                "         - Description: \"assertion failed: pos_point.is_safe()\"\n\n"
                "Check 2: core::num::<impl u8>::unchecked_mul.arithmetic_overflow.2\\\n"
                "         - Status: FAILURE\\\n"
                "         - Description: \"attempt to compute unchecked_mul which would overflow\"\\\n"
                "         - Location: main.rs:7:5 in function main\n")
        checks = parse_expected(text)["checks"]
        self.assertEqual([(c["property_class"], c["status"]) for c in checks],
                         [("assertion", "SUCCESS"), ("arithmetic_overflow", "FAILURE")])
        self.assertEqual(checks[1]["description"], "attempt to compute unchecked_mul which would overflow")
        self.assertEqual(checks[1]["location"], "main.rs:7:5 in function main")
        self.assertEqual(checks[1]["property_name"], "core::num::<impl u8>::unchecked_mul.arithmetic_overflow.2")

    def test_condensed_status_lines_with_inline_location(self):
        text = ("Status: UNREACHABLE\\\nDescription: \"\"This is unreachable\"\"\\\nin function main\n\n"
                "Status: FAILURE\\\nDescription: \"Function abort() was invoked\"\\\nin function std::process::abort\n\n"
                "Failed Checks: Function abort() was invoked\n\nVERIFICATION:- FAILED\n")
        parsed = parse_expected(text)
        self.assertEqual([(c["status"], c["description"]) for c in parsed["checks"]],
                         [("UNREACHABLE", "\"This is unreachable\""), ("FAILURE", "Function abort() was invoked")])
        self.assertEqual(parsed["checks"][1]["location"], "in function std::process::abort")
        self.assertEqual(parsed["failed_checks"], [{"description": "Function abort() was invoked", "harness": None}])

    def test_cover_statuses(self):
        text = ("Check 1: main.cover.1\\\nStatus: SATISFIED\\\nDescription: \"i may be greater than 20\"\n\n"
                "Status: UNSATISFIABLE\\\nDescription: \"cover condition: x == 3\"\n\n"
                "Check 3: main.cover.3\\\nStatus: UNREACHABLE\\\nDescription: \"cover location\"\n\n"
                " ** 1 of 3 cover properties satisfied (1 unreachable)\n")
        parsed = parse_expected(text)
        self.assertEqual([(c["property_class"], c["status"]) for c in parsed["covers"]],
                         [("cover", "SATISFIED"), ("cover", "UNSATISFIABLE"), ("cover", "UNREACHABLE")])
        self.assertEqual(parsed["checks"], [])
        self.assertEqual(parsed["cover_summaries"],
                         [{"satisfied": 1, "total": 3, "unreachable": 1, "harness": None}])

    def test_bare_status_token_and_check_summary(self):
        text = "UNREACHABLE\\\nDescription: \"assertion failed: x == 2\"\n ** 1 of 3 failed (1 unreachable)\n"
        parsed = parse_expected(text)
        self.assertEqual(parsed["checks"][0]["status"], "UNREACHABLE")
        self.assertEqual(parsed["check_summaries"], [{"failed": 1, "total": 3, "unreachable": 1, "harness": None}])

    def test_bare_token_followed_by_plain_description_line(self):
        parsed = parse_expected("SUCCESS\\\nassertion failed: y == 10\nFAILURE\\\nassertion failed: y != 10\n")
        self.assertEqual([(c["status"], c["description"]) for c in parsed["checks"]],
                         [("SUCCESS", "assertion failed: y == 10"), ("FAILURE", "assertion failed: y != 10")])

    def test_old_format_colon_status(self):
        parsed = parse_expected("line 7 assertion failed: false: FAILURE\n")
        self.assertEqual(parsed["checks"][0]["status"], "FAILURE")
        self.assertEqual(parsed["checks"][0]["form"], "old-format")

    def test_property_name_without_check_prefix_keeps_its_class(self):
        text = ("for_loop.loop_invariant_step.1\\\n - Status: SUCCESS\\\n - Description: \"Check invariant\"\n\n"
                "defs::no_op.cover\\\nStatus: SATISFIED\n")
        parsed = parse_expected(text)
        self.assertEqual([(c["property_class"], c["status"], c["description"]) for c in parsed["checks"]],
                         [("loop_invariant_step", "SUCCESS", "Check invariant")])
        self.assertEqual([(c["property_class"], c["status"]) for c in parsed["covers"]], [("cover", "SATISFIED")])

    def test_description_line_is_not_a_property_name(self):
        parsed = parse_expected("assertion failed: a.b.1\\\nStatus: FAILURE\n")
        self.assertEqual(parsed["checks"][0]["property_name"], None)

    def test_diagnostics_keep_error_codes(self):
        parsed = parse_expected("error[E0433]: cannot find module or crate `kani`\nerror: aborting due to 1 previous error\n")
        self.assertEqual([(d["level"], d["code"]) for d in parsed["diagnostics"]], [("error", "E0433"), ("error", None)])


class OracleTests(unittest.TestCase):
    OFFSET_FROM = ("Checking harness check_same...\nVERIFICATION:- SUCCESSFUL\n\n"
                   "Checking harness check_unit_panic...\nFailed Checks: assertion failed: 0 < pointee_size\n"
                   "VERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n\n"
                   "Checking harness check_diff_alloc...\nFailed Checks: same allocation\nVERIFICATION:- FAILED\n\n"
                   "Verification failed for - check_diff_alloc\n"
                   "Complete - 2 successfully verified harnesses, 1 failures, 3 total.\n")

    def test_per_harness_verdicts_with_should_panic(self):
        u = unit(harnesses=[("check_same", False), ("check_unit_panic", True), ("check_diff_alloc", False)])
        o = build_oracle(u, self.OFFSET_FROM)
        self.assertEqual(o["run_verdict"]["verdict"], "FAILED")
        self.assertEqual([(h["name"], h["should_panic"], h["verdict"]) for h in o["harnesses"]],
                         [("check_same", False, "SUCCESSFUL"), ("check_unit_panic", True, "SUCCESSFUL"),
                          ("check_diff_alloc", False, "FAILED")])
        self.assertEqual(o["summary"]["verification_lines"][1]["qualifier"],
                         "encountered one or more panics as expected")
        self.assertIn("per-harness", o["oracle_kinds"])
        self.assertEqual(o["expected_exit"]["kind"], "unchecked")

    def test_should_panic_whole_run_success_wins_over_failed_checks(self):
        text = " ** 2 of 2 failed\nFailed Checks: panicked on the `if` branch!\nVERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n"
        o = build_oracle(unit(harnesses=[("check", True)]), text)
        self.assertEqual(o["run_verdict"], {"verdict": "SUCCESSFUL", "basis": "single-harness-verification-line", "complete": True})
        self.assertEqual(o["harnesses"][0]["verdict"], "SUCCESSFUL")
        self.assertIn("whole-run", o["oracle_kinds"])

    def test_kani_verify_fail_directive(self):
        o = build_oracle(unit(mode="kani", harnesses=[("a", False)], step="verify"), None)
        self.assertEqual((o["stage"], o["expected_exit"]["kind"]), ("verify", "failure"))
        self.assertEqual(o["run_verdict"]["verdict"], "FAILED")
        self.assertEqual(o["harnesses"][0]["verdict"], "FAILED")

    def test_kani_verify_fail_with_several_harnesses_is_not_per_harness(self):
        o = build_oracle(unit(mode="kani", harnesses=[("a", False), ("b", False)], step="verify"), None)
        self.assertFalse(o["run_verdict"]["complete"])
        self.assertEqual([h["verdict"] for h in o["harnesses"]], [None, None])

    def test_kani_check_fail_directive_is_a_rejection(self):
        o = build_oracle(unit(mode="kani", harnesses=[("a", False)], step="check"), None)
        self.assertEqual(o["stage"], "check")
        self.assertIsNone(o["run_verdict"])
        self.assertIn("reject", o["oracle_kinds"])
        self.assertEqual(o["expected_exit"]["stage_command"], "kani-compiler -Z no-codegen")

    def test_kani_mode_default_is_success_for_every_harness(self):
        o = build_oracle(unit(mode="kani", harnesses=[("a", False), ("b", True)]), None)
        self.assertEqual(o["run_verdict"]["basis"], "exit-status")
        self.assertEqual([h["verdict"] for h in o["harnesses"]], ["SUCCESSFUL", "SUCCESSFUL"])

    def test_kani_fixme_inversion(self):
        o = build_oracle(unit(mode="kani-fixme", harnesses=[("a", False)], should_fail=True), None)
        self.assertEqual(o["expected_exit"]["kind"], "failure")
        self.assertTrue(o["inverted"])
        self.assertEqual(o["run_verdict"]["basis"], "exit-status-inverted")

    def test_fail_header_outside_kani_mode_states_no_verdict(self):
        u = unit(mode="kani-fixme", harnesses=[("a", False)], step="verify", should_fail=True)
        u["directive_panics"] = True
        o = build_oracle(u, None)
        self.assertEqual(o["upstream_outcome"], "props-parse-panic")
        self.assertEqual(o["expected_exit"]["kind"], "unchecked")
        self.assertIsNone(o["run_verdict"])
        self.assertEqual([h["verdict"] for h in o["harnesses"]], [None])
        self.assertEqual(o["oracle_kinds"], ["props-parse-panic"])

    def test_inverted_success_names_its_inverted_basis(self):
        o = build_oracle(unit(mode="kani", harnesses=[("a", False)], step="verify", should_fail=True), None)
        self.assertEqual(o["run_verdict"]["basis"], "exit-status-inverted")
        self.assertEqual(o["harnesses"][0]["basis"], "exit-status-inverted")

    def test_effective_keeps_completeness_and_upstream_ignore(self):
        text = "VERIFICATION:- SUCCESSFUL\n"
        o = build_oracle(unit(harnesses=[("a", False), ("b", False)], ignored="fixme test"), text)
        eff = effective_oracle_fields(o)
        self.assertEqual((eff["run_verdict"], eff["complete"], eff["upstream_ignored"]), ("SUCCESSFUL", False, True))
        o = build_oracle(unit(harnesses=[("a", False)]), "Status: FAILURE\n")
        o["overlay"] = [{"id": "kd-status-failure", "kind": "oracle", "effect": {"run_verdict": "FAILED"},
                         "relation": "fills"}]
        eff = effective_oracle_fields(o)
        self.assertEqual((eff["run_verdict"], eff["complete"], eff["upstream_ignored"]), ("FAILED", True, False))

    def test_exec_oracle_is_exit_code(self):
        o = build_oracle(unit(mode="exec", exit_code=1), "VERIFICATION:- FAILED\n")
        self.assertEqual(o["expected_exit"], {"kind": "code", "code": 1, "stage_command": "time <script>"})
        self.assertIn("exit-code", o["oracle_kinds"])

    def test_text_only_expected(self):
        o = build_oracle(unit(harnesses=[("a", False)]), "Checking contract\nsome text\n")
        self.assertEqual(o["oracle_kinds"], ["text-only"])
        self.assertIsNone(o["run_verdict"])


class LegacyVerdictTests(unittest.TestCase):
    """The discover.rs precedence the overlay's blast radii are computed with."""

    def test_precedence_matches_discover_rs(self):
        cases = [
            ("VERIFICATION:- FAILED\n", ("FAILED", "verification-failed-line")),
            (" ** 2 of 2 failed\nVERIFICATION:- SUCCESSFUL (encountered one or more panics as expected)\n",
             ("SUCCESSFUL", "verification-successful-line")),
            ("UNDETERMINED\n[Kani] info: Verification output shows one or more unwinding failures.\n",
             ("FAILED", "unwinding-banner")),
            ("Check 1\n- Status: FAILURE\\\nComplete - 3 successfully verified harnesses, 0 failures, 3 total.\n",
             ("SUCCESSFUL", "complete-summary")),
            ("FAILURE\\\nDescription: \"x\"\n", ("FAILED", "exact-status-token")),
            ("line 3 assertion failed: false: FAILURE\n", ("FAILED", "old-format-colon-failure")),
            ("UNREACHABLE\\\n ** 1 of 3 failed (1 unreachable)\n", ("FAILED", "n-of-m-failed")),
            (" ** 0 of 1 failed\n", ("SUCCESSFUL", "n-of-m-failed")),
            ("error: no harnesses matched\n", (None, None)),
        ]
        for text, want in cases:
            self.assertEqual(legacy_expected_verdict(text), want, text)


if __name__ == "__main__":
    unittest.main()
