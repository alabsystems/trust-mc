# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
import unittest

from fixture import TOOL_DIR  # noqa: F401  (puts kani_spec on sys.path)
from kani_spec.header import iter_header, parse_props, test_description


class HeaderTests(unittest.TestCase):
    def test_directives_stop_at_first_fn_or_mod(self):
        text = "// kani-flags: -Z stubbing\nuse x;\nfn main() {}\n// kani-flags: --late\n"
        self.assertEqual(parse_props(text, True)["kani_flags"], ["-Z", "stubbing"])
        self.assertEqual(list(iter_header("mod m;\n// kani-verify-fail\n", True)), [])

    def test_inner_doc_comment_is_not_a_directive(self):
        self.assertEqual(parse_props("//! kani-flags: --x\n", True)["kani_flags"], [])
        self.assertEqual(parse_props("/// kani-verify-fail\n", True)["kani_fail_step"], None)

    def test_fail_steps_are_whole_word(self):
        self.assertEqual(parse_props("// kani-verify-fail\n", True)["kani_fail_step"], "verify")
        self.assertEqual(parse_props("// kani-check-fail: reason\n", True)["kani_fail_step"], "check")
        self.assertEqual(parse_props("// kani-codegen-fail\n", True)["kani_fail_step"], "codegen")
        self.assertIsNone(parse_props("// kani-verify-failure\n", True)["kani_fail_step"])
        self.assertIsNone(parse_props("// kani-expect-fail\n", True)["kani_fail_step"])

    def test_non_rs_files_use_hash_comments(self):
        props = parse_props("# kani-flags: --harness x\n// kani-flags: --no\n", False)
        self.assertEqual(props["kani_flags"], ["--harness", "x"])

    def test_compile_flags_and_edition(self):
        props = parse_props("// compile-flags: --cfg foo\n// edition:2018\n", True)
        self.assertEqual(props["compile_flags"], ["--cfg", "foo", "--edition=2018"])

    def test_fixme_and_ignore_paths_are_ignored(self):
        self.assertEqual(test_description("tests/kani/A/fixme_x.rs", "kani", {})["ignore_message"], "fixme test")
        self.assertEqual(test_description("tests/kani/ignore/x.rs", "kani", {})["ignore_message"], "ignore test")
        self.assertFalse(test_description("tests/kani/A/x.rs", "kani", {})["ignore"])

    def test_kani_fixme_mode_runs_only_fixme_basenames_and_inverts(self):
        run = test_description("tests/kani-fixme/A/fixme_x.rs", "kani-fixme", {})
        self.assertEqual((run["ignore"], run["should_panic"]), (False, True))
        regular = test_description("tests/kani-fixme/fixme_dir/main.rs", "kani-fixme", {})
        self.assertEqual(regular["ignore_message"], "regular test")
        ign = test_description("tests/kani-fixme/A/ignore_x.rs", "kani-fixme", {})
        self.assertEqual(ign["ignore_message"], "ignore test")

    def test_should_fail_directive_inverts(self):
        props = parse_props("// should-fail\n", True)
        self.assertTrue(test_description("tests/kani/x.rs", "kani", props)["should_panic"])


if __name__ == "__main__":
    unittest.main()
