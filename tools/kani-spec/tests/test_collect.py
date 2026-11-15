# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
import tempfile
import unittest
from pathlib import Path

from fixture import make_repo
from kani_spec import SpecError
from kani_spec.collect import collect_paths, perf_overlays, select_harnesses, suite_table
from kani_spec.fsview import Tree
from kani_spec.generate import build_rows


class CollectTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls._tmp = tempfile.TemporaryDirectory(prefix="kani-spec-collect-")
        cls.root = Path(cls._tmp.name) / "kani"
        make_repo(cls.root)
        cls.tree = Tree(cls.root)
        cls.table, cls.suites, cls.rows, _ = build_rows(cls.tree)

    @classmethod
    def tearDownClass(cls):
        cls._tmp.cleanup()

    def suite(self, name):
        return next(s for s in self.suites if s["suite"] == name)

    def test_suite_table_parses_tests_array_and_extra_scripts(self):
        pairs = [(r["suite"], r["mode"]) for r in self.table]
        self.assertEqual(pairs, [("kani", "kani"), ("expected", "expected"), ("cargo-kani", "cargo-kani"),
                                 ("script-based-pre", "exec"), ("kani-fixme", "kani-fixme"),
                                 ("perf", "cargo-kani-test")])
        self.assertTrue(next(r for r in self.table if r["suite"] == "perf")["perf_overlays"])

    def test_rs_mode_collects_every_rs_file_except_temp_prefixes_and_auxiliary(self):
        ids = sorted(self.suite("kani")["unit_ids"])
        self.assertEqual(ids, ["kani/Arith/add.rs", "kani/Arith/fail.rs", "kani/Arith/reject.rs",
                               "kani/Gaps/fixme_loop.rs", "kani/Gaps/ignore_me.rs", "kani/fixme_dir/main.rs"])

    def test_fixme_and_ignore_units_are_kept_but_ignored(self):
        self.assertEqual(self.rows["kani/Gaps/fixme_loop.rs"][0]["ignored"], "fixme test")
        self.assertEqual(self.rows["kani/Gaps/ignore_me.rs"][0]["ignored"], "ignore test")
        self.assertEqual(self.rows["kani/fixme_dir/main.rs"][0]["classification"], "fixme")

    def test_kani_fixme_units_are_fixme_basenames_and_inverted(self):
        s = self.suite("kani-fixme")
        self.assertEqual(s["unit_ids"], ["kani-fixme/Gaps/fixme_loop.rs"])
        self.assertEqual(s["upstream_collected"], 6)
        self.assertEqual(s["excluded_from_units"], {"ignore test": 1, "regular test": 4})
        unit, _, oracle = self.rows["kani-fixme/Gaps/fixme_loop.rs"]
        self.assertTrue(unit["should_fail"])
        self.assertEqual(oracle["expected_exit"]["kind"], "failure")
        self.assertEqual(oracle["run_verdict"]["basis"], "exit-status-inverted")

    def test_cargo_mode_one_unit_per_expected_file_in_cargo_dirs(self):
        self.assertEqual(sorted(self.suite("cargo-kani")["unit_ids"]),
                         ["cargo-kani/pkg/expected", "cargo-kani/pkg/nested_check.expected", "cargo-kani/ws/expected"])
        unit = self.rows["cargo-kani/pkg/nested_check.expected"][0]
        self.assertEqual(unit["cargo"]["harness_filter"], "nested_check")
        self.assertEqual(unit["cargo"]["metadata_kani_flags"], ["--default-unwind", "2"])
        selected = sorted(h["pretty_name"] for h in unit["harnesses"] if h["selected"])
        self.assertEqual(selected, ["inner::nested_check"])
        whole = self.rows["cargo-kani/pkg/expected"][0]
        self.assertEqual(sorted((h["pretty_name"], h["cfg_active"]) for h in whole["harnesses"]),
                         [("inner::nested_check", True), ("inner::off", False), ("inner::other", True), ("top", True)])
        oracle = self.rows["cargo-kani/pkg/expected"][2]
        self.assertEqual(oracle["run_verdict"]["summary_total"], 3)
        self.assertEqual(oracle["run_verdict"]["selected_source_harnesses"], 3)

    def test_workspace_package_selection_features_and_cfg_test(self):
        unit, _, oracle = self.rows["cargo-kani/ws/expected"]
        self.assertEqual(unit["cargo"]["crate_targets"], ["a:lib"])
        active = [(h["pretty_name"], h["cfg_active"]) for h in unit["harnesses"]]
        self.assertEqual(active, [("in_a", True), ("only_tests", False)])
        self.assertEqual(oracle["run_verdict"]["selected_source_harnesses"], 1)

    def test_exec_mode_one_unit_per_directory_with_config(self):
        self.assertEqual(sorted(self.suite("script-based-pre")["unit_ids"]),
                         ["script-based-pre/minimal", "script-based-pre/playback"])
        unit, _, oracle = self.rows["script-based-pre/playback"]
        self.assertEqual(unit["exec"]["exit_code"], 1)
        self.assertEqual(oracle["expected_exit"], {"kind": "code", "code": 1, "stage_command": "time <script>"})
        minimal = self.rows["script-based-pre/minimal"][2]
        self.assertEqual(minimal["expected_exit"]["code"], 0)

    def test_exec_directory_without_config_aborts_collection(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "k"
            make_repo(root, {"tests/script-based-pre/broken/run.sh": "#!/bin/sh\n"})
            paths, error = collect_paths(Tree(root), "script-based-pre", "exec")
            self.assertIn("no config.yml", error)

    def test_perf_overlay_creates_unit_in_cargo_dir(self):
        self.assertEqual(self.suite("perf")["unit_ids"], ["perf/lib/expected"])
        mapping = perf_overlays(self.tree, "perf")
        self.assertEqual(sorted(mapping), ["tests/perf/lib/expected"])
        paths, _ = collect_paths(self.tree, "perf", "cargo-kani-test")
        self.assertEqual(paths, [])

    def test_expected_mode_uses_directory_expected_for_any_file(self):
        a = self.rows["expected/multi/a.rs"][0]
        b = self.rows["expected/multi/b.rs"][0]
        self.assertEqual(a["expected_path"], "tests/expected/multi/expected")
        self.assertEqual(b["expected_path"], "tests/expected/multi/b.expected")
        missing = self.rows["expected/nofile/main.rs"]
        self.assertIsNone(missing[0]["expected_path"])
        self.assertIn("no-expected-file", missing[2]["oracle_kinds"])

    def test_dry_run_line_is_not_a_suite(self):
        self.assertNotIn(("kani", "cargo-kani"), [(r["suite"], r["mode"]) for r in self.table])

    def test_suite_in_two_modes_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "k"
            make_repo(root, {"scripts/kani-slow-tests.sh": "cargo run -p compiletest -- --suite kani --mode expected\n"})
            with self.assertRaises(SpecError):
                suite_table(Tree(root))

    def test_harness_filter_matches_kani_metadata_semantics(self):
        hs = [{"pretty_name": "m::check_a"}, {"pretty_name": "check_ab"}, {"pretty_name": "other"}]
        select_harnesses(hs, ["check_a"], False)
        self.assertEqual([h["selected"] for h in hs], [True, True, False])
        select_harnesses(hs, ["check_ab"], True)
        self.assertEqual([h["selected"] for h in hs], [False, True, False])

    def test_compile_flag_cfgs_feed_cfg_evaluation(self):
        from kani_spec.collect import cfgs_from_compile_flags
        self.assertEqual(cfgs_from_compile_flags(['--cfg=feature="std"', "--cfg", "loom", "--edition=2021"]),
                         ({"std"}, {"loom"}))

    def test_unit_digest_covers_inputs(self):
        unit = self.rows["cargo-kani/pkg/expected"][0]
        paths = [i["path"] for i in unit["inputs"]]
        self.assertIn("tests/cargo-kani/pkg/src/inner.rs", paths)
        self.assertNotIn("tests/cargo-kani/pkg/nested_check.expected", paths)
        self.assertEqual(len(unit["sha256"]), 64)


if __name__ == "__main__":
    unittest.main()
