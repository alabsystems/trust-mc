#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unit tests for scripts/landing_select.py: every selection rule on a
synthetic workspace (a git repository built per test class), and the rules'
assumptions on this repository's own tree.

The rule tests read the module under test from ``SelectRules.mod``; the
mutants in scripts/test_landing_mutants.py re-run them against a mutated copy
and require at least one to fail."""

from __future__ import annotations

import importlib.util
import os
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
REPO = SCRIPTS.parent


def load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


landing_select = load("landing_select", SCRIPTS / "landing_select.py")


def crate(name: str, deps: dict[str, str] | None = None, extra: str = "") -> str:
    lines = [f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n', extra]
    if deps:
        lines.append("[dependencies]")
        lines += [f'{dep} = {{ path = "{path}" }}' for dep, path in deps.items()]
    return "\n".join(lines) + "\n"


FIXTURE = {
    "Cargo.toml": crate("trust-mc") + textwrap.dedent("""
        [workspace]
        members = ["trust-mc-core", "trust-mc-engine", "trust-mc-compiler", "trust-mc-backend",
                   "trust-mc-driver", "trust-mc-replay", "tools/compile-timer", "tools/build-trust-mc",
                   "library/trust-mc"]
        """),
    "Cargo.lock": "# lock\n",
    "src/lib.rs": "pub fn front_door() {}\n",
    "trust-mc-core/Cargo.toml": crate("trust-mc-core"),
    "trust-mc-engine/Cargo.toml": crate("trust-mc-engine", {"trust-mc-core": "../trust-mc-core"},
                                        '[lib]\npath = "../trust-mc-compiler/src/engine.rs"\n'),
    "trust-mc-compiler/Cargo.toml": crate("trust-mc-compiler", {"trust-mc-engine": "../trust-mc-engine",
                                                                "trust-mc-core": "../trust-mc-core"},
                                          '[[bin]]\nname = "trust-mc-compiler"\npath = "src/main.rs"\n'),
    "trust-mc-compiler/src/main.rs": "fn main() {}\n",
    "trust-mc-compiler/src/engine.rs": "pub mod codegen_ay;\n",
    "trust-mc-compiler/src/codegen_ay/chc/x.rs":
        'const FIXTURE: &str = include_str!("../../../../tests/fixtures/chc.rs");\n',
    "trust-mc-compiler/src/codegen_ay/obligation_free_walk.rs": "fn walk() { chc::detect_atomic_intrinsic(); }\n",
    "trust-mc-backend/Cargo.toml": crate("trust-mc-backend", {"trust-mc-engine": "../trust-mc-engine"}),
    "trust-mc-backend/src/lib.rs": "\n",
    "trust-mc-driver/Cargo.toml": crate("trust-mc-driver", {"trust-mc-core": "../trust-mc-core"}),
    "trust-mc-driver/src/main.rs": 'fn main() { let _ = "scripts/ay-soundness-gate.sh"; }\n',
    "trust-mc-driver/README.md": "# driver\n",
    "trust-mc-core/src/doc.md": "```\nassert!(true);\n```\n",
    "trust-mc-core/src/lib.rs": '#![doc = include_str!("doc.md")]\npub fn core() {}\n',
    "trust-mc-replay/Cargo.toml": crate("trust-mc-replay", {"trust-mc-driver": "../trust-mc-driver"}),
    "trust-mc-replay/src/main.rs": "fn main() {}\n",
    "tools/compile-timer/Cargo.toml": crate("compile-timer"),
    "tools/compile-timer/src/main.rs": 'fn main() { let _ = std::path::Path::new("x").join("scripts"); }\n',
    "tools/build-trust-mc/Cargo.toml": crate("build-trust-mc"),
    "tools/build-trust-mc/src/main.rs": "fn main() {}\n",
    "library/trust-mc/Cargo.toml": crate("kani", {"kani_macros": "../kani_macros"}),
    "library/trust-mc/src/lib.rs": "\n",
    "library/kani_macros/Cargo.toml": crate("kani_macros"),
    "library/kani_macros/src/lib.rs": "\n",
    "docs/a.md": "# a\n[b](b.md)\n",
    "docs/b.md": "# b\n",
    "README.md": "# readme\n",
    "scripts/soundness-dual-gate.py": "from helper import thing\n",
    "scripts/helper.py": "thing = 1\n",
    "scripts/unrelated.py": "print('hi')\n",
    "scripts/ay-soundness-gate.sh": "#!/bin/sh\n",
    "scripts/test_unrelated.py": "\n",
    # A leg script reading data in another region (scripts/tuple_check.py,
    # run by the lane build, reads DEFAULT_KANI_REV and the kani-spec pins).
    "scripts/check-trust-lane-build.sh": "#!/bin/sh\npython3 scripts/tuple_check.py\n",
    "scripts/tuple_check.py": textwrap.dedent("""
        ROOT = None
        CLONE = ROOT / "tools" / "kani-domination" / "src" / "clone.rs"
        PINS = ROOT / "tools/kani-spec/pins.toml"
        """),
    "tools/kani-domination/src/clone.rs": 'const DEFAULT_KANI_REV: &str = "x";\n',
    "tools/kani-spec/pins.toml": "[revs.spec]\n",
    "tools/kani-spec/README.md": "# spec\n",
    # A script test reaching a helper only through another script, and
    # reading a document of the tree.
    "scripts/test_tool.py": "import tool\nTEXT = ROOT / \"docs/b.md\"\nRUN = HERE / \"gone.py\"\n",
    "scripts/tool.py": "import tool_helper\n",
    "scripts/tool_helper.py": "X = 1\n",
    "scripts/gone.py": "\n",
    "tools/soundness-duals/manifest.toml": textwrap.dedent("""
        schema = "trust-mc.soundness-dual-manifest/v1"
        [[entry]]
        path = "a_dual.rs"
        lanes = ["bmc", "chc"]
        [[entry]]
        path = "c_dual.rs"
        lanes = ["chc"]
        """),
    "tools/soundness-duals/a_dual.rs": "\n",
    "tools/soundness-duals/c_dual.rs": "\n",
    "tools/soundness-duals/README.md": "# duals\n",
    "tools/soundness-duals/reports/r.json": "{}\n",
    "tools/engine-suite/known-failures.tsv": "test\tclass\n",
    "tools/kani-domination/src/main.rs": "\n",
    "tools/tuple.toml": "schema = 1\n",
    "tests/fixtures/chc.rs": "\n",
    "tests/other.rs": "\n",
    ".cargo/config.toml": "\n",
    "rust-toolchain.toml": "\n",
}


def write_tree(root: Path, files: dict[str, str]) -> None:
    for rel, text in files.items():
        path = root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root), *args], check=True, capture_output=True,
                          text=True).stdout


class Fixture:
    def __init__(self, files: dict[str, str] = FIXTURE):
        self.tmp = tempfile.TemporaryDirectory(prefix="landing-select-")
        self.root = Path(self.tmp.name)
        write_tree(self.root, files)
        git(self.root, "init", "-q", "-b", "main")
        git(self.root, "-c", "user.name=t", "-c", "user.email=t@t", "add", "-A")
        git(self.root, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "base")
        self.base = git(self.root, "rev-parse", "HEAD").strip()

    def close(self) -> None:
        self.tmp.cleanup()


class SelectRules(unittest.TestCase):
    mod = landing_select
    fixture: Fixture

    @classmethod
    def setUpClass(cls) -> None:
        cls.fixture = Fixture()

    @classmethod
    def tearDownClass(cls) -> None:
        cls.fixture.close()

    def ctx(self):
        if getattr(self.fixture, "ctx", None) is None:
            self.fixture.ctx = self.mod.build_context(self.mod.Tree(self.fixture.root, self.fixture.base))
        return self.fixture.ctx

    def select(self, *paths: str, status: str = "M", mode: str = "100644"):
        changes = [self.mod.Change(p, status, mode, mode) for p in paths]
        return self.mod.select(changes, self.ctx(), "base", "head")

    def legs(self, *paths: str, **kw) -> set[str]:
        return set(self.select(*paths, **kw).selected)

    def assert_everything(self, *paths: str, **kw) -> None:
        sel = self.select(*paths, **kw)
        self.assertTrue(sel.everything, f"{paths} should select everything, got {sorted(sel.selected)}")
        self.assertEqual(set(sel.selected), set(self.mod.all_legs(self.ctx().packages)))
        self.assertEqual(sel.skipped, {})

    # -- docs and prose ----------------------------------------------------

    def test_docs_only_selects_only_the_doc_check(self) -> None:
        self.assertEqual(self.legs("docs/a.md", "README.md"), {"docs-links"})

    def test_crate_prose_no_literal_names_is_docs(self) -> None:
        self.assertEqual(self.legs("trust-mc-driver/README.md"), {"docs-links"})

    def test_a_markdown_file_a_crate_includes_is_its_input(self) -> None:
        # include_str!("doc.md") has no slash; its doctests are the crate's tests.
        self.assertIn("crate-tests:trust-mc-core", self.legs("trust-mc-core/src/doc.md"))

    def test_duals_readme_and_reports_are_docs(self) -> None:
        self.assertEqual(self.legs("tools/soundness-duals/README.md", "tools/soundness-duals/reports/r.json"),
                         {"docs-links"})

    def test_a_deletion_runs_the_link_check(self) -> None:
        self.assertIn("docs-links", self.legs("scripts/unrelated.py", status="D"))

    # -- crates and the reverse closure -------------------------------------

    def test_leaf_crate_selects_only_its_tests(self) -> None:
        self.assertEqual(self.legs("tools/compile-timer/src/main.rs"), {"crate-tests:compile-timer"})

    def test_core_crate_selects_its_reverse_closure(self) -> None:
        sel = self.select("trust-mc-core/src/lib.rs")
        legs = set(sel.selected)
        for leg in ("dual-chc", "dual-bmc", "dual-validate", "engine-suite", "tsv-validate", "lane-build",
                    "crate-tests:trust-mc-core", "crate-tests:trust-mc-driver", "crate-tests:trust-mc-replay"):
            self.assertIn(leg, legs)
        for crate in ("trust-mc-engine", "trust-mc-compiler", "trust-mc-backend", "trust-mc-driver",
                      "trust-mc-replay"):
            self.assertIn(crate, sel.affected_crates)
        self.assertNotIn("crate-tests:compile-timer", legs)

    def test_driver_change_skips_the_engine_suite(self) -> None:
        legs = self.legs("trust-mc-driver/src/main.rs")
        self.assertTrue({"dual-chc", "dual-bmc", "lane-build", "crate-tests:trust-mc-driver",
                         "crate-tests:trust-mc-replay"} <= legs)
        self.assertNotIn("engine-suite", legs)

    def test_engine_source_owned_through_a_target_root(self) -> None:
        legs = self.legs("trust-mc-compiler/src/codegen_ay/obligation_free_walk.rs")
        self.assertTrue({"engine-suite", "lane-port", "lane-build", "dual-chc", "dual-bmc"} <= legs)

    def test_chc_codegen_runs_both_dual_lanes(self) -> None:
        # Lane-shared code (the obligation-free walk) calls into chc/: no
        # module under chc/ is unreachable from the BMC lane.
        legs = self.legs("trust-mc-compiler/src/codegen_ay/chc/x.rs")
        self.assertTrue({"dual-chc", "dual-bmc"} <= legs)

    def test_non_member_path_dependency_is_a_crate(self) -> None:
        legs = self.legs("library/kani_macros/src/lib.rs")
        self.assertTrue({"dual-chc", "dual-bmc"} <= legs)

    # -- literals ---------------------------------------------------------

    def test_a_script_a_crate_names_selects_the_crate(self) -> None:
        legs = self.legs("scripts/ay-soundness-gate.sh")
        self.assertTrue({"script-tests", "crate-tests:trust-mc-driver", "dual-chc"} <= legs)

    def test_bare_region_literal_is_a_read_unless_excluded(self) -> None:
        # compile-timer's `join("scripts")` is no reviewed exclusion: a read of
        # all of scripts/.
        self.assertIn("crate-tests:compile-timer", self.legs("scripts/unrelated.py"))

    def test_a_literal_does_not_map_an_unmapped_region(self) -> None:
        self.assert_everything("tests/fixtures/chc.rs")

    # -- data ---------------------------------------------------------------

    def test_chc_only_dual_entry_selects_only_the_chc_lane(self) -> None:
        self.assertEqual(self.legs("tools/soundness-duals/c_dual.rs"), {"dual-chc", "dual-validate"})

    def test_both_lane_entry_and_manifest_select_both(self) -> None:
        self.assertEqual(self.legs("tools/soundness-duals/a_dual.rs"), {"dual-chc", "dual-bmc", "dual-validate"})
        self.assertEqual(self.legs("tools/soundness-duals/manifest.toml"),
                         {"dual-chc", "dual-bmc", "dual-validate"})

    def test_engine_tsv(self) -> None:
        self.assertEqual(self.legs("tools/engine-suite/known-failures.tsv"), {"engine-suite", "tsv-validate"})

    def test_unrelated_script_selects_script_tests(self) -> None:
        self.assertEqual(self.legs("scripts/unrelated.py"), {"script-tests", "crate-tests:compile-timer"})

    def test_kani_domination(self) -> None:
        self.assertEqual(self.legs("tools/kani-domination/src/main.rs"), {"kani-domination-tests"})

    # -- what the legs' own scripts read -------------------------------------

    def test_a_file_a_leg_script_reads_selects_the_leg(self) -> None:
        # Without this rule DEFAULT_KANI_REV could move with only the
        # kani-domination tests run, and the lane build's tuple-check refuse
        # it on main.
        legs = self.legs("tools/kani-domination/src/clone.rs")
        self.assertTrue({"kani-domination-tests", "lane-build"} <= legs, legs)
        self.assertIn("lane-build", self.legs("tools/kani-spec/pins.toml"))

    def test_only_the_files_the_script_names_are_its_inputs(self) -> None:
        # The joined spelling names one file, not all of tools/.
        self.assertNotIn("lane-build", self.legs("tools/kani-spec/README.md"))
        self.assertNotIn("lane-build", self.legs("tools/kani-domination/src/main.rs"))

    def test_a_script_test_reaches_helpers_transitively(self) -> None:
        ctx = self.ctx()
        change = [self.mod.Change("scripts/tool_helper.py", "M", "100644", "100644")]
        tree = self.mod.Tree(self.fixture.root, self.fixture.base)
        self.assertEqual(self.mod.script_tests_reached(ctx, change, tree), ["scripts/test_tool.py"])

    def test_a_document_a_script_test_reads_selects_it(self) -> None:
        self.assertEqual(self.legs("docs/b.md"), {"docs-links", "script-tests"})
        tree = self.mod.Tree(self.fixture.root, self.fixture.base)
        change = [self.mod.Change("docs/b.md", "M", "100644", "100644")]
        self.assertEqual(self.mod.script_tests_reached(self.ctx(), change, tree), ["scripts/test_tool.py"])


    # -- fail-closed ------------------------------------------------------

    def test_unmapped_path_selects_everything(self) -> None:
        self.assert_everything("tests/other.rs")
        self.assert_everything("benchmarks/new.sh")

    def test_build_inputs_select_everything(self) -> None:
        # Inside mapped regions too, so the rule is what selects everything,
        # not the unmapped fallback.
        for path in ("Cargo.lock", "trust-mc-driver/Cargo.toml", "trust-mc-driver/build.rs",
                     "rust-toolchain.toml", ".cargo/config.toml", "tools/tuple.toml",
                     "tools/kani-domination/Cargo.lock", "trust-mc-driver/Cargo.lock",
                     "tools/kani-domination/Cargo.toml", "scripts/rust-toolchain"):
            with self.subTest(path=path):
                self.assert_everything(path)
                self.assertEqual(self.mod.classify_path(path, self.ctx()).rule, "build-input")

    def test_gate_scripts_and_their_helpers_select_everything(self) -> None:
        self.assert_everything("scripts/soundness-dual-gate.py")
        self.assert_everything("scripts/helper.py")

    def test_symlink_or_submodule_selects_everything(self) -> None:
        self.assert_everything("docs/a.md", mode="120000")
        self.assert_everything("docs/a.md", mode="160000")

    def test_every_leg_is_selected_or_skipped_with_a_reason(self) -> None:
        sel = self.select("trust-mc-driver/src/main.rs")
        universe = set(self.mod.all_legs(self.ctx().packages))
        self.assertEqual(set(sel.selected) | set(sel.skipped), universe)
        self.assertFalse(set(sel.selected) & set(sel.skipped))
        self.assertTrue(all(reason for reason in sel.skipped.values()))


class FailClosedTrees(unittest.TestCase):
    """Trees the selector cannot read select everything."""

    mod = landing_select

    def test_casefold_collision_selects_everything(self) -> None:
        fx = Fixture()
        try:
            # A case-insensitive file system cannot hold both spellings, so the
            # twin enters through the index, as a pull from elsewhere would.
            blob = subprocess.run(["git", "-C", str(fx.root), "hash-object", "-w", "--stdin"], input="# twin\n",
                                  check=True, capture_output=True, text=True).stdout.strip()
            git(fx.root, "update-index", "--add", "--cacheinfo", f"100644,{blob},readme.md")
            git(fx.root, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "-m", "twin")
            head = git(fx.root, "rev-parse", "HEAD").strip()
            ctx = self.mod.build_context(self.mod.Tree(fx.root, head))
            sel = self.mod.select([self.mod.Change("README.md", "M", "100644", "100644")], ctx)
            self.assertTrue(sel.everything)
        finally:
            fx.close()

    def test_unreadable_graph_selects_everything(self) -> None:
        files = dict(FIXTURE)
        files["trust-mc-core/Cargo.toml"] = "[package\n"
        fx = Fixture(files)
        try:
            ctx = self.mod.build_context(self.mod.Tree(fx.root, fx.base))
            self.assertIsNotNone(ctx.graph_error)
            sel = self.mod.select([self.mod.Change("docs/a.md", "M", "100644", "100644")], ctx)
            self.assertTrue(sel.everything)
        finally:
            fx.close()

    def test_missing_member_is_a_graph_error(self) -> None:
        files = dict(FIXTURE)
        del files["trust-mc-replay/Cargo.toml"]
        fx = Fixture(files)
        try:
            ctx = self.mod.build_context(self.mod.Tree(fx.root, fx.base))
            self.assertIn("trust-mc-replay", ctx.graph_error or "")
        finally:
            fx.close()

    def test_a_deleted_file_a_test_names_reaches_it(self) -> None:
        # The tree no longer holds the file, so only its name is left to find.
        fx = Fixture({k: v for k, v in FIXTURE.items() if k != "scripts/gone.py"})
        try:
            tree = self.mod.Tree(fx.root, fx.base)
            ctx = self.mod.build_context(tree)
            change = [self.mod.Change("scripts/gone.py", "D", "100644", "000000")]
            self.assertIn("scripts/test_tool.py", self.mod.script_tests_reached(ctx, change, tree))
        finally:
            fx.close()

    def test_metadata_disagreement_is_a_graph_error(self) -> None:
        fx = Fixture()
        try:
            tree = self.mod.Tree(fx.root, fx.base)
            root = str(fx.root.resolve())
            metadata = {
                "workspace_members": ["x"],
                "packages": [{"id": "x", "name": "ghost", "manifest_path": f"{root}/ghost/Cargo.toml",
                              "dependencies": []}],
            }
            ctx = self.mod.build_context(tree, metadata)
            self.assertIn("ghost", ctx.graph_error or "")
        finally:
            fx.close()


class PathRefs(unittest.TestCase):
    """How a script's code names a repository path (``path_refs``)."""

    mod = landing_select
    TOP = {"tools", "docs", "scripts", "src"}

    def refs(self, text: str) -> set[str]:
        return self.mod.path_refs(text, self.TOP)

    def test_spellings(self) -> None:
        cases = {
            'ROOT / "tools" / "x" / "y.rs"': {"tools/x/y.rs"},
            'p = "$ROOT/tools/x"': {"tools/x"},
            'cd "${ROOT_DIR}/scripts/a.sh"': {"scripts/a.sh"},
            # A comma run keeps its segments too (it may be an argument list).
            'os.path.join(root, "tools", "z")': {"tools", "tools/z"},
            'x = "../ay/src/lib.rs"': set(),
            'f"tools/{name}.py"': {"tools/*"},
            'glob("scripts/test_*.py")': {"scripts/test_*"},
            'root / "docs"': {"docs"},
            'docs = 1': set(),
            'subprocess.run(["git", "ls-files", "--", "*.sh"])': {"**.sh"},
            'for p in d.glob("*.rs"): pass': set(),
        }
        for text, want in cases.items():
            with self.subTest(text=text):
                self.assertEqual(self.refs(text), want)

    def test_under(self) -> None:
        self.assertTrue(self.mod._under("tools/x/a.rs", "tools/x"))
        self.assertFalse(self.mod._under("tools/xy/a.rs", "tools/x"))
        self.assertTrue(self.mod._under("tools/xy/a.rs", "tools/x*"))
        self.assertTrue(self.mod._under("deep/dir/run.sh", "**.sh"))
        self.assertFalse(self.mod._under("deep/dir/run.shx", "**.sh"))

    def test_literal_targets_read_a_computed_root(self) -> None:
        top = {"tools", "docs"}
        self.assertIn("crate/README.md",
                      self.mod.literal_targets("crate/src/lib.rs", "/README.md", "crate", top))
        self.assertIn("tools/soundness-duals/x.rs",
                      self.mod.literal_targets("crate/src/lib.rs", "{root}/tools/soundness-duals/x.rs",
                                               "crate", top))


class DiffParsing(unittest.TestCase):
    def test_raw_diff_records(self) -> None:
        raw = (":100644 100644 aaa bbb M\0a.rs\0:000000 120000 000 ccc A\0link\0"
               ":100644 000000 ddd 000 D\0gone.md\0")
        changes = landing_select.parse_raw_diff(raw)
        self.assertEqual([(c.path, c.status, c.new_mode) for c in changes],
                         [("a.rs", "M", "100644"), ("link", "A", "120000"), ("gone.md", "D", "000000")])


class ThisRepository(unittest.TestCase):
    """The selector's assumptions, checked on this repository's tree."""

    @classmethod
    def setUpClass(cls) -> None:
        cls.tree = landing_select.Tree(REPO, "HEAD")
        cls.ctx = landing_select.build_context(cls.tree)

    def test_graph_reads(self) -> None:
        self.assertIsNone(self.ctx.graph_error)
        self.assertIn("trust-mc-engine", self.ctx.packages)
        self.assertIn("kani_macros", self.ctx.packages)

    def test_graph_agrees_with_targo_metadata(self) -> None:
        metadata = landing_select.targo_metadata(REPO)
        self.assertIsNotNone(metadata, "targo metadata must run here (the Trust toolchain is this repo's)")
        packages = landing_select.read_graph(landing_select.Tree(REPO, None))
        self.assertEqual(landing_select.cross_check_metadata(packages, metadata, REPO), [])

    def test_literal_exclusions_are_not_stale(self) -> None:
        for (crate, file, literal), reason in landing_select.LITERAL_EXCLUSIONS.items():
            with self.subTest(file=file):
                text = self.tree.read(file) or ""
                self.assertIn(f'"{literal}"', text, f"stale exclusion: {reason}")
                self.assertIn(crate, landing_select.owners_of(file, self.ctx.owners))

    def test_gate_script_closure_holds_the_known_helpers(self) -> None:
        closure = self.ctx.gate_scripts
        for path in ("scripts/soundness-dual-gate.py", "scripts/ay_manifest_pin.py", "scripts/check_live_main.py",
                     "scripts/lib/python-with-toml.sh", "scripts/tuple_check.py", "scripts/host_room.py",
                     "scripts/landing_select.py", "tools/port/trust_api_codemod.py"):
            self.assertIn(path, closure)

    def test_chc_codegen_is_reached_from_lane_shared_code(self) -> None:
        # The fact that keeps CHC changes on both dual lanes (docs/landing-gates.md).
        walk = self.tree.read("trust-mc-compiler/src/codegen_ay/obligation_free_walk.rs") or ""
        self.assertIn("crate::codegen_ay::chc::detect_atomic_intrinsic", walk)
        verdict = landing_select.classify_path("trust-mc-compiler/src/codegen_ay/chc/mod.rs", self.ctx)
        affected = landing_select.reverse_closure(self.ctx.packages, verdict.crates)
        legs = landing_select.legs_for_crates(affected, self.ctx.packages)
        self.assertIn("dual-bmc", legs)
        self.assertIn("dual-chc", legs)

    def test_data_ref_exclusions_are_not_stale(self) -> None:
        top = {p.split("/", 1)[0] for p in self.tree.files()}
        matcher = landing_select.RefMatcher(landing_select.code_candidates(self.tree, self.ctx.owners))
        for (file, ref), reason in landing_select.DATA_REF_EXCLUSIONS.items():
            with self.subTest(file=file, ref=ref):
                code = landing_select._code_text(file, self.tree.read(file) or "")
                named = landing_select.path_refs(code, top) | matcher.named(code)
                self.assertIn(ref, named, f"stale exclusion: {reason}")

    def test_selector_tree_tests_run_the_selector_on_this_tree(self) -> None:
        for test in landing_select.SELECTOR_TREE_TESTS:
            with self.subTest(test=test):
                self.assertIn("class ThisRepository", self.tree.read(test) or "")

    def test_leg_scripts_exist(self) -> None:
        files = set(self.tree.files())
        for leg, roots in landing_select.LEG_SCRIPTS.items():
            with self.subTest(leg=leg):
                self.assertTrue(landing_select._expand_roots(roots, files), roots)

    def test_the_lane_build_reads_what_tuple_check_reads(self) -> None:
        # The hole the leg-read rule closes, on this tree.
        for path in ("tools/kani-domination/src/clone.rs", "tools/kani-spec/pins.toml"):
            with self.subTest(path=path):
                self.assertIn("lane-build", landing_select.classify_path(path, self.ctx).legs)
        self.assertNotIn("lane-build", landing_select.classify_path(
            "tools/kani-domination/src/main.rs", self.ctx).legs)

    def test_every_tracked_path_classifies(self) -> None:
        for path in self.tree.files():
            verdict = landing_select.classify_path(path, self.ctx)
            self.assertTrue(verdict.everything or verdict.crates or verdict.legs, path)


if __name__ == "__main__":
    unittest.main()
