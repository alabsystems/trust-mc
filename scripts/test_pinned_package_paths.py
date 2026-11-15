#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""The explicit latest-main diagnostic: every changed path is drift except regular files
under a reviewed exclusion that the pinned packages provably do not read.

Every test that reaches the exclusion check builds its fixture with `targo
--unverified check` (resolved as the gate resolves it: $TRUST_MC_TARGO, else
scripts/resolve-trust-tool.sh); a host without it fails these tests rather than
skipping them.
"""

from __future__ import annotations

import contextlib
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
import unittest
import unittest.mock
from collections import Counter
from pathlib import Path
from typing import Any, Optional, Sequence

SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))

import pinned_package_paths as ppp  # noqa: E402

if sys.version_info >= (3, 11):
    from tomllib import loads as toml_loads
else:
    from tomli import loads as toml_loads


def resolve_targo() -> str:
    explicit = os.environ.get("TRUST_MC_TARGO")
    if explicit:
        return explicit
    return subprocess.check_output(
        [str(SCRIPTS / "resolve-trust-tool.sh"), "targo"], text=True
    ).strip()


TARGO = resolve_targo()


def folds_case(directory: Path) -> bool:
    """Whether the file system under `directory` opens `X` as `x`."""
    probe = directory / "case-probe"
    probe.write_text("", encoding="utf-8")
    try:
        return (directory / "CASE-PROBE").exists()
    finally:
        probe.unlink()


def excluding(*patterns: str) -> list:
    return [ppp.Exclusion(pattern, "test") for pattern in patterns]


class without_build_inputs:
    """The gate with its reading of the files at the pin off (what every tracked
    file names for the C preprocessor or an assembler, what Rust files include
    under any cfg, what a build script's string literals name): what the checks
    observe alone must still refuse."""

    def __init__(self) -> None:
        self.patches = [
            unittest.mock.patch.object(ppp.BuildInputs, "scan_tree", lambda self, closure: None),
            unittest.mock.patch.object(ppp.BuildInputs, "scan_rust", lambda self, closure: None),
            unittest.mock.patch.object(ppp.BuildInputs, "scan_build_scripts", lambda self, closure: None),
        ]

    def __enter__(self) -> None:
        for patch in self.patches:
            patch.start()

    def __exit__(self, *details: Any) -> None:
        for patch in reversed(self.patches):
            patch.stop()


class GitRepo:
    """A scratch repository whose commits stand for the pin and live main."""

    def __init__(self, root: Path) -> None:
        self.root = root
        subprocess.run(["git", "init", "-q", "-b", "main", str(root)], check=True)
        self.git("config", "user.name", "Trust MC Test")
        self.git("config", "user.email", "trust-mc-test@example.invalid")
        self.git("config", "core.ignorecase", "false")

    def git(self, *arguments: str, stdin: Optional[bytes] = None) -> str:
        return subprocess.check_output(
            ["git", "-C", str(self.root), *arguments], input=stdin, stderr=subprocess.PIPE
        ).decode().strip()

    def commit(
        self, files: dict[str, Optional[str]], links: Optional[dict[str, str]] = None
    ) -> str:
        """Writes `files` (None deletes) and symbolic `links` on disk, and commits
        the working tree."""
        for relative, text in files.items():
            path = self.root / relative
            if text is None:
                self.git("rm", "-q", "-r", relative)
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding="utf-8")
        for relative, target in (links or {}).items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            if path.is_symlink():
                path.unlink()
            path.symlink_to(target)
        self.git("add", "-A")
        self.git("commit", "-q", "--allow-empty", "-m", "edit")
        return self.git("rev-parse", "HEAD")

    def after(self, revision: str, files: dict[str, Optional[str]]) -> str:
        """A commit of `files` on top of `revision` alone."""
        self.git("reset", "-q", "--hard", revision)
        return self.commit(files)

    def stage(self, entries: dict[str, tuple[str, str]]) -> str:
        """Commits `entries` (path -> (mode, content)) through the index alone,
        so a case-insensitive file system cannot fold two spellings into one.
        Only another `stage` may follow."""
        for path, (mode, content) in entries.items():
            if mode == "160000":
                sha = content
            else:
                sha = self.git("hash-object", "-w", "--stdin", stdin=content.encode())
            self.git("update-index", "--add", "--cacheinfo", f"{mode},{sha},{path}")
        self.git("commit", "-q", "--allow-empty", "-m", "stage")
        return self.git("rev-parse", "HEAD")


def gate(repo: GitRepo, pin: str, live_main: str, *packages: str) -> subprocess.CompletedProcess:
    """The standalone latest-main drift diagnostic without exclusions."""
    return subprocess.run(
        [
            sys.executable, str(SCRIPTS / "pinned_package_paths.py"), "drift", TARGO,
            str(repo.root), pin, live_main, *(packages or ("a",)),
        ],
        capture_output=True, text=True, check=False,
    )


PACKAGE = '[package]\nname = "{}"\nversion = "0.1.0"\nedition = "2021"\n'


class OneCrate(unittest.TestCase):
    """Package `a` of a one-crate workspace, pinned, and live main past it."""

    def setUp(self) -> None:
        self.scratch = tempfile.TemporaryDirectory()
        self.repo = GitRepo(Path(self.scratch.name).resolve() / "shapes")

    def tearDown(self) -> None:
        self.scratch.cleanup()

    def pin(self, files: dict[str, Optional[str]], links: Optional[dict[str, str]] = None) -> str:
        return self.repo.commit(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a"),
                **files,
            },
            links,
        )

    def drift(
        self, pin: str, live_main: str, exclusions: Sequence = (), consumer: Optional[Path] = None
    ):
        return ppp.drift(TARGO, self.repo.root, pin, live_main, ["a"], consumer, exclusions)

    def assert_read(self, pin: str, live_main: str, exclusions: Sequence, message: str) -> None:
        """The exclusions cover what `a` reads, so the gate refuses."""
        with self.assertRaisesRegex(ppp.Refusal, message):
            self.drift(pin, live_main, exclusions)

    def assert_unread(self, pin: str, live_main: str, exclusions: Sequence) -> None:
        result = self.drift(pin, live_main, exclusions)
        self.assertEqual(result.drifted, [])
        self.assertTrue(result.excluded)


class PureTests(unittest.TestCase):
    def test_a_pattern_matches_as_spelled_one_component_at_a_time(self) -> None:
        evals = ppp.Exclusion("evals/*/src", "x")
        self.assertTrue(evals.covers("evals/a/src/lib.rs"))
        self.assertTrue(evals.covers("evals/a/src"))
        self.assertFalse(evals.covers("evals/a/Cargo.lock"))
        self.assertFalse(evals.covers("evals/a/b/src/lib.rs"))
        self.assertFalse(evals.covers("Evals/a/src/lib.rs"))
        prose = ppp.Exclusion("*.md", "x")
        self.assertTrue(prose.covers("README.md"))
        self.assertTrue(prose.covers("README.md/inner"))
        self.assertFalse(prose.covers("docs/README.md"))
        self.assertFalse(ppp.Exclusion("docs", "x").covers("docsx/a.md"))

    def test_a_pattern_that_could_cover_what_cargo_reads_by_name_is_refused(self) -> None:
        for pattern in (
            "", "/docs", "docs/", "docs/../crates", "./docs", "docs/**", "docs/[ab]",
            "crates/a/Cargo.toml", "CARGO.TOML", ".gitattributes", "a/.cargo", "vendor/.git",
            "crates/a/Build.rs",
        ):
            with self.subTest(pattern=pattern):
                self.assertIsNotNone(ppp.pattern_problem(pattern))
        for pattern in ("docs", "*.md", "evals/*/src", "crates/a/src/build.rs.in"):
            with self.subTest(pattern=pattern):
                self.assertIsNone(ppp.pattern_problem(pattern))

    def test_the_list_is_read_per_repository_and_every_entry_needs_its_reason(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            listed = Path(scratch) / "x.toml"
            listed.write_text('[one]\n"docs" = "prose"\n"*.md" = "prose"\n', encoding="utf-8")
            self.assertEqual(
                [each.pattern for each in ppp.load_exclusions(listed, "one")], ["docs", "*.md"]
            )
            self.assertEqual(ppp.load_exclusions(listed, "other"), [])
            for text in ('[one]\n"docs" = ""\n', '[one]\n"docs" = 1\n', '[one]\n"../x" = "y"\n',
                         "one = 1\n", "[one\n"):
                with self.subTest(text=text):
                    listed.write_text(text, encoding="utf-8")
                    with self.assertRaises(ppp.Refusal):
                        ppp.load_exclusions(listed, "one")

    def test_the_reviewed_list_parses_with_a_reason_for_every_entry(self) -> None:
        listed = SCRIPTS / "pin-exclusions.toml"
        document = toml_loads(listed.read_text(encoding="utf-8"))
        self.assertEqual(
            sorted(document), [ppp.CARGO_AT_RUN_TIME, ppp.CONSUMER_BUILDS, "trust-ir", "trust-vc"]
        )
        for repository in ("trust-ir", "trust-vc"):
            exclusions = ppp.load_exclusions(listed, repository)
            self.assertTrue(exclusions)
            self.assertTrue(all(len(each.why) > 20 for each in exclusions))
        self.assertIsNone(ppp.load_cargo_at_run_time(listed, "trust-ir"))
        self.assertIn("api_surface", ppp.load_cargo_at_run_time(listed, "trust-vc") or "")

    def test_cargo_at_run_time_is_read_per_repository_and_needs_its_reason(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            listed = Path(scratch) / "x.toml"
            listed.write_text(f'[{ppp.CARGO_AT_RUN_TIME}]\none = "its api runs cargo"\n', encoding="utf-8")
            self.assertEqual(ppp.load_cargo_at_run_time(listed, "one"), "its api runs cargo")
            self.assertIsNone(ppp.load_cargo_at_run_time(listed, "other"))
            for text in (f'[{ppp.CARGO_AT_RUN_TIME}]\none = ""\n', f'{ppp.CARGO_AT_RUN_TIME} = 1\n',
                         f'[{ppp.CARGO_AT_RUN_TIME}]\none = 1\n'):
                with self.subTest(text=text):
                    listed.write_text(text, encoding="utf-8")
                    with self.assertRaises(ppp.Refusal):
                        ppp.load_cargo_at_run_time(listed, "one")

    def test_a_feature_enables_the_features_its_table_names_transitively(self) -> None:
        # Never more than Cargo enables: `serde/derive` may or may not turn on
        # feature `serde`, so it is not counted.
        table = {
            "default": ["z"], "x": [], "y": ["x", "dep:serde"], "z": ["y"], "serde": ["dep:serde"],
            "w": ["serde/derive"], "v": ["other?/f", "gone/f"],
        }
        self.assertEqual(ppp.enabled(table, {"default"}), {"default", "x", "y", "z"})
        self.assertEqual(ppp.enabled(table, {"y"}), {"x", "y"})
        self.assertEqual(ppp.enabled(table, {"w"}), {"w"})
        self.assertEqual(ppp.enabled(table, {"v"}), {"v"})

    def test_module_files_are_looked_for_beside_a_file_or_its_mod_rs_directory(self) -> None:
        self.assertEqual(ppp.module_directory(Path("/t/shared/gen.rs")), Path("/t/shared"))
        self.assertEqual(ppp.module_directory(Path("/t/shared/sub/mod.rs")), Path("/t/shared"))
        self.assertEqual(ppp.module_directory(Path("/t/shared/sub/MOD.RS")), Path("/t/shared"))
        self.assertEqual(ppp.module_directory(Path("/t/shared/x.txt")), Path("/t/shared"))

    def test_folding_is_canonical_caseless_matching(self) -> None:
        self.assertEqual(ppp.fold("SHARED/Raw.rs"), ppp.fold("shared/raw.rs"))
        self.assertEqual(ppp.fold("Café"), ppp.fold("café"))
        self.assertEqual(ppp.fold("K"), ppp.fold("k"))  # the Kelvin sign

    def test_the_probe_takes_exactly_the_features_it_is_given(self) -> None:
        manifest = toml_loads(
            ppp.probe_manifest(
                {
                    "a": (Path("/w/crates/a"), ["default", "x"]),
                    "b-c": (Path("/w/crates/b c"), []),
                    "d": (Path("/w/crates/d"), None),
                }
            )
        )
        self.assertEqual(
            manifest["dependencies"],
            {
                "a": {"path": "/w/crates/a", "default-features": False, "features": ["default", "x"]},
                "b-c": {"path": "/w/crates/b c", "default-features": False, "features": []},
                "d": {"path": "/w/crates/d"},
            },
        )
        self.assertEqual(manifest["workspace"], {})

    def test_dep_info_is_read_exactly_as_rustc_writes_it(self) -> None:
        # rustc escapes a space and nothing else: on the rule line `/w/c\` and
        # the separator after it read as an escaped space, so the per-name lines
        # decide, and every rule must be exactly them.
        names = ["/w/src/lib.rs", "/w/my dir/x.rs", "/w/c\\", "/w/f: g.txt", "/w/a\\ b", "/w/src/lib.rs"]
        with tempfile.TemporaryDirectory() as scratch:
            dep_info = Path(scratch) / "a-0.d"
            joined = " ".join(name.replace(" ", "\\ ") for name in names)
            dep_info.write_text(
                f"{dep_info}: {joined}\n\n/t/deps/liba-0.rmeta: {joined}\n\n"
                + "".join(name.replace(" ", "\\ ") + ":\n" for name in names)
                + "\n# env-dep:X=1\n# env-dep:Y\n# checksum:sha256=00 file_len:1 /w/src/lib.rs\n",
                encoding="utf-8",
            )
            self.assertEqual(ppp.dep_info_paths(dep_info), names)

    def test_dep_info_rustc_does_not_write_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            dep_info = Path(scratch) / "a-0.d"
            me = str(dep_info)
            for shape, text in {
                "a line continuation": f"{me}: /w/a \\\n /w/b\n\n/w/a:\n/w/b:\n",
                "a name holding a newline": f"{me}: /w/a\nb /w/c\n\n/w/a\nb:\n/w/c:\n",
                "a rule without a name": f"{me}: /w/a\n\n/w/a:\n/w/b:\n",
                "an unescaped space": f"{me}: /w/a b\n\n/w/a b:\n",
                "no rule for itself": "/t/deps/liba-0.rmeta: /w/a\n\n/w/a:\n",
                "no final newline": f"{me}: /w/a\n\n/w/a:",
                "no blank line after a rule": f"{me}: /w/a\n/w/a:\n",
                "no prerequisite": f"{me}: \n\n",
                "env-dep without its blank line": f"{me}: /w/a\n\n/w/a:\n# env-dep:X\n",
                "a comment rustc does not write": f"{me}: /w/a\n\n/w/a:\n\n# other\n",
            }.items():
                with self.subTest(shape=shape):
                    dep_info.write_text(text, encoding="utf-8")
                    with self.assertRaisesRegex(ppp.Refusal, "not dep-info as rustc writes it"):
                        ppp.dep_info_paths(dep_info)
            dep_info.write_bytes(f"{me}: /w/\xff\n\n/w/\xff:\n".encode("latin-1"))
            with self.assertRaisesRegex(ppp.Refusal, "cannot read the dep-info"):
                ppp.dep_info_paths(dep_info)

    def test_the_dep_info_of_a_unit_is_found_in_its_out_directory(self) -> None:
        # Cargo's build directory (Trust 0.12): a build script compiles to
        # `build/<package>/<hash>/out/build_script_build`, without
        # `-C extra-filename`, and rustc writes `build_script_build.d` beside it.
        with tempfile.TemporaryDirectory() as scratch:
            out = Path(scratch) / "debug/build/a/0123/out"
            out.mkdir(parents=True)
            script = {
                "package_id": "path+file:///w/a#0.1.0",
                "target": {"name": "build-script-build", "kind": ["custom-build"]},
                "filenames": [str(out / "build_script_build")],
            }
            library = {
                "package_id": "path+file:///w/a#0.1.0",
                "target": {"name": "a-b", "kind": ["lib"]},
                "filenames": [str(out / "liba_b-0123.rmeta")],
            }
            for message in (script, library):
                with self.subTest(target=message["target"]["name"]):
                    with self.assertRaisesRegex(ppp.Refusal, "no dep-info for"):
                        ppp.dep_info_files(message)
            (out / "build_script_build.d").write_text("", encoding="utf-8")
            (out / "a_b-0123.d").write_text("", encoding="utf-8")
            self.assertEqual(ppp.dep_info_files(script), [out / "build_script_build.d"])
            self.assertEqual(ppp.dep_info_files(library), [out / "a_b-0123.d"])
            # The name is the build script's own: a library's executable-like
            # file or another build script's dep-info is no stand-in.
            other = {**script, "target": {"name": "build-script-main", "kind": ["custom-build"]}}
            with self.assertRaisesRegex(ppp.Refusal, "no dep-info for"):
                ppp.dep_info_files(other)
            self.assertEqual(ppp.build_script_stdout(out), out.parent / "run" / "stdout")

    def test_build_script_output_is_read_as_cargo_reads_it(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            output = Path(scratch) / "output"
            output.write_bytes(
                b"  cargo:rerun-if-changed=../x.txt \r\n"
                b"cargo::rerun-if-changed=y\n"
                b"cargo:rerun-if-changed=\xff\n"  # not UTF-8: Cargo skips the line
                b"not cargo:rerun-if-changed=z\n"
                b"cargo:include=/w/include\n"
                b"cargo::metadata=root=/w\n"
                b"cargo:rustc-link-argument=old-syntax metadata\n"
                b"cargo:rustc-link-arg-bins=-Wl,-v\n"
                b"\x1ccargo:rerun-if-changed=kept\x1c\n"  # Rust's trim keeps U+001C
            )
            self.assertEqual(
                ppp.build_script_directives(output),
                [
                    ("rerun-if-changed", "../x.txt"),
                    ("rerun-if-changed", "y"),
                    ("metadata", "include=/w/include"),
                    ("metadata", "root=/w"),
                    ("metadata", "rustc-link-argument=old-syntax metadata"),
                    ("rustc-link-arg-bins", "-Wl,-v"),
                ],
            )
            self.assertEqual(
                ppp.rustc_flags("-L /a -lfoo  -Lnative=/b -l bar", output),
                (["/a", "native=/b"], ["foo", "bar"]),
            )
            with self.assertRaises(ppp.Refusal):
                ppp.rustc_flags("-L", output)
        self.assertEqual(ppp.search_directory("native=/a=b"), "/a=b")
        self.assertEqual(ppp.search_directory("/a=b"), "/a=b")

    def test_a_build_script_read_that_disagrees_with_cargo_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            base = Path(scratch).resolve()
            tree = base / "tree"
            (tree / "a").mkdir(parents=True)
            run = base / "target/debug/build/a/0"
            (run / "out").mkdir(parents=True)
            (run / "run").mkdir()
            (run / "run/stdout").write_text("cargo:rerun-if-changed=x\n", encoding="utf-8")
            fingerprint = run / "fingerprint/run-build-script-build-script-build.json"
            fingerprint.parent.mkdir()
            member = ppp.Member("a", tree / "a", [], [], [], {})
            message = {"out_dir": str(run / "out"), "linked_paths": [], "linked_libs": []}
            for recorded, linked, error in (
                (["y"], [], "Cargo recorded"),
                (["x"], ["/elsewhere"], "Cargo reported"),
            ):
                with self.subTest(error=error):
                    fingerprint.write_text(
                        json.dumps({"local": [{"RerunIfChanged": {"output": "o", "paths": recorded}}]}),
                        encoding="utf-8",
                    )
                    with self.assertRaisesRegex(ppp.Refusal, error):
                        ppp.build_script_reads(
                            ppp.Reads(tree), member, {**message, "linked_paths": linked}, base / "target"
                        )
            fingerprint.write_text(json.dumps({"local": [{"Unknown": 1}]}), encoding="utf-8")
            with self.assertRaisesRegex(ppp.Refusal, "cannot read what Cargo watches"):
                ppp.build_script_reads(ppp.Reads(tree), member, message, base / "target")

    def test_an_assembler_file_directive_is_told_from_a_word_named_include(self) -> None:
        for text in (
            b'.incbin "x"', b'  .INCBIN \\"x\\"', b'concat!(".incbin \\"", p)', b'.Include\t"a.s"',
            b'.include"a.s"', b'concat!(".include ", "\\"", p)', b'".incbin\\t\\"x\\""',
            b'".incbin \\\n        \\"x\\""', b'r#".incbin "x""#',
        ):
            with self.subTest(text=text):
                self.assertIsNotNone(ppp.ASSEMBLER_FILE_DIRECTIVE.search(text))
        # find-msvc-tools 0.1.11 (a build dependency of trust-ir's closure):
        # `self.include.iter()`, `sdk_info.include)`, `tool.include.push(..)`.
        for text in (
            b"self.include(x)", b"b.include (x)", b".include_lineage", b".includes_license()",
            b'include!("x.rs")', b"#include <a.h>", b'.incbinx "y"', b"f(info.include)",
            b"info.include, x", b"x.include;", b"the `.include` directive", b"self.include.iter()",
            b'x.include == "a"',
        ):
            with self.subTest(text=text):
                self.assertIsNone(ppp.ASSEMBLER_FILE_DIRECTIVE.search(text))

    @staticmethod
    def build_input_reads(
        files: dict[str, bytes], excluded: Sequence[str], patterns: Sequence[str] = ("shared",)
    ) -> set[str]:
        """What the gate reads that the tracked `files` name for the C
        preprocessor or an assembler, crates/a being package a, `excluded` the
        excluded changes and `patterns` the reviewed exclusions."""
        with tempfile.TemporaryDirectory() as scratch:
            tree = Path(scratch).resolve()
            for name, data in files.items():
                (tree / name).parent.mkdir(parents=True, exist_ok=True)
                (tree / name).write_bytes(data)
            reads = ppp.Reads(tree)
            inputs = ppp.BuildInputs(
                tree, {name: "100644" for name in files},
                [(path, ppp.Exclusion("shared", "test")) for path in excluded],
                excluding(*patterns), reads,
            )
            inputs.scan_tree([ppp.Member("a", tree / "crates/a", [], [], [], {})])
            return set(reads.paths)

    def test_a_build_input_reads_what_it_names_wherever_that_is_looked_for(self) -> None:
        shared = ["shared/blob.bin", "shared/blob.inc", "shared/sys/blob.h", "shared/deep.inc"]

        def reads(text: bytes, other: bytes = b".byte 1\n") -> set[str]:
            # x.S is a file of package a; asm/y.S is a file outside it.
            return self.build_input_reads(
                {"crates/a/src/x.S": text, "crates/a/src/own.inc": b".byte 1\n", "asm/y.S": other}, shared
            )

        for text, read in (
            (b'.incbin "../../shared/blob.bin"\n', "shared/blob.bin"),
            (b'  .INCBIN \\"../../shared/blob.bin\\"', "shared/blob.bin"),  # in a Rust literal
            (b'r#".incbin "blob.bin""#', "shared/blob.bin"),
            (b'.incbin "/elsewhere/tree/crates/a/../../shared/blob.bin", 0, 4\n', "shared/blob.bin"),
            (b'.incbin "/elsewhere/tree/shared/blob.bin" // data\n', "shared/blob.bin"),
            (b'#include "blob.inc"\n', "shared/blob.inc"),  # through an -I
            (b"#  include <sys/blob.h>\n", "shared/sys/blob.h"),
            (b'#include_next "BLOB.INC"\n', "shared/blob.inc"),  # folded, as APFS opens it
            (b'#import "blob.inc"\n', "shared/blob.inc"),
            (b'#embed "blob.bin" limit(2)\n', "shared/blob.bin"),
            (b'incbin "blob.bin", 4\n', "shared/blob.bin"),  # NASM
            (b'%include "blob.inc"\n', "shared/blob.inc"),
            (b'#include "../shared/deep.inc"\n', "shared/deep.inc"),
        ):
            with self.subTest(text=text):
                self.assertEqual(reads(text), {read})
                # A file outside the package reads the same: a build script can
                # hand any file of the tree to the tool.
                self.assertEqual(reads(b"", text), {read})
        # A name that reaches no excluded path, however it is looked for.
        for text in (
            b'#include <stdint.h>\n.incbin "data/table.bin"\n#include "own.inc"\n',
            b".byte 1 # .incbin is not used here\n", b"self.include(x)",
            b'    cc::Build::new()\n        .include("src")\n        .compile("x");\n',
            b"the .include directive reads", b'x.include == "a"', b".include_lineage",
            b'/// `incbin!("path")`\npub fn incbin(input: TokenStream) {}\n', b".incbin\n",
        ):
            with self.subTest(text=text):
                self.assertEqual(reads(text), set())
                self.assertEqual(reads(b"", text), set())
        # A name no string literal spells, at the start of a statement: a macro,
        # a define, a template a program fills (r12 verifier: `@BLOB@` and `%s`
        # passed as literal names that reach nothing).
        for text, line in (
            (b".data\n.incbin BLOB_PATH\n", 2),
            (b'#define BLOB "../../shared/blob.bin"\n.incbin BLOB\n', 2),
            (b'let t = format!(".data\\n.incbin {blob:?}\\n");\n', 1),
            (b'concat!(".incbin \\"", p, "\\"")', 1),
            (b'concat!(".include ", "\\"", p)', 1),
            (b"SYM: .incbin FILE\n", 1),
            (b"#include MACRO\n", 1),
            (b'.incbin "$(SHARED)/blob.bin"\n', 1),
            (b'.incbin "@BLOB@"\n', 1),
            (b'#include "@CONFIG_H@"\n', 1),
            (b'.incbin "%BLOB%"\n', 1),
            (b"f.write('.incbin \"%s\"\\n' % path)\n", 1),
        ):
            with self.subTest(text=text):
                with self.assertRaisesRegex(
                    ppp.Refusal, rf"crates/a/src/x\.S \(a file of package a\) spells '\S+' on line {line} "
                    "with a file name that is no string literal",
                ):
                    reads(text)
                with self.assertRaisesRegex(
                    ppp.Refusal, rf"asm/y\.S \(a tracked file a build script can hand the tool\) spells "
                    rf"'\S+' on line {line} with a file name that is no string literal",
                ):
                    reads(b"", text)
        with self.assertRaisesRegex(ppp.Refusal, "keeps no component"):
            reads(b'.include "../.."\n')
        # Under a reviewed exclusion (reviewed as read by no build), a literal
        # name is read and any other is not refused: TrustIR's scripts/ci_gates.sh
        # spells `#    import` in a shell comment.
        for text, read in (
            (b"#                             import the authenticator's own suite\n", set()),
            (b".incbin BLOB_PATH\n", set()),
            (b'.include "../.."\n', set()),
            (b'.incbin "../shared/blob.bin"\n', {"shared/blob.bin"}),
        ):
            with self.subTest(reviewed=text):
                self.assertEqual(
                    self.build_input_reads({"scripts/ci_gates.sh": text}, shared, ("shared", "scripts")), read
                )

    def test_a_rust_file_includes_what_its_literals_name_under_any_cfg(self) -> None:
        source = (
            '// include_str!("../../comment.txt")\n'
            '/* nested /* include_str!("../../comment.txt") */ still a comment */\n'
            '#[cfg(target_os = "linux")]\n'
            'pub fn blob() -> &\'static str { include_str!("../../../shared/blob.bin") }\n'
            "const QUOTE: char = '\"';\n"
            'const TEXT: &str = "include_str!(\\"../../string.txt\\")";\n'
            "const BYTES: &[u8] =\n"
            '    include_bytes!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../shared/", "b.bin"));\n'
            '#[cfg_attr(target_os = "linux", path = "../../../shared/linux.rs")]\nmod imp;\n'
            '#[path = r"x/y.rs"] mod y;\n'
            'include!{"gen.rs"}\n'
            "fn f<'a>(x: &'a str) -> &'a str { x }\n"
            'const RAW: &str = r#"include_str!("raw.txt")"#;\n'
            '#[doc = include_str!("../README.md")]\nstruct S;\n'
            'const OUT: &str = include_str!(concat!(env!("OUT_DIR"), "/generated.txt"));\n'
        )
        self.assertEqual(
            [
                (read.line, read.what, read.spelled, os.path.normpath(read.joined))
                for read in ppp.rust_reads(source, Path("/t/crates/a/src/lib.rs"), Path("/t/crates/a"))
                if read.joined is not None
            ],
            [
                (4, "include_str!", "../../../shared/blob.bin", "/t/shared/blob.bin"),
                (8, "include_bytes!", "/../../shared/b.bin", "/t/shared/b.bin"),
                (9, "path attribute", "../../../shared/linux.rs", "/t/shared/linux.rs"),
                (11, "path attribute", "x/y.rs", "/t/crates/a/src/x/y.rs"),
                (12, "include!", "gen.rs", "/t/crates/a/src/gen.rs"),
                (15, "include_str!", "../README.md", "/t/crates/a/README.md"),
            ],
        )

    def test_the_rust_a_consumer_can_compile_is_read_with_what_it_includes(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            tree = Path(scratch).resolve()
            files = {
                "crates/a/build.rs": 'fn main() { let _ = include_str!("../../shared/build.txt"); }\n',
                "crates/a/src/lib.rs": '#[cfg(windows)]\n#[path = "../../../common/imp.rs"]\nmod imp;\n',
                "common/imp.rs": 'pub const B: &[u8] = include_bytes!("../shared/imp.bin");\n',
                "crates/a/tests/t.rs": 'const T: &str = include_str!("../../../shared/test.txt");\n',
                "crates/a/examples/e.rs": 'const E: &str = include_str!("../../../shared/example.txt");\n',
                "crates/a/src/bin/b.rs": 'const B: &str = include_str!("../../../../shared/bin.txt");\n',
            }
            for name, text in files.items():
                (tree / name).parent.mkdir(parents=True, exist_ok=True)
                (tree / name).write_text(text, encoding="utf-8")
            package = tree / "crates/a"
            member = ppp.Member(
                "a", package, [package, package / "src"], [], [], {},
                uncompiled_roots=(package / "examples", package / "src/bin", package / "tests"),
            )
            reads = ppp.Reads(tree)
            ppp.BuildInputs(tree, {}, [], [], reads).scan_rust([member])
            self.assertEqual(
                sorted(reads.paths), ["common/imp.rs", "shared/build.txt", "shared/imp.bin"]
            )

    def test_usage(self) -> None:
        script = "pinned_package_paths.py"
        self.assertEqual(ppp.main([script, "drift"]), 2)
        self.assertEqual(ppp.main([script, "drift", "--consumer"]), 2)
        self.assertEqual(ppp.main([script, "drift", "--exclusions", "x", "t", "c", "p", "m", "a"]), 2)

    def test_a_build_is_read_as_its_lane_runs_it(self) -> None:
        for command, arguments, targets in (
            # publish/config.sh's ship gate: a `targo trust` lane resolves as the unverified one.
            ("trust check --allow-l0-gaps --locked -p a -p b", ("check", "-p", "a", "-p", "b"), ()),
            ("--unverified test --locked -p trust-mc-core --lib -- --nocapture",
             ("test", "-p", "trust-mc-core", "--lib"), ()),
            ("trust build --certify --hardened --trust-profile unix_hardened --locked -j 2 "
             "--workspace --report-dir '/r/x y'", ("build", "--workspace"), ()),
            ("--unverified build --release --target-dir t -pfoo --features=a,b -j3 -F c",
             ("build", "--release", "-p", "foo", "--features", "a,b", "-F", "c"), ()),
            ("--unverified run --quiet -p compiletest -- --suite x", ("build", "-p", "compiletest"), ()),
            ("--unverified check --all-targets --target aarch64-apple-darwin --profile=profiling",
             ("check", "--all-targets", "--target", "aarch64-apple-darwin", "--profile", "profiling"),
             ("aarch64-apple-darwin",)),
            # scripts/check-trust-verification.sh on Trust 0.12: the dependency
            # scope reaches the compiler through Cargo's rustflags, not TRUSTFLAGS.
            ("trust check --certify --config "
             "\"target.'cfg(all())'.rustflags=['-Ztrust-verify-include-dependencies=yes']\" "
             "--locked --workspace", ("check", "--workspace"), ()),
            ("trust build \"--config=build.rustflags=['-Ztrust-a','-Ztrust-b=1']\" -p a",
             ("build", "-p", "a"), ()),
        ):
            with self.subTest(command=command):
                build = ppp.parse_build("lane", command)
                self.assertEqual((build.arguments, build.targets), (arguments, targets))
        for command, why in (
            ("build", "names no Targo lane"),
            ("--unverified build-dev", "runs no Cargo command"),
            ("--unverified doc", "runs no Cargo command"),
            ("--unverified build --config profile.dev.panic='abort'", "'--config'"),
            # Only a trust lane's rustflags made of Trust verification options.
            ("--unverified build --config \"build.rustflags=['-Ztrust-a']\"", "'--config'"),
            ("trust build --config \"profile.dev.panic='abort'\"", "'--config'"),
            ("trust build --config \"build.rustflags=['--cfg','x']\"", "'--config'"),
            ("trust build --config \"build.rustflags=['-Ztrust-a','-Copt-level=0']\"", "'--config'"),
            ("trust build --config build.rustflags=[]", "'--config'"),
            ("trust build --config \"build.rustflags='-Ztrust-a'\"", "'--config'"),
            ("trust build --config \"build.rustflags=['-Ztrust-a']\" --config \"build.jobs=1\"",
             "'--config'"),
            ("trust build --config \"target.'cfg(unix)'.linker='cc'\"", "'--config'"),
            ("trust build --config \"build.rustflags=['-Ztrust-a']\" --config",
             "gives --config no value"),
            ("trust build --config ../other.toml", "'--config'"),
            ("--unverified build -Z build-std", "'-Z'"),
            ("--unverified build --manifest-path x/Cargo.toml", "'--manifest-path'"),
            ("--unverified check --allow-l0-gaps", "'--allow-l0-gaps'"),
            ("trust check --standalone", "'--standalone'"),
            ("--unverified build -- x", "passes `--` to `build`"),
            ("--unverified build --features", "gives --features no value"),
            ("--unverified build --release=yes", "gives --release, which takes none, a value"),
            ("--unverified build 'open", "is no command line"),
        ):
            with self.subTest(command=command):
                with self.assertRaisesRegex(ppp.Refusal, f"{re.escape(why)}.*cannot be derived"):
                    ppp.parse_build("lane", command)

    def test_the_builds_are_read_from_the_list_each_with_its_command(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            listed = Path(scratch) / "x.toml"
            listed.write_text(
                f'[{ppp.CONSUMER_BUILDS}]\n"ship" = "--unverified build -p a"\n"t" = "trust check"\n',
                encoding="utf-8",
            )
            self.assertEqual(
                [(build.lane, build.arguments) for build in ppp.load_consumer_builds(listed)],
                [("ship", ("build", "-p", "a")), ("t", ("check",))],
            )
            listed.write_text("[one]\n", encoding="utf-8")
            self.assertEqual(ppp.load_consumer_builds(listed), [])
            for text in (f'{ppp.CONSUMER_BUILDS} = 1\n', f'[{ppp.CONSUMER_BUILDS}]\n"x" = ""\n',
                         f'[{ppp.CONSUMER_BUILDS}]\n"x" = 1\n', f'[{ppp.CONSUMER_BUILDS}]\n"x" = "doc"\n'):
                with self.subTest(text=text):
                    listed.write_text(text, encoding="utf-8")
                    with self.assertRaises(ppp.Refusal):
                        ppp.load_consumer_builds(listed)

    def test_a_probe_asks_for_each_package_as_the_build_compiled_it(self) -> None:
        crates_io = "registry+https://github.com/rust-lang/crates.io-index"
        packages = {
            f"{crates_io}#serde@1.0.1": {"id": f"{crates_io}#serde@1.0.1", "name": "serde",
                                        "version": "1.0.1", "source": crates_io},
            f"{crates_io}#serde@0.9.0": {"id": f"{crates_io}#serde@0.9.0", "name": "serde",
                                        "version": "0.9.0", "source": crates_io},
            "git+https://g/h.git?rev=ab%2Fc#h@0.2.0": {
                "id": "git+https://g/h.git?rev=ab%2Fc#h@0.2.0", "name": "h", "version": "0.2.0",
                "source": "git+https://g/h.git?rev=ab%2Fc#0123"},
            "path+file:///c/a#0.1.0": {"id": "path+file:///c/a#0.1.0", "name": "a", "version": "0.1.0",
                                       "source": None, "manifest_path": "/c/a/Cargo.toml"},
            "path+file:///o/l#0.3.0": {"id": "path+file:///o/l#0.3.0", "name": "l", "version": "0.3.0",
                                       "source": None, "manifest_path": "/o/l/Cargo.toml"},
        }
        requests = {
            (f"{crates_io}#serde@1.0.1", ppp.TARGET_SIDE): ("derive", "std"),
            (f"{crates_io}#serde@1.0.1", ppp.HOST_SIDE): ("std",),
            (f"{crates_io}#serde@0.9.0", ppp.TARGET_SIDE): (),
            ("git+https://g/h.git?rev=ab%2Fc#h@0.2.0", ppp.HOST_SIDE): ("default",),
            ("path+file:///c/a#0.1.0", ppp.TARGET_SIDE): ("x",),
            ("path+file:///o/l#0.3.0", ppp.TARGET_SIDE): (),
        }
        build = ppp.parse_build("lane", "--unverified build")
        cone = ppp.BuildCone(build, {}, requests, frozenset({"a"}), {"path+file:///c/a#0.1.0": "a"})
        manifest = toml_loads(
            ppp.reproducing_manifest(cone, packages, {"path+file:///c/a#0.1.0": Path("/tree/crates/a")})
        )
        self.assertEqual(manifest["package"]["build"], "build.rs")
        entry = {"default-features": False}
        self.assertEqual(
            sorted(manifest["dependencies"].values(), key=lambda each: (each["package"], each["version"])),
            [
                {**entry, "package": "a", "path": "/tree/crates/a", "version": "=0.1.0", "features": ["x"]},
                {**entry, "package": "l", "path": "/o/l", "version": "=0.3.0", "features": []},
                {**entry, "package": "serde", "version": "=0.9.0", "features": []},
                {**entry, "package": "serde", "version": "=1.0.1", "features": ["derive", "std"]},
            ],
        )
        self.assertEqual(
            sorted(manifest["build-dependencies"].values(), key=lambda each: each["package"]),
            [
                {**entry, "package": "h", "git": "https://g/h.git", "rev": "ab/c", "version": "=0.2.0",
                 "features": ["default"]},
                {**entry, "package": "serde", "version": "=1.0.1", "features": ["std"]},
            ],
        )
        for source in ("registry+https://other/index", "git+https://g/h.git?rev=a&branch=b#0"):
            with self.subTest(source=source):
                strange = {"id": "x#y@1.0.0", "name": "y", "version": "1.0.0", "source": source}
                with self.assertRaisesRegex(ppp.Refusal, "cannot spell"):
                    ppp.reproducing_manifest(
                        ppp.BuildCone(build, {}, {("x#y@1.0.0", ppp.TARGET_SIDE): ()}, frozenset(), {}),
                        {"x#y@1.0.0": strange}, {},
                    )


# TrustIR's shape: trust-ir-build path-depends on trust-ir and trust-ir-giveback
# and dev-depends on trust-ir-conformance; trust-ir-cli depends on
# trust-ir-build. Each member inherits its version, trust-ir-build also its
# lints and a workspace dependency.
MEMBER = '[package]\nname = "{name}"\nversion.workspace = true\nedition = "2021"\n'
TRUST_IR_WORKSPACE = {
    "crates/trust-ir/Cargo.toml": MEMBER.format(name="trust-ir"),
    "crates/trust-ir/src/lib.rs": "pub fn ir() {}\n",
    "crates/trust-ir/README.md": "trust-ir\n",
    "crates/trust-ir/tests/t.rs": "#[test]\nfn t() {}\n",
    "crates/trust-ir-giveback/Cargo.toml": MEMBER.format(name="trust-ir-giveback"),
    "crates/trust-ir-giveback/src/lib.rs": "pub fn giveback() {}\n",
    "crates/trust-ir-build/Cargo.toml": MEMBER.format(name="trust-ir-build")
    + "[dependencies]\ntrust-ir = { path = \"../trust-ir\" }\n"
    + "trust-ir-giveback = { path = \"../trust-ir-giveback\" }\n"
    + "helper = { workspace = true }\n"
    + "[dev-dependencies]\ntrust-ir-conformance = { path = \"../trust-ir-conformance\" }\n"
    + "[lints]\nworkspace = true\n",
    "crates/trust-ir-build/src/lib.rs": "pub fn build() {}\n",
    "crates/helper/Cargo.toml": MEMBER.format(name="helper"),
    "crates/helper/src/lib.rs": "pub fn help() {}\n",
    "crates/trust-ir-conformance/Cargo.toml": MEMBER.format(name="trust-ir-conformance"),
    "crates/trust-ir-conformance/src/lib.rs": "pub fn battery() {}\n",
    "crates/trust-ir-cli/Cargo.toml": MEMBER.format(name="trust-ir-cli")
    + "[dependencies]\ntrust-ir-build = { path = \"../trust-ir-build\" }\n",
    "crates/trust-ir-cli/src/lib.rs": "pub fn cli() {}\n",
    "docs/spec.md": "spec\n",
}
PINNED = ["trust-ir", "trust-ir-build"]


def root_manifest(version: str = "0.10.0", helper: str = "", cli: str = "4") -> str:
    return (
        '[workspace]\nmembers = ["crates/*"]\nresolver = "2"\n'
        f'[workspace.package]\nversion = "{version}"\n'
        f'[workspace.dependencies]\nhelper = {{ path = "crates/helper"{helper} }}\n'
        f'unused = "{cli}"\n'
        '[workspace.lints.rust]\nunsafe_code = "forbid"\n'
    )


class WholeTreeTests(unittest.TestCase):
    """A checkout shaped like TrustIR. Without exclusions, every changed path is
    drift: a670291ab diffed only the closure's directories and the root
    manifest's inherited keys, so a change elsewhere left the pin standing."""

    def setUp(self) -> None:
        self.scratch = tempfile.TemporaryDirectory()
        self.repo = GitRepo(Path(self.scratch.name).resolve() / "trust-ir")
        self.pin = self.repo.commit({"Cargo.toml": root_manifest(), **TRUST_IR_WORKSPACE})

    def tearDown(self) -> None:
        self.scratch.cleanup()

    def drifted(self, live_main: str, exclusions: Sequence = ()) -> list[str]:
        return ppp.drift(TARGO, self.repo.root, self.pin, live_main, PINNED, None, exclusions).drifted

    def test_a_change_to_a_path_dependency_of_a_pinned_package_is_drift(self) -> None:
        giveback = self.repo.commit({"crates/trust-ir-giveback/src/lib.rs": "pub fn g() {}\n"})
        self.assertEqual(self.drifted(giveback), ["crates/trust-ir-giveback/src/lib.rs"])
        helper = self.repo.commit({"crates/helper/src/lib.rs": "pub fn h() {}\n"})
        self.assertEqual(
            self.drifted(helper),
            ["crates/helper/src/lib.rs", "crates/trust-ir-giveback/src/lib.rs"],
        )

    def test_any_change_to_the_root_manifest_is_drift(self) -> None:
        # a670291ab compared only the inherited keys and reported [] here.
        unused = self.repo.commit({"Cargo.toml": root_manifest(cli="5") + "[patch.crates-io]\n"})
        self.assertEqual(self.drifted(unused), ["Cargo.toml"])

    def test_a_change_to_a_crate_nothing_pinned_depends_on_is_drift(self) -> None:
        # A dependent, a dev-dependency, prose: a670291ab reported [].
        live_main = self.repo.commit(
            {
                "crates/trust-ir-cli/src/lib.rs": "pub fn moved() {}\n",
                "crates/trust-ir-conformance/src/lib.rs": "pub fn moved() {}\n",
                "docs/spec.md": "moved\n",
            }
        )
        self.assertEqual(
            self.drifted(live_main),
            [
                "crates/trust-ir-cli/src/lib.rs",
                "crates/trust-ir-conformance/src/lib.rs",
                "docs/spec.md",
            ],
        )

    def test_what_nothing_pinned_reads_passes_once_excluded(self) -> None:
        live_main = self.repo.commit(
            {
                "crates/trust-ir-cli/src/lib.rs": "pub fn moved() {}\n",
                "crates/trust-ir-conformance/src/lib.rs": "pub fn moved() {}\n",
                "docs/spec.md": "moved\n",
            }
        )
        result = ppp.drift(
            TARGO, self.repo.root, self.pin, live_main, PINNED, None,
            excluding("docs", "crates/trust-ir-cli/src", "crates/trust-ir-conformance/src"),
        )
        self.assertEqual(result.drifted, [])
        self.assertEqual(len(result.excluded), 3)

    def test_the_inputs_are_read_from_the_pin_not_the_working_tree(self) -> None:
        live_main = self.repo.commit({"crates/trust-ir-giveback/src/lib.rs": "pub fn g() {}\n"})
        # The working tree sits past live main and has lost the giveback crate.
        self.repo.commit({"crates/trust-ir-giveback": None})
        self.assertEqual(self.drifted(live_main), ["crates/trust-ir-giveback/src/lib.rs"])

    def test_the_command_exits_one_on_drift_and_names_what_changed(self) -> None:
        live_main = self.repo.commit({"crates/trust-ir-giveback/src/lib.rs": "pub fn g() {}\n"})
        drifted = gate(self.repo, self.pin, live_main, *PINNED)
        self.assertEqual(drifted.returncode, 1, drifted.stderr)
        self.assertIn("changed: crates/trust-ir-giveback/src/lib.rs", drifted.stderr)
        self.assertEqual(drifted.stdout.strip(), "1 changed paths, 1 of them drift")
        unchanged = gate(self.repo, self.pin, self.pin, *PINNED)
        self.assertEqual(unchanged.returncode, 0, unchanged.stderr)
        self.assertEqual(unchanged.stdout.strip(), "no path changed")

    def test_the_command_takes_the_reviewed_list_and_exits_two_on_a_read_exclusion(self) -> None:
        listed = Path(self.scratch.name) / "exclusions.toml"
        listed.write_text(
            '[trust-ir]\n"docs" = "prose"\n"crates/trust-ir-giveback/src" = "wrong"\n',
            encoding="utf-8",
        )
        command = [
            sys.executable, str(SCRIPTS / "pinned_package_paths.py"), "drift", "--exclusions",
            str(listed), "--repository", "trust-ir", TARGO, str(self.repo.root), self.pin,
        ]
        prose = self.repo.commit({"docs/spec.md": "moved\n"})
        passed = subprocess.run([*command, prose, *PINNED], capture_output=True, text=True)
        self.assertEqual(passed.returncode, 0, passed.stderr)
        self.assertIn("all under reviewed exclusions docs", passed.stdout)
        giveback = self.repo.commit({"crates/trust-ir-giveback/src/lib.rs": "pub fn g() {}\n"})
        refused = subprocess.run([*command, giveback, *PINNED], capture_output=True, text=True)
        self.assertEqual(refused.returncode, 2, refused.stderr)
        self.assertIn("trust-ir-giveback reads crates/trust-ir-giveback/src/lib.rs", refused.stderr)
        missing = subprocess.run([*command, prose, "trust-ir-ay"], capture_output=True, text=True)
        self.assertEqual(missing.returncode, 2, missing.stderr)
        self.assertIn("declares no package", missing.stderr)


class WhatAnEarlierGatePassedTests(OneCrate):
    """Shapes where live main changes what a consumer of `a` builds and an
    earlier gate exited 0. Each runs the gate's command as check-shared-pins
    runs it, without an exclusion list, so it runs against every version.
    Measured (r8 verifier): a670291ab exits 0 on the first five; 339e1a7a5 also
    on the last."""

    def assert_gate_drift(self, pin: str, live_main: str, *changed: str) -> None:
        result = gate(self.repo, pin, live_main)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        for path in changed:
            self.assertIn(f"changed: {path}\n", result.stderr)

    def test_a_build_script_spelled_in_another_case_than_its_package_is_drift(self) -> None:
        # Next to tracked crates/a, live main adds crates/A/build.rs. A checkout
        # on APFS writes it into crates/a, and Cargo runs it (verifier: a Git
        # consumer's MODE went 1 -> 2).
        pin = self.pin(
            {
                "crates/a/src/lib.rs": (
                    "#[cfg(not(tuned))]\npub const MODE: u32 = 1;\n"
                    "#[cfg(tuned)]\npub const MODE: u32 = 2;\n"
                )
            }
        )
        live_main = self.repo.stage(
            {"crates/A/build.rs": ("100644", 'fn main() { println!("cargo:rustc-cfg=tuned"); }\n')}
        )
        self.assert_gate_drift(pin, live_main, "crates/A/build.rs")

    def test_a_path_dependency_through_a_symbolic_link_live_main_repoints_is_drift(self) -> None:
        # `b` is reached as ../../links/b, a link to crates/b, on a target this
        # host is not or as an optional dependency, so no check builds it; live
        # main re-points the link at vendor/b (verifier: B went 1 -> 2 for a Git
        # and a path consumer).
        for dependency in (
            '[target.\'cfg(target_os = "linux")\'.dependencies]\nb = { path = "../../links/b" }\n',
            '[dependencies]\nb = { path = "../../links/b", optional = true }\n',
        ):
            with self.subTest(dependency=dependency):
                pin = self.pin(
                    {
                        "Cargo.toml": (
                            '[workspace]\nmembers = ["crates/a", "crates/b"]\n'
                            'exclude = ["links", "vendor"]\n'
                        ),
                        "crates/a/Cargo.toml": PACKAGE.format("a") + dependency,
                        "crates/a/src/lib.rs": "",
                        "crates/b/Cargo.toml": PACKAGE.format("b"),
                        "crates/b/src/lib.rs": "pub const B: u32 = 1;\n",
                        "vendor/b/Cargo.toml": PACKAGE.format("b") + "[workspace]\n",
                        "vendor/b/src/lib.rs": "pub const B: u32 = 2;\n",
                    },
                    {"links/b": "../crates/b"},
                )
                live_main = self.repo.commit({}, {"links/b": "../vendor/b"})
                self.assert_gate_drift(pin, live_main, "links/b")

    def test_a_root_gitattributes_change_is_drift(self) -> None:
        # Cargo's Git checkout applies it: include_str!("t.txt") went from 8
        # bytes to 10 (verifier).
        pin = self.pin(
            {
                "crates/a/src/lib.rs": 'pub const T: &str = include_str!("t.txt");\n',
                "crates/a/src/t.txt": "one\ntwo\n",
            }
        )
        live_main = self.repo.commit({".gitattributes": "*.txt text eol=crlf\n"})
        self.assert_gate_drift(pin, live_main, ".gitattributes")

    def test_another_manifest_declaring_a_pinned_package_name_is_drift(self) -> None:
        # A Git consumer resolves `a -> b { path = "../b" }` by name over every
        # manifest of the checkout and takes the highest version: B went 1 -> 2
        # (verifier).
        pin = self.pin(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a", "crates/b"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a") + '[dependencies]\nb = { path = "../b" }\n',
                "crates/a/src/lib.rs": "pub use b::B;\n",
                "crates/b/Cargo.toml": PACKAGE.format("b"),
                "crates/b/src/lib.rs": "pub const B: u32 = 1;\n",
            }
        )
        live_main = self.repo.commit(
            {
                "evals/fixture/b/Cargo.toml": (
                    '[package]\nname = "b"\nversion = "0.2.0"\nedition = "2021"\n[workspace]\n'
                ),
                "evals/fixture/b/src/lib.rs": "pub const B: u32 = 2;\n",
            }
        )
        self.assert_gate_drift(pin, live_main, "evals/fixture/b/Cargo.toml")

    def test_a_workspace_manifest_between_the_package_and_the_root_is_drift(self) -> None:
        # crates/Cargo.toml becomes the workspace crates/a inherits from:
        # CARGO_PKG_VERSION went 0.1.0 -> 9.9.9 for a Git and a path consumer.
        pin = self.pin(
            {
                "Cargo.toml": (
                    '[workspace]\nmembers = ["crates/a"]\n[workspace.package]\nversion = "0.1.0"\n'
                ),
                "crates/a/Cargo.toml": (
                    '[package]\nname = "a"\nversion.workspace = true\nedition = "2021"\n'
                ),
                "crates/a/src/lib.rs": 'pub const V: &str = env!("CARGO_PKG_VERSION");\n',
            }
        )
        live_main = self.repo.commit(
            {
                "crates/Cargo.toml": (
                    '[workspace]\nmembers = ["a"]\n[workspace.package]\nversion = "9.9.9"\n'
                )
            }
        )
        self.assert_gate_drift(pin, live_main, "crates/Cargo.toml")

    def test_a_build_script_live_main_adds_to_a_package_with_none_is_drift(self) -> None:
        # No build script at the pin and no `package.build` key: Cargo finds
        # live main's build.rs, which turns on a cfg of the unchanged lib.rs.
        pin = self.pin(
            {
                "crates/a/src/lib.rs": (
                    "#[cfg(not(tuned))]\npub const MODE: u32 = 1;\n"
                    "#[cfg(tuned)]\npub const MODE: u32 = 2;\n"
                )
            }
        )
        live_main = self.repo.commit(
            {"crates/a/build.rs": 'fn main() {\n    println!("cargo:rustc-cfg=tuned");\n}\n'}
        )
        self.assert_gate_drift(pin, live_main, "crates/a/build.rs")


class WhatAnExclusionNeverCoversTests(OneCrate):
    """Under an exclusion, a change Cargo or git reads by name, one read through
    a link or submodule, and one a case-insensitive checkout folds onto another
    spelling are drift, whatever the reason given for the pattern."""

    def test_what_cargo_or_git_reads_by_name_is_drift(self) -> None:
        pin = self.pin(
            {
                "crates/a/src/lib.rs": "",
                "evals/b/Cargo.toml": PACKAGE.format("eval-b") + "[workspace]\n",
                "evals/b/src/lib.rs": "",
            }
        )
        for path in (
            "evals/b/Cargo.toml",
            "evals/c/Cargo.toml",
            "evals/b/.gitattributes",
            "evals/.gitmodules",
            "evals/b/.cargo/config.toml",
            "evals/b/build.rs",
        ):
            with self.subTest(path=path):
                live_main = self.repo.after(pin, {path: "x = 1\n"})
                drifted = self.drift(pin, live_main, excluding("evals")).drifted
                self.assertEqual(len(drifted), 1, drifted)
                self.assertTrue(drifted[0].startswith(f"{path} (under exclusion evals, but"), drifted)

    def test_a_manifest_spelled_in_another_case_is_drift(self) -> None:
        pin = self.pin({"crates/a/src/lib.rs": ""})
        live_main = self.repo.stage({"evals/b/CARGO.TOML": ("100644", PACKAGE.format("a"))})
        drifted = self.drift(pin, live_main, excluding("evals")).drifted
        self.assertEqual(drifted, [
            "evals/b/CARGO.TOML (under exclusion evals, but Cargo or git reads CARGO.TOML by name)"
        ])

    def test_a_build_rs_that_is_no_build_script_can_be_excluded(self) -> None:
        pin = self.pin(
            {
                "crates/a/src/lib.rs": "",
                "evals/b/Cargo.toml": PACKAGE.format("eval-b") + "[workspace]\n",
                "evals/b/src/lib.rs": "mod build;\n",
                "evals/b/src/build.rs": "",
            }
        )
        live_main = self.repo.commit({"evals/b/src/build.rs": "pub fn moved() {}\n"})
        self.assert_unread(pin, live_main, excluding("evals"))

    def test_a_symbolic_link_or_a_submodule_under_an_exclusion_is_drift(self) -> None:
        pin = self.pin({"crates/a/src/lib.rs": "", "docs/x.md": "x\n"})
        link = self.repo.commit({}, {"docs/link.rs": "../crates/a/src/lib.rs"})
        self.assertEqual(
            self.drift(pin, link, excluding("docs")).drifted,
            ["docs/link.rs (under exclusion docs, but mode 120000 is no regular file: what is "
             "read through it changes)"],
        )
        retyped = self.repo.commit({"docs/x.md": None}, {"docs/x.md": "../crates/a/Cargo.toml"})
        self.assertIn("mode 120000", self.drift(link, retyped, excluding("docs")).drifted[0])
        submodule = self.repo.stage({"docs/vendor": ("160000", pin)})
        self.assertIn("mode 160000", self.drift(retyped, submodule, excluding("docs")).drifted[0])

    def test_a_spelling_another_tracked_path_folds_onto_is_drift(self) -> None:
        # On APFS, docs/ and Docs/ are one directory: a change under the
        # excluded spelling rewrites what the other spelling's reader opens.
        self.pin({"crates/a/src/lib.rs": "", "docs/x.md": "x\n"})
        pin = self.repo.stage({"Docs/keep.rs": ("100644", "pub fn keep() {}\n")})
        live_main = self.repo.stage({"docs/x.md": ("100644", "moved\n")})
        self.assertEqual(
            self.drift(pin, live_main, excluding("docs")).drifted,
            ["docs/x.md (under exclusion docs, but tracked Docs folds onto docs)"],
        )
        added = self.repo.stage({"DOCS/y.md": ("100644", "y\n")})
        self.assertIn("DOCS/y.md", self.drift(live_main, added, excluding("docs")).drifted)


class WhatThePinnedPackagesReadTests(OneCrate):
    """When every change is excluded, the exclusions must be unread at the pin;
    each of these reads one, so the gate refuses (exit 2)."""

    def test_an_exclusion_nothing_reads_passes_and_one_change_outside_it_is_drift(self) -> None:
        pin = self.pin({"crates/a/src/lib.rs": "", "docs/x.md": "x\n"})
        prose = self.repo.commit({"docs/x.md": "moved\n"})
        result = self.drift(pin, prose, excluding("docs"))
        self.assertEqual((result.drifted, [path for path, _ in result.excluded]), ([], ["docs/x.md"]))
        self.assertIn("1 feature set x dev and release", result.describe())
        both = self.repo.commit({"docs/x.md": "again\n", "crates/a/src/lib.rs": "pub fn a() {}\n"})
        self.assertEqual(self.drift(pin, both, excluding("docs")).drifted, ["crates/a/src/lib.rs"])

    def test_a_directory_of_the_closure_is_read_whatever_this_host_compiles(self) -> None:
        # A fixture `a` reads at run time; `b` on another target; `c` optional;
        # a lib root outside the package with a module only Linux compiles.
        pin = self.pin(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/*"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a")
                + '[lib]\npath = "../../shared/lib.rs"\n'
                + '[target.\'cfg(target_os = "none")\'.dependencies]\nb = { path = "../b" }\n'
                + '[dependencies]\nc = { path = "../c", optional = true }\n',
                "crates/a/fixtures/f.json": "{}\n",
                "shared/lib.rs": '#[cfg(target_os = "linux")]\nmod linux;\n',
                "shared/linux.rs": "",
                "crates/b/Cargo.toml": PACKAGE.format("b"),
                "crates/b/src/lib.rs": "",
                "crates/c/Cargo.toml": PACKAGE.format("c"),
                "crates/c/src/lib.rs": "",
            }
        )
        for path, pattern, reader in (
            ("crates/a/fixtures/f.json", "crates/a/fixtures", "package a reads crates/a"),
            ("crates/b/notes.txt", "crates/b/notes.txt", "package b reads crates/b"),
            ("crates/c/notes.txt", "crates/*/notes.txt", "package c reads crates/c"),
            ("shared/linux.rs", "shared", "a crate root of a reads shared"),
        ):
            with self.subTest(path=path):
                live_main = self.repo.after(pin, {path: "// moved\n"})
                self.assert_read(pin, live_main, excluding(pattern), reader)

    def test_a_file_the_manifest_names_is_read(self) -> None:
        pin = self.pin(
            {
                "crates/a/Cargo.toml": PACKAGE.format("a") + 'readme = "../../docs/README.md"\n',
                "crates/a/src/lib.rs": "",
                "docs/README.md": "a\n",
            }
        )
        live_main = self.repo.commit({"docs/README.md": "moved\n"})
        self.assert_read(pin, live_main, excluding("docs"), "the manifest of a reads docs/README.md")

    def test_every_spelling_rustc_resolves_is_read(self) -> None:
        # The shapes that static source walks (d5043a82e, 3016e279d) missed;
        # rustc's dep-info names each.
        shapes = {
            "alias": ("use core::include_str as text;\n"
                      'pub const T: &str = text!("../../../shared/x.txt");\n'),
            "macro argument": ("macro_rules! call {\n    ($m:ident, $p:literal) => { $m!($p) };\n}\n"
                               'pub const C: &str = call!(include_str, "../../../shared/x.txt");\n'),
            "assembled path": ("macro_rules! module {\n"
                               "    ($key:ident = $file:literal, $name:ident $end:tt) => {\n"
                               "        #[$key = $file] pub mod $name $end\n    };\n}\n"
                               'module!(path = "../../../shared/x.txt", wrapped;);\n'),
            "not a shebang": ("#!/* not a shebang */[allow(unused)] pub const B: &str = "
                              'include_str!("../../../shared/x.txt");\n'),
            "braces": 'pub const B: &str = include_str! { "../../../shared/x.txt" };\n',
            "brackets": 'pub const K: &[u8] = ::core::include_bytes!["../../../shared/x.txt"];\n',
            "raw path": '#[path = r"../../../shared/x.txt"]\nmod raw;\n',
            "cfg_attr path": '#[cfg_attr(all(), path = "../../../shared/x.txt")]\nmod p;\n',
            "include chain": 'include!("../../../shared/gen.in");\n',
            "macro_rules body": "#[macro_use]\nmod m;\npub const D: &str = data!();\n",
        }
        for name, lib in shapes.items():
            with self.subTest(shape=name):
                pin = self.pin(
                    {
                        "crates/a/src/lib.rs": lib,
                        "crates/a/src/m.rs": (
                            'macro_rules! data {\n    () => { include_str!("../../../shared/x.txt") };\n}\n'
                        ),
                        "crates/a/src/platform.rs": "",
                        "shared/gen.in": 'include!("x.txt");\n',
                        "shared/x.txt": "",
                    }
                )
                live_main = self.repo.commit({"shared/x.txt": "// moved\n"})
                self.assert_read(pin, live_main, excluding("shared"), "reads shared/x.txt")

    def test_a_spelling_in_another_case_is_read_as_what_it_folds_to(self) -> None:
        if not folds_case(self.repo.root):
            self.skipTest("this file system does not fold case, so the spelling does not compile")
        pin = self.pin(
            {
                "crates/a/src/lib.rs": '#[path = "../../../SHARED/Raw.rs"]\nmod raw;\n',
                "shared/raw.rs": "",
            }
        )
        live_main = self.repo.commit({"shared/raw.rs": "// moved\n"})
        self.assert_read(pin, live_main, excluding("shared"), "reads SHARED/Raw.rs")

    def test_what_only_the_release_profile_compiles_is_read(self) -> None:
        pin = self.pin(
            {
                "crates/a/src/lib.rs": (
                    '#[cfg(not(debug_assertions))]\npub const R: &str = '
                    'include_str!("../../../shared/r.txt");\n'
                ),
                "shared/r.txt": "",
            }
        )
        live_main = self.repo.commit({"shared/r.txt": "moved\n"})
        self.assert_read(pin, live_main, excluding("shared"), "\\(a\\) --release reads shared/r.txt")

    def test_a_crate_testing_overflow_checks_apart_from_debug_assertions_is_refused(self) -> None:
        # trust-mc's dev profile turns debug assertions off for dependencies and
        # leaves overflow checks on; the checks only pair them (dev, release).
        pin = self.pin(
            {
                "crates/a/src/lib.rs": (
                    "#![feature(cfg_overflow_checks)]\n"
                    '#[cfg(all(overflow_checks, not(debug_assertions)))]\n'
                    'pub const X: &str = include_str!("../../../shared/x.txt");\n'
                ),
                "shared/x.txt": "",
            }
        )
        live_main = self.repo.commit({"shared/x.txt": "moved\n"})
        self.assert_read(pin, live_main, excluding("shared"), r"enables cfg\(overflow_checks\)")

    def test_what_a_build_script_watches_is_read_and_its_siblings_are_not(self) -> None:
        pin = self.pin(
            {
                "crates/a/build.rs": (
                    'fn main() { println!("cargo:rerun-if-changed=../../shared/assets"); }\n'
                ),
                "crates/a/src/lib.rs": "",
                "shared/assets/one.txt": "",
                "shared/other.txt": "",
            }
        )
        watched = self.repo.commit({"shared/assets/two.txt": "new\n"})
        self.assert_read(pin, watched, excluding("shared"), BUILD_SCRIPT_LITERAL)
        with without_build_inputs():
            self.assert_read(pin, watched, excluding("shared"), "build script of a reads shared/assets")
        unwatched = self.repo.commit({"shared/assets/two.txt": None, "shared/other.txt": "x\n"})
        self.assert_unread(pin, unwatched, excluding("shared"))

    def test_the_target_of_a_symbolic_link_is_read(self) -> None:
        # Behind a cfg no check takes, the compiler never opens the link.
        pin = self.pin(
            {"crates/a/src/lib.rs": '#[cfg(target_os = "none")]\nmod linux;\n',
             "shared/linux.rs": ""},
            {"crates/a/src/linux.rs": "../../../shared/linux.rs"},
        )
        live_main = self.repo.commit({"shared/linux.rs": "pub fn moved() {}\n"})
        self.assert_read(
            pin, live_main, excluding("shared"), "symbolic link crates/a/src/linux.rs reads shared"
        )

    def test_another_manifest_of_the_pin_declaring_a_closure_name_is_refused(self) -> None:
        # A Git consumer may build evals/b as `b`, so its sources are read.
        pin = self.pin(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a", "crates/b"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a") + '[dependencies]\nb = { path = "../b" }\n',
                "crates/a/src/lib.rs": "",
                "crates/b/Cargo.toml": PACKAGE.format("b"),
                "crates/b/src/lib.rs": "",
                "evals/b/Cargo.toml": PACKAGE.format("b").replace("0.1.0", "0.2.0") + "[workspace]\n",
                "evals/b/src/lib.rs": "",
            }
        )
        live_main = self.repo.commit({"evals/b/src/lib.rs": "pub fn moved() {}\n"})
        self.assert_read(pin, live_main, excluding("evals"), "evals/b/Cargo.toml declares package 'b'")
        unparsed = self.repo.commit(
            {"evals/b/Cargo.toml": 'this is not toml, "a"\n', "evals/b/src/lib.rs": "pub fn b() {}\n"}
        )
        again = self.repo.commit({"evals/b/src/lib.rs": "pub fn again() {}\n"})
        self.assert_read(unparsed, again, excluding("evals"), "declares package 'a'")

    def test_a_path_dependency_no_member_of_the_workspace_is_refused(self) -> None:
        pin = self.pin(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a"]\nexclude = ["vendor/v"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a")
                + '[target.\'cfg(target_os = "none")\'.dependencies]\nv = { path = "../../vendor/v" }\n',
                "crates/a/src/lib.rs": "",
                "vendor/v/Cargo.toml": PACKAGE.format("v"),
                "vendor/v/src/lib.rs": "",
                "docs/x.md": "",
            }
        )
        live_main = self.repo.commit({"docs/x.md": "moved\n"})
        self.assert_read(pin, live_main, excluding("docs"), "no member of the pinned workspace")

    def test_a_generated_file_is_refused(self) -> None:
        pin = self.pin(
            {
                "crates/a/build.rs": (
                    "fn main() {\n"
                    '    let out = std::env::var("OUT_DIR").unwrap();\n'
                    '    std::fs::write(format!("{out}/gen.rs"), "pub fn gen() {}").unwrap();\n'
                    '    println!("cargo:rerun-if-changed=build.rs");\n'
                    "}\n"
                ),
                "crates/a/src/lib.rs": 'include!(concat!(env!("OUT_DIR"), "/gen.rs"));\n',
                "docs/x.md": "",
            }
        )
        live_main = self.repo.commit({"docs/x.md": "moved\n"})
        self.assert_read(pin, live_main, excluding("docs"), "not pinned content")


def check_revision(repo: GitRepo, revision: str, work: Path) -> subprocess.CompletedProcess:
    """`targo --unverified check` of crates/a in a fresh checkout of `revision`."""
    tree = work / revision[:12]
    subprocess.run(["git", "clone", "-q", str(repo.root), str(tree)], check=True)
    subprocess.run(["git", "-C", str(tree), "checkout", "-q", revision], check=True)
    return subprocess.run(
        [TARGO, "--unverified", "check", "--offline", "--message-format=json",
         "--manifest-path", str(tree / "crates/a/Cargo.toml"),
         "--target-dir", str(work / f"target-{revision[:12]}")],
        capture_output=True, text=True, check=False,
    )


def reads_of_a(build: subprocess.CompletedProcess, base: Path) -> set[str]:
    """What rustc's dep-info names for `a`, absolute (a relative one is under
    `base`, the root of the workspace cargo ran in)."""
    reads = set()
    for line in build.stdout.splitlines():
        message = json.loads(line) if line.startswith("{") else {}
        if message.get("reason") == "compiler-artifact" and message["target"]["name"] == "a":
            for dep_info in ppp.dep_info_files(message):
                reads.update(
                    os.path.normpath(os.path.join(base, path)) for path in ppp.dep_info_paths(dep_info)
                )
    return reads


def consumer_output(
    repo: GitRepo, revision: str, work: Path, main_rs: str, build_rs: Optional[str] = None
) -> str:
    """What a binary depending on crates/a of a fresh checkout of `revision`
    prints: the consumer the gate stands for, built and linked."""
    tree = work / f"tree-{revision[:12]}"
    subprocess.run(["git", "clone", "-q", str(repo.root), str(tree)], check=True)
    subprocess.run(["git", "-C", str(tree), "checkout", "-q", revision], check=True)
    consumer = work / f"consumer-{revision[:12]}"
    (consumer / "src").mkdir(parents=True)
    (consumer / "src" / "main.rs").write_text(main_rs, encoding="utf-8")
    if build_rs is not None:
        (consumer / "build.rs").write_text(build_rs, encoding="utf-8")
    (consumer / "Cargo.toml").write_text(
        PACKAGE.format("consumer")
        + f'[dependencies]\na = {{ path = "{tree}/crates/a" }}\n[workspace]\n',
        encoding="utf-8",
    )
    run = subprocess.run(
        [TARGO, "--unverified", "run", "-q", "--offline", "--manifest-path",
         str(consumer / "Cargo.toml"), "--target-dir", str(work / f"target-{revision[:12]}")],
        capture_output=True, text=True, check=False,
    )
    if run.returncode != 0:
        raise AssertionError(run.stderr[-3000:])
    return run.stdout


class DepInfoTests(OneCrate):
    """rustc escapes only a space in dep-info. fae91a1cb read the first line of
    the first rule and took every backslash-space for an escaped space, so a
    tracked name holding a newline cut the list short, and one ending in a
    backslash merged the next name into a path that does not exist: every read
    after it was lost (r9 verifier: exit 0 with `shared` excluded while a
    consumer printed `one` at the pin and `two` at live main)."""

    def assert_read_after(self, odd: str, literal: str, message: str) -> None:
        pin = self.pin(
            {
                "crates/a/src/lib.rs": (
                    f'pub const ODD: &str = include_str!("../../../other/{literal}");\n'
                    'pub const X: &str = include_str!("../../../shared/x.txt");\n'
                ),
                f"other/{odd}": "odd\n",
                "shared/x.txt": "one\n",
            }
        )
        live_main = self.repo.commit({"shared/x.txt": "two\n"})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [
                consumer_output(self.repo, revision, Path(work), 'fn main() { print!("{}", a::X); }\n')
                for revision in (pin, live_main)
            ]
        self.assertEqual(printed, ["one\n", "two\n"])  # the consumer builds from shared/x.txt
        self.assert_read(pin, live_main, excluding("shared"), message)

    def test_a_name_ending_in_a_backslash_hides_no_read(self) -> None:
        self.assert_read_after("x\\", "x\\\\", "reads shared/x.txt")

    def test_a_name_holding_a_newline_is_refused(self) -> None:
        self.assert_read_after("a\nb.txt", "a\\nb.txt", "not dep-info as rustc writes it")


STATIC_LIBRARY_C = "int r10_value(void) {{ return {}; }}\n"


def static_library(work: Path, value: int) -> bytes:
    """libr10.a whose r10_value() returns `value`."""
    source = work / f"r10-{value}.c"
    source.write_text(STATIC_LIBRARY_C.format(value), encoding="utf-8")
    subprocess.run(["cc", "-c", "-o", str(work / f"r10-{value}.o"), str(source)], check=True)
    archive = work / f"libr10-{value}.a"
    subprocess.run(["ar", "rcs", str(archive), str(work / f"r10-{value}.o")], check=True)
    return archive.read_bytes()


def build_script(*lines: str) -> str:
    """A build script printing `lines`, each formatted with `shared`, the
    absolute directory ../../shared of its package."""
    printed = "".join(
        f"    println!({json.dumps(line)}{', shared = shared.display()' if '{shared}' in line else ''});\n"
        for line in lines
    )
    return (
        "fn main() {\n"
        '    let shared = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../shared");\n'
        + printed
        + '    println!("cargo:rerun-if-changed=build.rs");\n'
        "}\n"
    )


class BuildScriptOutputTests(OneCrate):
    """What a build script of the closure tells Cargo, rustc and the linker is
    read as Cargo reads it. fae91a1cb matched `cargo:rerun-if-changed=` only at
    the start of an untrimmed line and never looked at link directives: `check`
    never links, so a library the linker reads is in no dep-info."""

    def commit_bytes(self, files: dict[str, bytes]) -> str:
        for relative, content in files.items():
            (self.repo.root / relative).parent.mkdir(parents=True, exist_ok=True)
            (self.repo.root / relative).write_bytes(content)
        self.repo.git("add", "-A")
        self.repo.git("commit", "-q", "-m", "bytes")
        return self.repo.git("rev-parse", "HEAD")

    def test_a_static_library_the_linker_reads_is_read(self) -> None:
        # r9 verifier: a consumer printed 1 at the pin and 2 at live main, and
        # fae91a1cb exited 0 with `shared` excluded.
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as objects:
            one, two = static_library(Path(objects), 1), static_library(Path(objects), 2)
        self.pin(
            {
                "crates/a/build.rs": build_script(
                    "cargo:rustc-link-search=native={shared}", "cargo:rustc-link-lib=static=r10"
                ),
                "crates/a/src/lib.rs": (
                    'extern "C" { fn r10_value() -> i32; }\n'
                    "pub fn value() -> i32 { unsafe { r10_value() } }\n"
                ),
            }
        )
        pin = self.commit_bytes({"shared/libr10.a": one})
        live_main = self.commit_bytes({"shared/libr10.a": two})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [
                consumer_output(self.repo, revision, Path(work), 'fn main() { print!("{}", a::value()); }\n')
                for revision in (pin, live_main)
            ]
        self.assertEqual(printed, ["1", "2"])
        self.assert_read(pin, live_main, excluding("shared"), BUILD_SCRIPT_LITERAL)
        with without_build_inputs():
            self.assert_read(pin, live_main, excluding("shared"), "the linker, searching native=.* reads shared")

    def test_a_library_search_path_given_through_rustc_flags_is_read(self) -> None:
        pin = self.pin(
            {
                "crates/a/build.rs": build_script("cargo:rustc-flags=-L {shared}/lib"),
                "crates/a/src/lib.rs": "",
                "shared/lib/libx.a": "",
            }
        )
        live_main = self.repo.commit({"shared/lib/libx.a": "moved\n"})
        self.assert_read(pin, live_main, excluding("shared"), BUILD_SCRIPT_LITERAL)
        with without_build_inputs():
            self.assert_read(pin, live_main, excluding("shared"), "the linker, searching .* reads shared/lib")

    def test_a_linker_argument_or_a_relative_search_path_is_refused(self) -> None:
        for line, message in (
            ("cargo:rustc-link-arg=-Wl,-v", "passes the linker rustc-link-arg"),
            ("cargo::rustc-link-arg-cdylib=-Wl,-v", "passes the linker rustc-link-arg-cdylib"),
            ("cargo:rustc-link-search=native=../../shared", "relative library search path"),
            ("cargo:rustc-link-lib=static:+verbatim=../../shared/libx.a", "a path rather than a library"),
        ):
            with self.subTest(line=line):
                pin = self.pin(
                    {"crates/a/build.rs": build_script(line), "crates/a/src/lib.rs": "", "docs/x.md": ""}
                )
                live_main = self.repo.commit({"docs/x.md": "moved\n"})
                self.assert_read(pin, live_main, excluding("docs"), message)

    def test_a_watched_path_is_read_however_the_line_is_padded(self) -> None:
        # Cargo trims each line of the output: fae91a1cb missed an indented
        # directive and read `x.txt  ` for one with trailing blanks.
        for line in ("  cargo:rerun-if-changed={shared}/x.txt", "cargo:rerun-if-changed={shared}/x.txt  "):
            with self.subTest(line=line):
                pin = self.pin(
                    {"crates/a/build.rs": build_script(line), "crates/a/src/lib.rs": "", "shared/x.txt": ""}
                )
                live_main = self.repo.commit({"shared/x.txt": "moved\n"})
                with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
                    build = check_revision(self.repo, pin, Path(work))
                    self.assertEqual(build.returncode, 0, build.stderr)
                    (fingerprint,) = Path(work, f"target-{pin[:12]}", "debug", "build").glob(
                        "a/*/fingerprint/run-build-script-build-script-build.json"
                    )
                    watched = json.loads(fingerprint.read_text(encoding="utf-8"))["local"]
                    package = Path(os.path.realpath(work)) / pin[:12] / "crates/a"
                # Cargo watches shared/x.txt ...
                self.assertIn(
                    os.path.normpath(package / "../../shared/x.txt"),
                    [
                        os.path.normpath(package / path)
                        for entry in watched
                        for path in entry.get("RerunIfChanged", {}).get("paths", [])
                    ],
                )
                # ... so the gate reads it (its literal names it too).
                self.assert_read(pin, live_main, excluding("shared"), BUILD_SCRIPT_LITERAL)
                with without_build_inputs():
                    self.assert_read(
                        pin, live_main, excluding("shared"), "build script of a reads shared/x.txt"
                    )


def metadata_build_script(line: str) -> str:
    """A build script printing `line`, formatted with `own` (crates/a/include)
    and `shared` (../../shared/include), both absolute."""
    arguments = "".join(
        f", {name} = {name}.display()" for name in ("own", "shared") if "{" + name + "}" in line
    )
    return (
        "fn main() {\n"
        '    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));\n'
        '    let (own, shared) = (dir.join("include"), dir.join("../../shared/include"));\n'
        "    let _ = (&own, &shared);\n"
        f"    println!({json.dumps(line)}{arguments});\n"
        '    println!("cargo:rerun-if-changed=build.rs");\n'
        "}\n"
    )


def metadata_dependent(separator: str) -> str:
    """A dependent's build script that reads x.h from the first directory of
    DEP_R10_INCLUDE holding it, the list split on `separator` and each entry
    trimmed, as a -sys consumer hands each directory to `cc -I`."""
    return (
        "fn main() {\n"
        '    let dirs = std::env::var("DEP_R10_INCLUDE").unwrap();\n'
        f"    let text = dirs.split('{separator}')\n"
        "        .find_map(|dir| std::fs::read_to_string(\n"
        '            std::path::Path::new(dir.trim()).join("x.h")).ok())\n'
        '        .expect("x.h");\n'
        '    let out = std::env::var("OUT_DIR").unwrap();\n'
        '    std::fs::write(format!("{out}/x.h"), text).unwrap();\n'
        "}\n"
    )


class LinksTests(OneCrate):
    """Cargo hands what the build script of a package declaring `links` prints
    as metadata to its dependents' build scripts. 0bbf5f4fb counted a value as a
    read only when it was one absolute path of the tree, so a list or a padded
    value hid the read (r10 verifier: exit 0 with `shared` excluded while the
    consumer printed `one` at the pin and `two` at live main). A package of the
    closure that declares `links` is refused, whatever its metadata."""

    def test_a_package_that_hands_dependents_metadata_is_refused(self) -> None:
        for line, separator in (
            ("cargo:include={shared}", ","),
            ("cargo::metadata=include={shared}", ","),
            # libz-sys 1.1.29 build.rs:59 joins its include paths with ",".
            ("cargo:include={own},{shared}", ","),
            # env::join_paths joins them with ":" on Unix.
            ("cargo:include={own}:{shared}", ":"),
            # Cargo keeps the blanks after `=`; a dependent trims them.
            ("cargo:include=   {shared}", ","),
        ):
            with self.subTest(line=line):
                pin = self.pin(
                    {
                        "crates/a/Cargo.toml": PACKAGE.format("a") + 'links = "r10"\n',
                        "crates/a/build.rs": metadata_build_script(line),
                        "crates/a/src/lib.rs": "",
                        "crates/a/include/other.h": "",
                        "shared/include/x.h": "one\n",
                    }
                )
                live_main = self.repo.commit({"shared/include/x.h": "two\n"})
                with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
                    printed = [
                        consumer_output(
                            self.repo, revision, Path(work),
                            'fn main() { print!("{}", include_str!(concat!(env!("OUT_DIR"), "/x.h"))); }\n',
                            metadata_dependent(separator),
                        )
                        for revision in (pin, live_main)
                    ]
                # The consumer builds from shared/include/x.h ...
                self.assertEqual(printed, ["one\n", "two\n"])
                # ... so `shared` cannot be excluded.
                self.assert_read(pin, live_main, excluding("shared"), "a declares links = 'r10'")


def blob_lib(template: str) -> str:
    """crates/a/src/lib.rs: `a::blob()` returns the four bytes a global_asm!
    block assembles from `template`, a macro call that expands to its text."""
    return (
        '#[cfg(target_vendor = "apple")]\nmacro_rules! sym { () => { "_R10_BLOB" } }\n'
        '#[cfg(not(target_vendor = "apple"))]\nmacro_rules! sym { () => { "R10_BLOB" } }\n'
        f'core::arch::global_asm!(".data", concat!(".globl ", sym!()), concat!(sym!(), ":"), {template});\n'
        'extern "C" { static R10_BLOB: [u8; 4]; }\n'
        "pub fn blob() -> String {\n"
        "    unsafe { String::from_utf8_lossy(&*core::ptr::addr_of!(R10_BLOB)).into_owned() }\n"
        "}\n"
    )


SHARED_BLOB = 'concat!(env!("CARGO_MANIFEST_DIR"), "/../../shared/blob.bin")'


class AssemblerTests(OneCrate):
    """The assembler reads what a `.incbin` or `.include` directive names at
    codegen: `check` never assembles, and rustc's dep-info does not name the
    file (r10 verifier: 0bbf5f4fb exited 0 with `shared` excluded while the
    consumer printed `one` at the pin and `two` at live main)."""

    def assert_blob_read(self, pin: str, message: str) -> None:
        live_main = self.repo.commit({"shared/blob.bin": "two\n"})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [
                consumer_output(self.repo, revision, Path(work), 'fn main() { print!("{}", a::blob()); }\n')
                for revision in (pin, live_main)
            ]
        # The consumer links what the assembler read from shared/blob.bin ...
        self.assertEqual(printed, ["one\n", "two\n"])
        # ... so `shared` cannot be excluded.
        self.assert_read(pin, live_main, excluding("shared"), message)

    def test_a_file_the_assembler_reads_is_refused(self) -> None:
        # Each is refused twice over: as a file of the package (whatever host
        # builds it), and, with that search off, as a file rustc compiles.
        for files, message, compiled in (
            (
                {"crates/a/src/lib.rs": blob_lib(f'concat!(".incbin \\"", {SHARED_BLOB}, "\\"")')},
                r"crates/a/src/lib\.rs \(a file of package a\) spells '\.incbin' on line 5 with a "
                r"file name that is no string literal",
                r"crates/a/src/lib\.rs, which a \(a\) compiles, spells the assembler directive "
                r"'\.incbin' on line 5:",
            ),
            (
                # A template include_str! reads: dep-info names it, not what it includes.
                {
                    "crates/a/src/lib.rs": blob_lib('include_str!("blob.s")'),
                    "crates/a/src/blob.s": '.INCBIN "../../shared/blob.bin"\n',
                },
                r"shared covers shared/blob\.bin, and crates/a/src/blob\.s \(a file of package a\), "
                r"whose '\.INCBIN' on line 1 names '\.\./\.\./shared/blob\.bin' in whatever search "
                r"directory a build script gives it, reads shared/blob\.bin",
                r"crates/a/src/blob\.s, which a \(a\) compiles, spells the assembler directive "
                r"'\.INCBIN' on line 1:",
            ),
        ):
            with self.subTest(files=sorted(files)):
                self.repo = GitRepo(Path(self.scratch.name).resolve() / f"shapes-{len(files)}")
                pin = self.pin({**files, "shared/blob.bin": "one\n"})
                self.assert_blob_read(pin, message)
                live_main = self.repo.git("rev-parse", "HEAD")
                with without_build_inputs():
                    self.assert_read(pin, live_main, excluding("shared"), compiled)

    def test_a_directive_a_git_dependency_expands_to_is_refused(self) -> None:
        # a's sources spell no directive; the macro of its Git dependency does.
        helper = GitRepo(Path(self.scratch.name).resolve() / "helper")
        helper.commit(
            {
                "Cargo.toml": PACKAGE.format("helper") + "[workspace]\n",
                "src/lib.rs": (
                    "#[macro_export]\nmacro_rules! incbin {\n"
                    '    ($path:expr) => { concat!(".incbin \\"", $path, "\\"") };\n}\n'
                ),
            }
        )
        cargo_home = Path(self.scratch.name).resolve() / "cargo-home"
        with unittest.mock.patch.dict(os.environ, {"CARGO_HOME": str(cargo_home)}):
            self.pin(
                {
                    "crates/a/Cargo.toml": PACKAGE.format("a")
                    + f'[dependencies]\nhelper = {{ git = "file://{helper.root}" }}\n',
                    "crates/a/src/lib.rs": blob_lib(f"helper::incbin!({SHARED_BLOB})"),
                    "shared/blob.bin": "one\n",
                }
            )
            # Cargo fetches it once, writing Cargo.lock; every build after is offline.
            subprocess.run(
                [TARGO, "fetch", "--manifest-path", str(self.repo.root / "crates/a/Cargo.toml")],
                check=True, capture_output=True,
            )
            pin = self.repo.commit({})
            self.assert_blob_read(
                pin,
                r"/git/checkouts/helper-.*/src/lib\.rs, which helper \(git\+file:.*\) compiles, "
                r"spells the assembler directive '\.incbin' on line 3:",
            )

    def test_a_method_or_field_named_include_is_no_directive(self) -> None:
        # trust-ir-build calls `self.include(..)` and reads `.include_lineage`.
        pin = self.pin(
            {
                "crates/a/src/lib.rs": (
                    "pub struct S { pub include_lineage: bool }\n"
                    "impl S { pub fn include(&self) -> bool { self.include_lineage } }\n"
                    "pub fn f(s: &S) -> bool { s.include() && s.include_lineage }\n"
                ),
                "docs/x.md": "",
            }
        )
        live_main = self.repo.commit({"docs/x.md": "moved\n"})
        self.assert_unread(pin, live_main, excluding("docs"))


class ModuleCandidateTests(OneCrate):
    """`mod m;` makes rustc look for `m.rs` and `m/mod.rs`; dep-info names only
    the one it found, so the other is read too (r9 verifier: 28777a32f exited 0
    with 'shared' excluded while live main's consumer failed with E0761)."""

    def assert_candidate_read(self, files: dict[str, str], added: str) -> None:
        pin = self.pin(files)
        live_main = self.repo.commit({added: "pub const S: u32 = 2;\n"})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            at_pin = check_revision(self.repo, pin, Path(work))
            at_main = check_revision(self.repo, live_main, Path(work))
        # What a consumer of `a` compiles changed: the pin builds, live main not.
        self.assertEqual(at_pin.returncode, 0, at_pin.stderr)
        self.assertIn("E0761", at_main.stdout + at_main.stderr)
        self.assert_read(pin, live_main, excluding("shared"), f"covers {added}, and .* reads shared")

    def test_a_module_file_beside_a_file_rustc_read_is_read(self) -> None:
        self.assert_candidate_read(
            {
                "crates/a/src/lib.rs": '#[path = "../../../shared/gen.rs"]\npub mod gen;\n',
                "shared/gen.rs": "pub mod sub;\n",
                "shared/sub.rs": "pub const S: u32 = 1;\n",
            },
            "shared/sub/mod.rs",
        )

    def test_the_other_candidate_of_a_mod_rs_is_read(self) -> None:
        # An inline module's #[path] sets where `x` is looked for; rustc found
        # shared/m/x/mod.rs, and shared/m/x.rs is the other candidate.
        self.assert_candidate_read(
            {
                "crates/a/src/lib.rs": '#[path = "../../../shared/m"]\npub mod m {\n    pub mod x;\n}\n',
                "shared/m/x/mod.rs": "pub const S: u32 = 1;\n",
            },
            "shared/m/x.rs",
        )


class ExtractionTests(OneCrate):
    """The pin is read as a checkout writes it. `git archive` applies
    `export-subst`, which neither a path checkout nor Cargo's Git checkout does
    (r9 verifier: 28777a32f checked shared/x.txt while a checkout of the pin
    compiles shared/$Format:x$.txt, and exited 0 on a change to the latter)."""

    def test_a_file_is_read_as_a_checkout_writes_it(self) -> None:
        pin = self.pin(
            {
                ".gitattributes": "/crates/a/src/lib.rs export-subst\n",
                "crates/a/src/lib.rs": 'pub const T: &str = include_str!("../../../shared/$Format:x$.txt");\n',
                "shared/x.txt": "archive\n",
                "shared/$Format:x$.txt": "checkout\n",
            }
        )
        live_main = self.repo.commit({"shared/$Format:x$.txt": "moved\n"})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            checkout = check_revision(self.repo, pin, Path(work))
            self.assertEqual(checkout.returncode, 0, checkout.stderr)
            tree = Path(work).resolve() / pin[:12]
            self.assertIn(str(tree / "shared/$Format:x$.txt"), reads_of_a(checkout, tree))
        self.assert_read(pin, live_main, excluding("shared"), r"reads shared/\$Format:x\$\.txt")

    def test_a_path_git_and_libgit2_check_out_differently_is_refused(self) -> None:
        self.pin({"crates/a/src/lib.rs": "", "docs/y.md": "y\n"})
        for attributes in ("/shared/x.txt filter=anything\n", "*.txt working-tree-encoding=UTF-16\n"):
            with self.subTest(attributes=attributes):
                # Staged as blobs, so no attribute converts them on the way in.
                pin = self.repo.stage(
                    {".gitattributes": ("100644", attributes), "shared/x.txt": ("100644", "x\n")}
                )
                live_main = self.repo.stage({"docs/y.md": ("100644", f"moved {attributes}")})
                self.assert_read(pin, live_main, excluding("docs"), "Git and libgit2 check it out")


class CargoAtRunTimeTests(OneCrate):
    """Where a pinned package runs Cargo on its own workspace at run time
    (trust-vc-merge-contract's api_surface), Cargo loads every member and
    resolves with the workspace's Cargo.lock (r9 verifier, trust-vc a9edcdd4:
    a lock-only commit moved trust-vc-core's itoa 1.0.18 -> 1.0.15, and a
    duplicate test name under crates/trust-vc/tests failed the load, while
    28777a32f exited 0 on both with the reviewed list)."""

    WHY = "a's api runs cargo rustdoc on crates/b"

    def setUp(self) -> None:
        super().setUp()
        self.pinned = self.pin(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/*"]\nresolver = "2"\n',
                "crates/a/src/lib.rs": "",
                "crates/b/Cargo.toml": PACKAGE.format("b"),
                "crates/b/src/lib.rs": "",
                "crates/b/tests/t.rs": "",
                "Cargo.lock": "# This file is automatically @generated by Cargo.\nversion = 4\n",
                "docs/x.md": "x\n",
            }
        )

    def gate_run(self, live_main: str, *patterns: str, why: Optional[str] = WHY):
        return ppp.drift(TARGO, self.repo.root, self.pinned, live_main, ["a"], None,
                         excluding(*patterns), why)

    def test_what_loading_the_workspace_reads_is_read(self) -> None:
        for path, pattern, read in (
            ("crates/b/tests/t.rs", "crates/b/tests", "crates/b"),
            ("Cargo.lock", "Cargo.lock", "Cargo.lock"),
            ("crates/new/tests/t.rs", "crates/*/tests", "crates"),  # a directory the glob lists
        ):
            with self.subTest(path=path):
                live_main = self.repo.after(self.pinned, {path: "// moved\n"})
                # Nothing the pinned package compiles reads it ...
                self.assertEqual(self.gate_run(live_main, pattern, why=None).drifted, [])
                # ... but the Cargo it runs does.
                with self.assertRaisesRegex(
                    ppp.Refusal,
                    f"(?m)Cargo, which a pinned package runs on its workspace at run time, reads {read}$",
                ):
                    self.gate_run(live_main, pattern)

    def test_what_loading_the_workspace_does_not_read_passes(self) -> None:
        live_main = self.repo.after(self.pinned, {"docs/x.md": "moved\n"})
        self.assertEqual(self.gate_run(live_main, "docs").drifted, [])

    def test_the_command_takes_it_from_the_reviewed_list(self) -> None:
        listed = Path(self.scratch.name) / "exclusions.toml"
        listed.write_text(
            f'[r]\n"crates/b/tests" = "tests"\n[cargo-at-run-time]\nr = "{self.WHY}"\n',
            encoding="utf-8",
        )
        live_main = self.repo.after(self.pinned, {"crates/b/tests/t.rs": "// moved\n"})
        refused = subprocess.run(
            [sys.executable, str(SCRIPTS / "pinned_package_paths.py"), "drift", "--exclusions",
             str(listed), "--repository", "r", TARGO, str(self.repo.root), self.pinned, live_main, "a"],
            capture_output=True, text=True, check=False,
        )
        self.assertEqual(refused.returncode, 2, refused.stdout + refused.stderr)
        self.assertIn("runs on its workspace at run time, reads crates/b", refused.stderr)


# --- the builds the repository's shell scripts spell ---------------------------


def _quoted_end(text: str, start: int) -> int:
    """The index of the `"` closing the double-quoted string opened at `start`;
    a `$( )`, `${ }` or backquoted command inside it is skipped whole."""
    index = start + 1
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
        elif char == '"':
            return index
        elif char == "$" and text[index + 1 : index + 2] in ("(", "{"):
            index = _group_end(text, index + 1) + 1
        elif char == "`":
            end = text.find("`", index + 1)
            index = len(text) if end < 0 else end + 1
        else:
            index += 1
    return len(text)


def _group_end(text: str, start: int) -> int:
    """The index of what closes the `(` or `{` at `start`, what nests or is
    quoted inside it skipped."""
    opener = text[start]
    closer = ")" if opener == "(" else "}"
    depth, index = 0, start
    while index < len(text):
        char = text[index]
        if char == "\\":
            index += 2
            continue
        if char == '"':
            index = _quoted_end(text, index) + 1
            continue
        if char == "'" and opener == "(":
            end = text.find("'", index + 1)
            index = len(text) if end < 0 else end + 1
            continue
        if char == opener:
            depth += 1
        elif char == closer:
            depth -= 1
            if depth == 0:
                return index
        index += 1
    return len(text)


HERE_DOCUMENT = re.compile(r"<<(-?)[ \t]*(?:'([^'\n]*)'|\"([^\"\n]*)\"|\\?([A-Za-z_][A-Za-z_0-9]*))")
ARRAY_ASSIGNMENT = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\+?=")
ASSIGNMENT = re.compile(r"([A-Za-z_][A-Za-z_0-9]*)(\+?)=(.*)", re.S)
DECLARATIONS = frozenset({"local", "export", "declare", "readonly", "typeset"})


def _substitutions(segment: str) -> list[str]:
    """The commands a word or a double-quoted string runs: each `$( )` (not
    `$(( ))`, arithmetic) and backquoted command in it."""
    found, index = [], 0
    while index < len(segment):
        if segment.startswith("$((", index):
            index = _group_end(segment, index + 1) + 1
        elif segment.startswith("$(", index):
            end = _group_end(segment, index + 1)
            found.append(segment[index + 2 : end])
            index = end + 1
        elif segment[index] == "`":
            end = segment.find("`", index + 1)
            end = len(segment) if end < 0 else end
            found.append(segment[index + 1 : end])
            index = end + 1
        elif segment[index] == "\\":
            index += 2
        else:
            index += 1
    return found


def shell_commands(text: str) -> tuple[list[list[str]], list[tuple[str, bool, list[str]]]]:
    """The simple commands of a bash script, each as its words with the quotes
    removed (a variable stays as spelled), and its assignments in order (name,
    whether it appends, the words assigned). Comments and here-document bodies
    are dropped, a line continuation joins two lines, and an array assignment
    `name=( ... )` spans lines; its words also count as a command, which
    `"${name[@]}"` runs. A command substitution's commands (`$( )`, backquotes,
    quoted or not) count too. Commands split at `;`, `&`, `|`, `(`, `)` and a
    newline; a redirection and its target are dropped."""
    commands: list[list[str]] = []
    assignments: list[tuple[str, bool, list[str]]] = []
    words: list[str] = []
    array: Optional[tuple[str, bool, list[str]]] = None
    word: Optional[str] = None
    redirected = False  # the next word is a redirection's target
    documents: list[tuple[str, bool]] = []
    index = 0

    def nested(segment: str) -> None:
        for inner in _substitutions(segment):
            inner_commands, inner_assignments = shell_commands(inner)
            commands.extend(inner_commands)
            assignments.extend(inner_assignments)

    def finish_word() -> None:
        nonlocal word, redirected
        if word is not None and not redirected:
            (array[2] if array is not None else words).append(word)
        elif word is not None:
            redirected = False
        word = None

    def finish_command() -> None:
        nonlocal words
        finish_word()
        if words:
            commands.append(words)
            position = 0
            if words[0] in DECLARATIONS:
                position = 1
                while position < len(words) and words[position].startswith("-"):
                    position += 1
            for each in words[position:]:
                found = ASSIGNMENT.fullmatch(each)
                if found is None:
                    break
                assignments.append((found.group(1), bool(found.group(2)), [found.group(3)]))
        words = []

    while index < len(text):
        char = text[index]
        following = text[index + 1 : index + 2]
        if char == "\\":
            if following != "\n":
                word = (word or "") + following
            index += 2
        elif char == "'":
            end = text.find("'", index + 1)
            end = len(text) if end < 0 else end
            word, index = (word or "") + text[index + 1 : end], end + 1
        elif char == '"':
            end = _quoted_end(text, index)
            nested(text[index + 1 : end])
            body = re.sub(r'\\([$`"\\\n])', lambda m: "" if m.group(1) == "\n" else m.group(1),
                          text[index + 1 : end])
            word, index = (word or "") + body, end + 1
        elif char == "$" and following in ("(", "{"):
            end = _group_end(text, index + 1)
            nested(text[index : end + 1])
            word, index = (word or "") + text[index : end + 1], end + 1
        elif char == "`":
            end = text.find("`", index + 1)
            end = len(text) if end < 0 else end
            nested(text[index : end + 1])
            word, index = (word or "") + text[index : end + 1], end + 1
        elif char == "#" and word is None:
            end = text.find("\n", index)
            index = len(text) if end < 0 else end
        elif char == "<" and HERE_DOCUMENT.match(text, index) and text[index + 2 : index + 3] != "<":
            found = HERE_DOCUMENT.match(text, index)
            assert found is not None
            if word is not None and word.isdigit():
                word = None
            finish_word()
            documents.append((found.group(2) or found.group(3) or found.group(4), bool(found.group(1))))
            index = found.end()
        elif char in "<>" or (char == "&" and following == ">"):
            if word is not None and word.isdigit():
                word = None
            finish_word()
            while index < len(text) and text[index] in "<>&|":
                index += 1
            redirected = True
        elif char in " \t":
            finish_word()
            index += 1
        elif char == "\n":
            finish_word()
            if array is None:
                finish_command()
            index += 1
            for delimiter, tabs in documents:
                while index < len(text):
                    end = text.find("\n", index)
                    end = len(text) if end < 0 else end
                    line, index = text[index:end], end + 1
                    if (line.lstrip("\t") if tabs else line) == delimiter:
                        break
            documents = []
        elif char == "(" and array is None and word is not None and ARRAY_ASSIGNMENT.fullmatch(word):
            array, word = (word.rstrip("=").rstrip("+"), word.endswith("+="), []), None
            index += 1
        elif char == ")" and array is not None:
            finish_word()
            assignments.append(array)
            commands.append(array[2])
            array = None
            index += 1
        elif char in ";&|()":
            finish_command()
            index += 1
        else:
            word = (word or "") + char
            index += 1
    finish_command()
    return commands, assignments


# The most values the lint reads a variable as; one with more is reported.
MAX_SHELL_VALUES = 64


def shell_values(assignments: Sequence[tuple[str, bool, list[str]]], name: str) -> list[list[str]]:
    """What the variable `name` may hold, as word lists: every literal
    assignment, and each earlier value with every literal append (`+=`, which a
    script may make or not). A value naming another variable is known only at
    run time and is not read (a caller's `-p`). More than MAX_SHELL_VALUES of
    them are one value that no build reads."""
    known: list[list[str]] = []
    for assigned, appends, value in assignments:
        if assigned != name or not value or any("$" in each or "`" in each for each in value):
            continue
        added = [before + value for before in known] if appends and known else [value]
        known.extend(each for each in added if each not in known)
        if len(known) > MAX_SHELL_VALUES:
            return [[f"<more than {MAX_SHELL_VALUES} values of ${name}>"]]
    return known


VARIABLE = re.compile(r"\$\{?([A-Za-z_][A-Za-z_0-9]*)(?:\[[@*]\])?\}?")
# What a Cargo program word looks like: `cargo` (a path to it), or a variable
# naming it (`$CARGO`, `${TRUST_MC_CARGO}`).
STOCK_CARGO = re.compile(r"(?:\S*/)?cargo|\$\{?[A-Za-z_0-9]*cargo\}?", re.IGNORECASE)


def spelled_builds(text: str) -> list[tuple[str, list[str]]]:
    """Every build a bash script spells, whatever spells the program: `targo`,
    a variable or an array element. A Targo build is the lane selector
    (`--unverified` or `trust`) and what follows it when the first word after
    it that is no option is a Cargo command of ppp.BUILD_COMMANDS or
    `build-dev`; each is ("targo", its words from the selector on). A word
    naming Cargo itself followed by such a command is ("cargo", its words).
    A variable a script assigns a literal is read as each such value."""
    commands, assignments = shell_commands(text)
    found: list[tuple[str, list[str]]] = []
    for command in commands:
        if not any(word in ("--unverified", "trust") or STOCK_CARGO.fullmatch(word) for word in command):
            continue
        alternatives: list[list[str]] = [[]]
        for word in command:
            variable = VARIABLE.fullmatch(word)
            choices = (shell_values(assignments, variable.group(1)) if variable else []) or [[word]]
            alternatives = [done + choice for done in alternatives for choice in choices]
        for words in alternatives:
            for position, word in enumerate(words):
                if word in ("--unverified", "trust"):
                    kind = "targo"
                elif STOCK_CARGO.fullmatch(word):
                    kind = "cargo"
                else:
                    continue
                verb = next(
                    (each for each in words[position + 1 :] if not each.startswith(("-", "+"))), None
                )
                if verb in ppp.BUILD_COMMANDS or (kind == "targo" and verb == "build-dev"):
                    build = (kind, words[position:] if kind == "targo" else words[position + 1 :])
                    if (kind, _before_arguments(build[1])) not in [
                        (other, _before_arguments(spelled)) for other, spelled in found
                    ]:
                        found.append(build)
                    break
    return found


def _before_arguments(words: list[str]) -> list[str]:
    """`words` up to `--`, after which they go to the test harness or the program."""
    return words[: words.index("--")] if "--" in words else words


# Builds a script spells of a workspace other than trust-mc's, by the script and
# the manifest it names, with why nothing of trust-mc's is built.
OTHER_WORKSPACES = {
    ("scripts/build-pinned-ay-cli.sh", "${src}/Cargo.toml"): (
        "the pinned ay worktree's own workspace, built from a lane directory of its own"
    ),
    ("scripts/ay-replacement-proof.sh", "$TRUST_MC_DIR/tools/replacement-audit/Cargo.toml"): (
        "tools/replacement-audit declares its own [workspace] and depends on no pinned package"
    ),
}


def lane_lint(scripts: dict[str, str], listed: Path) -> tuple[dict[str, Counter], list[str]]:
    """Per script (repository path -> text), what builds it spells, counted by
    kind (a declared build, `build-dev`, another workspace's build), and what
    it spells that is none of them: a build of trust-mc that [consumer-builds]
    does not declare, one it cannot read, or one through Cargo itself. A build
    that a Python or Rust program other than tools/build-trust-mc runs is not
    read here; `git grep` finds none."""
    declared = {build.arguments for build in ppp.load_consumer_builds(listed)}
    counts: dict[str, Counter] = {}
    problems: list[str] = []
    for where, text in sorted(scripts.items()):
        for kind, words in spelled_builds(text):
            spelled = " ".join(shlex.quote(each) for each in words)
            options = _before_arguments(words)
            manifest = None
            for index, each in enumerate(options):
                if each == "--manifest-path":
                    manifest = options[index + 1] if index + 1 < len(options) else ""
                elif each.startswith("--manifest-path="):
                    manifest = each.partition("=")[2]
            if kind == "cargo":
                problems.append(f"{where}: {spelled}: a build through Cargo, not targo (AGENTS.md)")
            elif words[1:2] == ["build-dev"]:
                counts.setdefault(where, Counter())["build-dev"] += 1
            elif manifest is not None and (where, manifest) in OTHER_WORKSPACES:
                counts.setdefault(where, Counter())["other workspace"] += 1
            elif manifest is not None:
                problems.append(
                    f"{where}: {spelled}: builds {manifest}, which OTHER_WORKSPACES does not list"
                )
            else:
                try:
                    arguments = ppp.parse_build(where, spelled).arguments
                except ppp.Refusal as error:
                    problems.append(f"{where}: {error}")
                    continue
                if arguments in declared:
                    counts.setdefault(where, Counter())["declared"] += 1
                else:
                    problems.append(f"{where}: {spelled}: [{ppp.CONSUMER_BUILDS}] does not declare it")
    return counts, problems


# trust-vc af9a3696, root [workspace] members (explicit, no glob).
TRUST_VC_MEMBERS = (
    "crates/cargo-trust-vc", "crates/trust-vc", "crates/trust-vc-core", "crates/trust-vc-driver",
    "crates/trust-vc-kernel", "crates/trust-vc-merge-contract", "crates/trust-vc-merge-runner",
    "crates/trust-vc-oracle", "crates/trust-vc-rustc", "crates/trust-vc-std",
    "crates/trust-vc-trust-engine", "crates/trust-vc-types", "crates/trust-vc-vcir",
)


class ReviewedListTests(unittest.TestCase):
    """The committed list, against what trust-vc-merge-contract's api_surface
    makes Cargo read at run time: `targo --unverified rustdoc --lib --manifest-path
    <member>/Cargo.toml` (no --locked; trust-vc af9a3696) loads every
    member and resolves with the root Cargo.lock. 28777a32f excluded the lock,
    five members' tests/ and two members' src/ (r9 verifier)."""

    LISTED = SCRIPTS / "pin-exclusions.toml"

    def test_trust_vc_declares_the_cargo_it_runs(self) -> None:
        self.assertIsNotNone(ppp.load_cargo_at_run_time(self.LISTED, "trust-vc"))

    def test_trust_vc_excludes_nothing_that_cargo_loads(self) -> None:
        listed = self.LISTED
        loaded = ["Cargo.lock"] + [
            f"{member}/{path}"
            for member in TRUST_VC_MEMBERS
            for path in ("src/bin/x.rs", "src/main.rs", "tests/x.rs", "tests/x/main.rs",
                         "examples/x.rs", "benches/x.rs", "fixtures/x.json", "README.md")
        ]
        covered = sorted(
            f"{each.pattern} covers {path}"
            for path in loaded
            for each in ppp.load_exclusions(listed, "trust-vc")
            if each.covers(path)
        )
        self.assertEqual(covered, [])

    # Who reads an excluded path at the pin (grep of TrustIR 355a9e9d, repeated
    # at a00a6128 with the same crates -- the new trust-ir-laws names scripts/
    # only in comments -- at 066e1765, whose crates/ diff names no excluded
    # path outside comments, at a50b394e, whose crates/ diff adds one
    # reader, trust-ir's formula_schema_census integration test, of the trees
    # wire_census already reads -- frontend/src and every crates/*/src -- at
    # bf7ee706, whose crates/ diff adds Cargo's `metadata --locked` of the
    # frontend workspace to trust-ir's dependency_pin_coherence test, a reader
    # of frontend/Cargo.lock that test already include_str!s, and a
    # lowering-target-subset.md read by trust-ir-conformance's new union_carrier
    # test, and trust-vc a9edcdd4 and af9a3696, comments aside): its reason names each. fae91a1cb's
    # reasons said nothing in crates/ names evals, scripts (r9 verifier), docs or
    # a root *.md of trust-vc, and that no crate reads TrustIR's scripts.
    READERS = {
        ("trust-vc", "evals"): ("crates/trust-vc/tests", "vc_extraction", "crates/cargo-trust-vc"),
        ("trust-vc", "scripts"): ("crates/cargo-trust-vc", "rust_frontend.sh"),
        ("trust-vc", "docs"): ("doc_api_syntax",),
        ("trust-vc", "*.md"): ("doc_api_syntax",),
        ("trust-ir", "docs"): ("trust-ir-conformance",),
        ("trust-ir", "lean"): ("trust-ir, trust-ir-build and trust-ir-conformance",),
        ("trust-ir", "scripts"): ("trust-ir-conformance",),
        ("trust-ir", "*.md"): ("trust-ir-conformance",),
        ("trust-ir", "frontend/src"): ("wire_census", "formula_schema_census"),
        ("trust-ir", "frontend/Cargo.lock"): ("dependency_pin_coherence",),
    }

    @staticmethod
    def repository_scripts() -> dict[str, str]:
        """Every shell script of the working tree git tracks or would (not
        ignored) outside tests/, whose scripts build their own fixtures, and the
        ship gate as publication reads it (`^KEY_DEFAULT="(.*)"$`), a command
        line."""
        repository = SCRIPTS.parent
        listed = subprocess.check_output(
            ["git", "-C", str(repository), "ls-files", "-z", "--cached", "--others",
             "--exclude-standard", "--", "*.sh", "*.bash"],
            text=True,
        )
        scripts = {
            name: (repository / name).read_text(encoding="utf-8")
            for name in listed.split("\0")
            if name and not name.startswith("tests/")
        }
        ship = re.search(r'^CHECK_CMD_DEFAULT="(.*)"$', scripts["publish/config.sh"], re.M)
        assert ship is not None
        scripts["publish/config.sh CHECK_CMD_DEFAULT"] = ship.group(1)
        return scripts

    def test_every_lane_that_builds_trust_mc_is_a_declared_build(self) -> None:
        # Every targo build, check, test or run a tracked script spells, however
        # it spells the program, and the ship gate.
        counts, problems = lane_lint(self.repository_scripts(), self.LISTED)
        self.assertEqual(problems, [])
        self.assertEqual(
            {where: dict(kinds) for where, kinds in counts.items()},
            {
                "publish/config.sh CHECK_CMD_DEFAULT": {"declared": 2},
                "scripts/ay-bump-canary.sh": {"declared": 2, "build-dev": 1},
                "scripts/ay-compiletest.sh": {"declared": 1, "build-dev": 1},
                "scripts/ay-replacement-proof.sh": {"other workspace": 2},
                "scripts/ay-soundness-gate.sh": {"build-dev": 1},
                "scripts/check-trust-advisory-lane.sh": {"declared": 3},
                "scripts/check-trust-lane-build.sh": {"declared": 3},
                "scripts/check-trust-verification.sh": {"declared": 2},
            },
        )
        manifest = toml_loads(
            (SCRIPTS.parent / "tools/replacement-audit/Cargo.toml").read_text(encoding="utf-8")
        )
        self.assertIn("workspace", manifest)
        self.assertEqual(
            [name for name, spec in manifest["dependencies"].items()
             if isinstance(spec, dict) and ("path" in spec or "git" in spec)],
            [],
        )

    def test_a_lane_is_found_however_the_script_spells_targo(self) -> None:
        # r11 verifier (lint_gap.sh): 003643bd6's lint found only "$TARGO" and
        # "$TRUST_MC_TARGO", so a bare `targo` (as AGENTS.md spells it) or
        # "${targo}" (as build-pinned-ay-cli.sh does) lane went untied.
        for text in (
            "#!/usr/bin/env bash\nset -euo pipefail\n"
            "targo --unverified test --locked -p trust-mc-trust-vc-ingest\n",
            '#!/usr/bin/env bash\ntargo="$(scripts/resolve-trust-tool.sh targo)"\n'
            '"${targo}" --unverified build --release -p trust-mc-trust-vc-ingest\n',
            '"$TRUST_MC_TARGO" --unverified test --locked -p trust-mc-trust-vc-ingest\n',
            'lane=test\nlocal -a run=( "$T" --unverified\n  "$lane" --locked # why\n'
            '  -p trust-mc-trust-vc-ingest )\n"${run[@]}" 2>&1 | tee log\n',
            "( cd x && TARGO=1 targo --unverified test --locked -p trust-mc-trust-vc-ingest ) >&2\n",
        ):
            with self.subTest(text=text):
                scripts = {**self.repository_scripts(), "scripts/r11v-lane.sh": text}
                _, problems = lane_lint(scripts, self.LISTED)
                self.assertEqual(len(problems), 1, problems)
                self.assertRegex(
                    problems[0],
                    r"^scripts/r11v-lane\.sh: --unverified (test|build --release) (--locked )?-p "
                    r"trust-mc-trust-vc-ingest: \[consumer-builds\] does not declare it$",
                )

    def test_a_script_is_read_as_bash_splits_it(self) -> None:
        text = (
            "cat <<'EOF'\n  targo --unverified test -p here-document\nEOF\n"
            'echo "targo --unverified test -p quoted" # targo --unverified test -p comment\n'
            'die "targo --unverified build --release -p ay failed"\n'
            "mode=check\ncase $1 in --build) mode=build ;; esac\n"
            'selection=(--workspace)\nselection=()\n'
            'command=("$TARGO" trust "$mode" --locked "${selection[@]}" \\\n  --report-dir "$d")\n'
            'cargo +nightly test -p stock\n"$CARGO" build\n'
            "x=${#packages[@]} # not a comment start above\n"
        )
        self.assertEqual(
            spelled_builds(text),
            [
                ("targo", ["trust", "check", "--locked", "--workspace", "--report-dir", "$d"]),
                ("targo", ["trust", "build", "--locked", "--workspace", "--report-dir", "$d"]),
                ("cargo", ["+nightly", "test", "-p", "stock"]),
                ("cargo", ["build"]),
            ],
        )
        script = 'cargo test -p a\n"$T" --unverified check --manifest-path m/Cargo.toml\n'
        _, problems = lane_lint({"scripts/x.sh": script}, self.LISTED)
        self.assertEqual(
            problems,
            [
                "scripts/x.sh: test -p a: a build through Cargo, not targo (AGENTS.md)",
                "scripts/x.sh: --unverified check --manifest-path m/Cargo.toml: builds m/Cargo.toml, "
                "which OTHER_WORKSPACES does not list",
            ],
        )

    def test_the_builds_build_dev_runs_are_declared(self) -> None:
        # tools/build-trust-mc spells its nested builds in Rust: build_bin's
        # `.args([...])` after `.args(extra_args)` (extra: none, or --release for
        # `build-dev --release` and the bundle), and build_tools' `args`.
        source = (SCRIPTS.parent / "tools/build-trust-mc/src/sysroot.rs").read_text(encoding="utf-8")
        constants = {
            name: value for name, value in re.findall(r'const (\w+): &str = "([^"]*)";', source)
        }
        for name, values in re.findall(r"const (\w+): \[&str; \d+\] = \[([^\]]*)\];", source):
            for index, value in enumerate(re.findall(r'"([^"]*)"', values)):
                constants[f"{name}[{index}]"] = value
        body = source[source.index("pub(crate) fn build_bin") :]
        spelled = re.search(r"\.args\(extra_args\)\.args\(\[(.*?)\]\);", body, re.S)
        assert spelled is not None
        words = [
            item.strip().strip('"') if item.strip().startswith('"') else constants[item.strip()]
            for item in spelled.group(1).split(",") if item.strip()
        ]
        tools = re.search(r'fn build_tools.*?let args = \[([^\]]*)\];', source, re.S)
        assert tools is not None
        tool_words = re.findall(r'"([^"]*)"', tools.group(1))
        declared = {build.lane: build.arguments for build in ppp.load_consumer_builds(self.LISTED)}
        for lane, words_of_lane in (
            ("build-dev: tools/build-trust-mc build_bin", words),
            ("build-dev --release and bundle: tools/build-trust-mc build_bin", ["--release", *words]),
            ("bundle: tools/build-trust-mc build_tools", ["--release", *tool_words]),
        ):
            with self.subTest(lane=lane):
                command = " ".join(["--unverified", "build", *words_of_lane])
                self.assertEqual(declared.get(lane), ppp.parse_build(lane, command).arguments)

    def test_every_measured_reader_is_named_in_its_reason(self) -> None:
        missing = []
        for (repository, pattern), readers in self.READERS.items():
            reasons = {each.pattern: each.why for each in ppp.load_exclusions(self.LISTED, repository)}
            missing += [f"[{repository}] {pattern}: {reader}" for reader in readers
                        if reader not in reasons[pattern]]
        self.assertEqual(missing, [])


class ConsumerFeatureTests(unittest.TestCase):
    """Each package of the closure is checked with every feature set a build of
    the consumer can give it: between what every edge into it asks for and what
    the consumer's --all-features graph gives it."""

    def setUp(self) -> None:
        self.scratch = tempfile.TemporaryDirectory()
        self.base = Path(self.scratch.name).resolve()
        self.repo = GitRepo(self.base / "pinned")

    def tearDown(self) -> None:
        self.scratch.cleanup()

    def pin(self, lib: str, features: str, **files: str) -> str:
        return self.repo.commit(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a") + f"[features]\n{features}",
                "crates/a/src/lib.rs": lib,
                **files,
            }
        )

    def consumer(self, dependency: str) -> Path:
        consumer = self.base / "consumer"
        (consumer / "src").mkdir(parents=True)
        (consumer / "src" / "lib.rs").write_text("", encoding="utf-8")
        (consumer / "Cargo.toml").write_text(
            '[package]\nname = "consumer"\nversion = "0.1.0"\nedition = "2021"\n'
            f'[dependencies]\na = {{ path = "{self.repo.root}/crates/a"{dependency} }}\n'
            '[features]\nturbo = ["a/fast"]\n[workspace]\n',
            encoding="utf-8",
        )
        subprocess.run(
            [TARGO, "metadata", "--format-version", "1", "--offline", "--manifest-path",
             str(consumer / "Cargo.toml")],
            check=True, capture_output=True, cwd=consumer,
        )
        return consumer / "Cargo.toml"

    def drift(self, pin: str, live_main: str, consumer: Optional[Path], *builds: str):
        """The gate for `consumer`, whose one declared build is `targo
        --unverified check` unless `builds` names others."""
        return ppp.drift(
            TARGO, self.repo.root, pin, live_main, ["a"], consumer, excluding("shared"),
            builds=[ppp.parse_build(command, command) for command in builds or ["--unverified check"]],
        )

    def test_a_read_behind_a_feature_the_consumer_enables_is_seen(self) -> None:
        pin = self.pin(
            '#[cfg(feature = "extra")]\npub const E: &str = include_str!("../../../shared/e.txt");\n',
            "extra = []\nfast = []\n",
            **{"shared/e.txt": ""},
        )
        live_main = self.repo.commit({"shared/e.txt": "moved\n"})
        # Without the consumer the feature is off and no check makes the read;
        # the include is read from the source, under whatever cfg.
        with self.assertRaisesRegex(
            ppp.Refusal, r"crates/a/src/lib\.rs \(a Rust file of package a\), whose include_str! on "
            r"line 2 names '\.\./\.\./\.\./shared/e\.txt' under whatever cfg, reads shared/e\.txt",
        ):
            self.drift(pin, live_main, None)
        # With it, the check compiles the read and rustc names it.
        with self.assertRaisesRegex(ppp.Refusal, r"and a \(a\) reads shared/e\.txt"):
            self.drift(pin, live_main, self.consumer(', features = ["extra"]'))
        # And with the reading of the sources off, without the consumer the
        # read is what the module docstring leaves outside.
        with without_build_inputs():
            self.assertEqual(self.drift(pin, live_main, None).drifted, [])

    def write_consumer(self, name: str, manifest: str, lib: str = "") -> Path:
        directory = self.base / name
        (directory / "src").mkdir(parents=True)
        (directory / "src" / "lib.rs").write_text(lib, encoding="utf-8")
        (directory / "Cargo.toml").write_text(manifest, encoding="utf-8")
        return directory / "Cargo.toml"

    def slow_pin(self) -> tuple[str, str]:
        pin = self.pin(
            '#[cfg(not(feature = "fast"))]\npub const S: &str = '
            'include_str!("../../../shared/slow.txt");\n',
            "fast = []\n",
            **{"shared/slow.txt": "one\n"},
        )
        return pin, self.repo.commit({"shared/slow.txt": "two\n"})

    def assert_builds_reading_slow(self, consumer: Path, *selection: str) -> None:
        """The consumer's own non-dev check of `selection` compiles `a` reading
        shared/slow.txt: what the gate must see."""
        build = subprocess.run(
            [TARGO, "--unverified", "check", "--offline", "--message-format=json", *selection,
             "--manifest-path", str(consumer), "--target-dir", str(self.base / "consumer-target")],
            capture_output=True, text=True, check=False, cwd=consumer.parent,
        )
        self.assertEqual(build.returncode, 0, build.stderr)
        self.assertIn(str(self.repo.root / "shared/slow.txt"), reads_of_a(build, consumer.parent))

    def test_a_read_only_the_consumers_non_dev_build_makes_is_seen(self) -> None:
        # trust-mc's shape (r9 verifier): trust-mc-trust-bmc depends on
        # trust-ir with default features and adds serde and binary as a
        # dev-dependency; metadata's resolve unifies them and 28777a32f checked
        # only that set, never what `cargo build` compiles.
        pin, live_main = self.slow_pin()
        consumer = self.write_consumer(
            "consumer",
            PACKAGE.format("consumer")
            + f'[dependencies]\na = {{ path = "{self.repo.root}/crates/a" }}\n'
            + f'[dev-dependencies]\na = {{ path = "{self.repo.root}/crates/a", features = ["fast"] }}\n'
            + '[workspace]\nresolver = "2"\n',
            "pub use a::S;\n",
        )
        self.assert_builds_reading_slow(consumer)
        with self.assertRaisesRegex(ppp.Refusal, "reads shared/slow.txt"):
            self.drift(pin, live_main, consumer)

    def test_a_read_only_a_build_of_one_member_makes_is_seen(self) -> None:
        # trust-mc's shape: `-p trust-mc-trust-bmc` compiles trust-ir with its
        # default features only; a --workspace build adds serde, fmt and
        # clean-expr through trust-mc-driver and trust-ir-build.
        pin, live_main = self.slow_pin()
        root = self.base / "consumer"
        dependency = f'a = {{ path = "{self.repo.root}/crates/a"'
        self.write_consumer("consumer/plain", PACKAGE.format("plain") + f"[dependencies]\n{dependency} }}\n",
                            "pub use a::S;\n")
        self.write_consumer("consumer/quick", PACKAGE.format("quick")
                            + f'[dependencies]\n{dependency}, features = ["fast"] }}\n')
        (root / "Cargo.toml").write_text(
            '[workspace]\nmembers = ["plain", "quick"]\nresolver = "2"\n', encoding="utf-8"
        )
        self.assert_builds_reading_slow(root / "Cargo.toml", "-p", "plain")
        subprocess.run(
            [TARGO, "generate-lockfile", "--offline", "--manifest-path", str(root / "Cargo.toml")],
            check=True, capture_output=True, cwd=root,
        )
        with self.assertRaisesRegex(ppp.Refusal, "reads shared/slow.txt"):
            self.drift(pin, live_main, root / "Cargo.toml")

    def test_the_feature_sets_lie_between_what_every_edge_asks_and_all_features(self) -> None:
        self.repo.commit(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a")
                + '[features]\ndefault = ["z"]\nx = []\ny = ["x"]\nz = []\nunasked = []\n',
                "crates/a/src/lib.rs": "",
            }
        )
        consumer = self.write_consumer(
            "consumer",
            PACKAGE.format("consumer")
            + f'[dependencies]\na = {{ path = "{self.repo.root}/crates/a" }}\n'
            + f'[dev-dependencies]\na = {{ path = "{self.repo.root}/crates/a", features = ["y"] }}\n'
            + '[workspace]\n',
        )
        subprocess.run(
            [TARGO, "generate-lockfile", "--offline", "--manifest-path", str(consumer)],
            check=True, capture_output=True, cwd=consumer.parent,
        )
        workspace = ppp.tree_workspace(TARGO, self.repo.root, ["a"])
        closure = ppp.package_closure(workspace.members, ["a"])
        # Floor: default (both edges) enables z. Ceiling: + y, which enables x.
        self.assertEqual(
            ppp.consumer_feature_sets(TARGO, consumer, workspace.members, closure, ["a"]),
            [("a", ["default", "z"]), ("a", ["default", "x", "z"]), ("a", ["default", "x", "y", "z"])],
        )

    def test_a_consumer_with_more_feature_sets_than_the_gate_checks_is_refused(self) -> None:
        # fae91a1cb checked up to 2^8 sets per package, about 17 s each for
        # trust-ir (r9 verifier: ~2,200 s once three more trust-ir features are
        # requested); six free features are 64 sets, refused before any build.
        features = [f"f{index}" for index in range(6)]
        pin = self.pin("", "".join(f"{feature} = []\n" for feature in features), **{"shared/x.txt": ""})
        live_main = self.repo.commit({"shared/x.txt": "moved\n"})
        consumer = self.write_consumer(
            "consumer",
            PACKAGE.format("consumer")
            + f'[dependencies]\na = {{ path = "{self.repo.root}/crates/a" }}\n[features]\n'
            + "".join(f'{feature} = ["a/{feature}"]\n' for feature in features)
            + "[workspace]\n",
        )
        subprocess.run(
            [TARGO, "generate-lockfile", "--offline", "--manifest-path", str(consumer)],
            check=True, capture_output=True, cwd=consumer.parent,
        )
        with self.assertRaisesRegex(ppp.Refusal, "up to 64 feature sets .* at most 32"):
            self.drift(pin, live_main, consumer)

    def test_a_read_behind_a_feature_the_consumer_turns_off_by_default_is_seen(self) -> None:
        # The consumer's --all-features graph enables `fast` (through `turbo`);
        # its default build does not, and reads slow.txt.
        pin = self.pin(
            '#[cfg(not(feature = "fast"))]\npub const S: &str = '
            'include_str!("../../../shared/slow.txt");\n',
            "fast = []\n",
            **{"shared/slow.txt": ""},
        )
        live_main = self.repo.commit({"shared/slow.txt": "moved\n"})
        with self.assertRaisesRegex(ppp.Refusal, "reads shared/slow.txt"):
            self.drift(pin, live_main, self.consumer(""))



def gate_with_builds(
    repo: GitRepo, pin: str, live_main: str, consumer: Path, builds: dict[str, str],
    *patterns: str,
) -> subprocess.CompletedProcess:
    """The command check-shared-pins runs, with `consumer` and a reviewed list
    excluding `patterns` (default `shared`) of repository `shapes` and
    declaring `builds` (lane -> command) of the consumer."""
    listed = consumer.parent / "pin-exclusions.toml"
    listed.write_text(
        "[shapes]\n"
        + "".join(f'"{pattern}" = "test"\n' for pattern in patterns or ("shared",))
        + "[consumer-builds]\n"
        + "".join(f"{json.dumps(lane)} = {json.dumps(command)}\n" for lane, command in builds.items()),
        encoding="utf-8",
    )
    return subprocess.run(
        [
            sys.executable, str(SCRIPTS / "pinned_package_paths.py"), "drift", "--consumer",
            str(consumer), "--exclusions", str(listed), "--repository", "shapes", TARGO,
            str(repo.root), pin, live_main, "a",
        ],
        capture_output=True, text=True, check=False,
    )


def run_consumer(consumer: Path, target: Path, *command: str) -> str:
    """What `targo --unverified <command>` of `consumer` prints (`run` by default)."""
    run = subprocess.run(
        [TARGO, "--unverified", *(command or ("run",)), "-q", "--offline", "--manifest-path",
         str(consumer), "--target-dir", str(target)],
        capture_output=True, text=True, check=False, cwd=consumer.parent,
    )
    if run.returncode != 0:
        raise AssertionError(run.stderr[-3000:])
    return run.stdout


# A Git dependency whose macro reads a file of its caller's package only under
# its feature `embed`: `load!(p)` expands to include_str! of
# CARGO_MANIFEST_DIR/p, and to a constant without it.
EMBEDDING_HELPER = {
    "Cargo.toml": PACKAGE.format("helper") + "[features]\nembed = []\n[workspace]\n",
    "src/lib.rs": (
        '#[cfg(feature = "embed")]\n#[macro_export]\nmacro_rules! load {\n'
        '    ($p:expr) => { include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/", $p)) };\n}\n'
        '#[cfg(not(feature = "embed"))]\n#[macro_export]\nmacro_rules! load {\n'
        '    ($p:expr) => { "not embedded\\n" };\n}\n'
    ),
}
LOADING_A = 'pub fn x() -> &\'static str { helper::load!("../../shared/x.txt") }\n'


class ConsumerBuildTests(unittest.TestCase):
    """What a closure package compiles also depends on the features the
    consumer's build gives the packages it depends on: Cargo's resolver unifies
    them over the build (resolver 2: per build, dev-dependencies only when the
    build compiles tests, build scripts' and procedural macros' apart). r10
    verifier: 367cc97dc gave a dependency of the closure only what the closure
    asks of it, and exited 0 with `shared` excluded while the consumer printed
    `one` at the pin and `two` at live main."""

    def setUp(self) -> None:
        self.scratch = tempfile.TemporaryDirectory()
        self.base = Path(self.scratch.name).resolve()
        self.repo = GitRepo(self.base / "pinned")
        self.helper = GitRepo(self.base / "helper")
        patcher = unittest.mock.patch.dict(os.environ, {"CARGO_HOME": str(self.base / "cargo-home")})
        patcher.start()
        self.addCleanup(patcher.stop)

    def tearDown(self) -> None:
        self.scratch.cleanup()

    def pin(self, helper: dict[str, str], lib: str) -> tuple[str, str]:
        """crates/a, depending on the Git `helper`, at the pin; live main
        changes only shared/."""
        self.helper.commit(helper)
        self.repo.commit(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a")
                + f'[dependencies]\nhelper = {{ git = "file://{self.helper.root}" }}\n',
                "crates/a/src/lib.rs": lib,
                "shared/x.txt": "one\n",
                "shared/blob.bin": "one\n",
            }
        )
        subprocess.run(
            [TARGO, "fetch", "--manifest-path", str(self.repo.root / "crates/a/Cargo.toml")],
            check=True, capture_output=True,
        )
        pin = self.repo.commit({})  # with Cargo.lock
        return pin, self.repo.commit({"shared/x.txt": "two\n", "shared/blob.bin": "two\n"})

    def consumer(self, revision: str, manifest: str, main_rs: str, build_rs: str = "") -> Path:
        """A consumer of crates/a of a checkout of `revision`: `manifest`'s
        {a} and {helper} name them."""
        tree = self.base / f"tree-{revision[:12]}"
        if not tree.exists():
            subprocess.run(["git", "clone", "-q", str(self.repo.root), str(tree)], check=True)
            subprocess.run(["git", "-C", str(tree), "checkout", "-q", revision], check=True)
        consumer = self.base / f"consumer-{revision[:12]}"
        (consumer / "src").mkdir(parents=True)
        (consumer / "src" / "main.rs").write_text(main_rs, encoding="utf-8")
        if build_rs:
            (consumer / "build.rs").write_text(build_rs, encoding="utf-8")
        (consumer / "Cargo.toml").write_text(
            PACKAGE.format("consumer")
            + manifest.format(a=f'a = {{ path = "{tree}/crates/a" }}', helper=f'git = "file://{self.helper.root}"')
            + "[workspace]\n",
            encoding="utf-8",
        )
        subprocess.run(
            [TARGO, "fetch", "--manifest-path", str(consumer / "Cargo.toml")],
            check=True, capture_output=True,
        )
        return consumer / "Cargo.toml"

    def consumers(self, pin: str, live_main: str, manifest: str, main_rs: str, build_rs: str = "",
                  *command: str) -> Path:
        """The consumer at the pin, once shown to print `one` there and `two`
        at live main through `command`: it builds from shared/."""
        printed = [
            run_consumer(
                self.consumer(revision, manifest, main_rs, build_rs), self.base / f"target-{revision[:12]}",
                *command,
            )
            for revision in (pin, live_main)
        ]
        self.assertEqual(printed, ["one\n", "two\n"])
        return self.base / f"consumer-{pin[:12]}" / "Cargo.toml"

    def assert_refused(self, gate: subprocess.CompletedProcess, message: str) -> None:
        self.assertEqual(gate.returncode, 2, f"gate passed: {gate.stdout}{gate.stderr}")
        self.assertRegex(gate.stderr, message)

    def test_a_dependency_macro_that_reads_a_file_only_under_a_unified_feature_is_seen(self) -> None:
        pin, live_main = self.pin(EMBEDDING_HELPER, LOADING_A)
        consumer = self.consumers(
            pin, live_main, '[dependencies]\n{a}\nhelper = {{ {helper}, features = ["embed"] }}\n',
            'fn main() { print!("{}", a::x()); }\n',
        )
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {"ship": "--unverified build"}),
            r"a \(a\).* reads shared/x\.txt",
        )

    def test_a_dependency_macro_that_expands_to_incbin_only_under_a_unified_feature_is_seen(self) -> None:
        helper = {
            "Cargo.toml": PACKAGE.format("helper") + "[features]\nasm = []\n[workspace]\n",
            "src/lib.rs": (
                '#[cfg(feature = "asm")]\nmod asm;\n'
                '#[cfg(not(feature = "asm"))]\n#[macro_export]\nmacro_rules! blob {\n'
                '    ($p:expr) => { ".ascii \\"none\\"" };\n}\n'
            ),
            "src/asm.rs": (
                "#[macro_export]\nmacro_rules! blob {\n"
                '    ($p:expr) => { concat!(".incbin \\"", $p, "\\"") };\n}\n'
            ),
        }
        pin, live_main = self.pin(helper, blob_lib(f"helper::blob!({SHARED_BLOB})"))
        consumer = self.consumers(
            pin, live_main, '[dependencies]\n{a}\nhelper = {{ {helper}, features = ["asm"] }}\n',
            'fn main() { print!("{}", a::blob()); }\n',
        )
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {"ship": "--unverified build"}),
            r"spells the assembler directive '\.incbin'",
        )

    def test_a_dev_dependency_counts_only_in_a_build_that_compiles_tests(self) -> None:
        # Resolver 2: `build` leaves the dev-dependency's `embed` off, `test` turns it on.
        pin, live_main = self.pin(EMBEDDING_HELPER, LOADING_A)
        consumer = self.consumer(
            pin,
            '[dependencies]\n{a}\n[dev-dependencies]\nhelper = {{ {helper}, features = ["embed"] }}\n',
            'fn main() { print!("{}", a::x()); }\n#[test]\nfn embeds() { assert_eq!(a::x(), "one\\n"); }\n',
        )
        target = self.base / "target"
        self.assertEqual(run_consumer(consumer, target), "not embedded\n")
        run_consumer(consumer, target, "test")  # its test build embeds shared/x.txt
        built = gate_with_builds(self.repo, pin, live_main, consumer, {"build": "--unverified build"})
        self.assertEqual(built.returncode, 0, built.stderr)
        self.assertIn("all under reviewed exclusions shared", built.stdout)
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer,
                             {"build": "--unverified build", "tests": "--unverified test"}),
            r"reads shared/x\.txt",
        )

    def test_a_build_dependency_is_resolved_for_the_host_apart(self) -> None:
        # The consumer's build script calls `a` built for the host, where the
        # build-dependency turns `embed` on; the target's `a` has it off.
        pin, live_main = self.pin(EMBEDDING_HELPER, LOADING_A)
        consumer = self.consumers(
            pin, live_main,
            '[dependencies]\n{a}\n[build-dependencies]\n{a}\nhelper = {{ {helper}, features = ["embed"] }}\n',
            'fn main() { assert_eq!(a::x(), "not embedded\\n"); println!("{}", env!("FROM_BUILD")); }\n',
            'fn main() { println!("cargo:rustc-env=FROM_BUILD={}", a::x().trim()); }\n',
        )
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {"ship": "--unverified build"}),
            r"a \(a\).* reads shared/x\.txt",
        )

    def test_a_probe_that_compiles_otherwise_than_the_build_is_refused(self) -> None:
        # Negative control of the reproduction check: the probe's unit graph
        # must list exactly the build's units.
        pin, live_main = self.pin(EMBEDDING_HELPER, LOADING_A)
        consumer = self.consumer(
            pin, '[dependencies]\n{a}\nhelper = {{ {helper}, features = ["embed"] }}\n', "fn main() {}\n"
        )
        real = ppp.probe_units

        def without_one(*arguments: Any) -> dict[str, str]:
            found = real(*arguments)
            found.pop(sorted(found)[0])
            return found

        with unittest.mock.patch.object(ppp, "probe_units", without_one):
            with self.assertRaisesRegex(ppp.Refusal, r"does not compile what that build does \(1 of its"):
                ppp.drift(
                    TARGO, self.repo.root, pin, live_main, ["a"], consumer, excluding("shared"),
                    builds=[ppp.parse_build("ship", "--unverified build")],
                )

    def test_a_consumer_without_a_declared_build_is_refused(self) -> None:
        pin, live_main = self.pin(EMBEDDING_HELPER, LOADING_A)
        consumer = self.consumer(pin, "[dependencies]\n{a}\n", "fn main() {}\n")
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {}), r"no build of .* is declared"
        )
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {"odd": "--unverified build -Z x"}),
            r"the build `odd` .* passes '-Z'.* cannot be derived",
        )

    def test_declared_builds_that_compile_no_pinned_package_are_refused(self) -> None:
        pin, live_main = self.pin(EMBEDDING_HELPER, LOADING_A)
        consumer = self.consumer(
            pin, "[dependencies]\n[dev-dependencies]\n{a}\n", "fn main() {}\n#[test]\nfn t() { a::x(); }\n"
        )
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {"ship": "--unverified build"}),
            r"no declared build of .* compiles \['a'\]",
        )
        tested = gate_with_builds(self.repo, pin, live_main, consumer, {"tests": "--unverified test"})
        self.assertEqual(tested.returncode, 0, tested.stderr)

    def test_a_build_with_panic_abort_is_refused(self) -> None:
        # `cfg(panic = "abort")` code: the checks unwind. A profile of the
        # manifest applies to every build of it; one Cargo configuration sets,
        # to the declared builds of that profile.
        pin, live_main = self.pin(EMBEDDING_HELPER, LOADING_A)
        consumer = self.consumer(
            pin, '[dependencies]\n{a}\n[profile.release]\npanic = "abort"\n', "fn main() {}\n"
        )
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {"dev": "--unverified build"}),
            r"builds profile 'release' with panic = 'abort'",
        )
        manifest = consumer.read_text(encoding="utf-8").replace('[profile.release]\npanic = "abort"\n', "")
        consumer.write_text(manifest, encoding="utf-8")
        (consumer.parent / ".cargo").mkdir()
        (consumer.parent / ".cargo" / "config.toml").write_text(
            '[profile.release]\npanic = "abort"\n', encoding="utf-8"
        )
        passed = gate_with_builds(self.repo, pin, live_main, consumer, {"dev": "--unverified build"})
        self.assertEqual(passed.returncode, 0, passed.stderr)
        self.assert_refused(
            gate_with_builds(self.repo, pin, live_main, consumer, {"release": "--unverified build --release"}),
            r"the build `release` compiles .* with panic = 'abort'",
        )


class AssemblerExpansionTests(OneCrate):
    """The assembler reads what the template the compiler expanded names, however
    the sources spell it (r10 verifier: 367cc97dc exited 0 with `shared` excluded
    while the consumer printed `one` at the pin and `two` at live main)."""

    def assert_blob_read(self, pin: str, message: str) -> None:
        live_main = self.repo.commit({"shared/blob.bin": "two\n"})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [
                consumer_output(self.repo, revision, Path(work), 'fn main() { print!("{}", a::blob()); }\n')
                for revision in (pin, live_main)
            ]
        self.assertEqual(printed, ["one\n", "two\n"])
        self.assert_read(pin, live_main, excluding("shared"), message)

    def test_a_directive_a_procedural_macro_formats_is_seen_in_the_expansion(self) -> None:
        # The natural way to quote a path in Rust: format!(".incbin {:?}", path).
        pin = self.pin(
            {
                "Cargo.toml": '[workspace]\nmembers = ["crates/a", "crates/m"]\n',
                "crates/a/Cargo.toml": PACKAGE.format("a") + '[dependencies]\nm = { path = "../m" }\n',
                "crates/a/src/lib.rs": blob_lib('m::incbin!("../../shared/blob.bin")'),
                "crates/m/Cargo.toml": PACKAGE.format("m") + "[lib]\nproc-macro = true\n",
                "crates/m/src/lib.rs": (
                    "use proc_macro::TokenStream;\n\n"
                    "/// `incbin!(\"path\")`: the file at `path`, relative to the caller's manifest.\n"
                    "#[proc_macro]\npub fn incbin(input: TokenStream) -> TokenStream {\n"
                    "    let literal = input.to_string();\n"
                    "    let directory = std::env::var(\"CARGO_MANIFEST_DIR\").unwrap();\n"
                    "    let path = format!(\"{directory}/{}\", literal.trim_matches('\"'));\n"
                    "    let template = format!(\".incbin {:?}\", path);\n"
                    "    format!(\"{:?}\", template).parse().unwrap()\n}\n"
                ),
                "shared/blob.bin": "one\n",
            }
        )
        # m's own source formats the directive; its expansion in a quotes the name.
        self.assert_blob_read(
            pin, r"crates/m/src/lib\.rs \(a file of package m\) spells '\.incbin' on line 9 with a "
            r"file name that is no string literal \('\{:\?\}\", path\);'\)"
        )
        live_main = self.repo.git("rev-parse", "HEAD")
        with without_build_inputs():
            self.assert_read(
                pin, live_main, excluding("shared"),
                r"the compiler's expansion of (a|m) \(.*\) spells the assembler directive '\.incbin'",
            )

    def test_a_directive_a_build_script_assembles_is_seen(self) -> None:
        # The build script assembles a .S file with the system C compiler; the
        # assembler reads what its .incbin names. Declared (watched) or not, and
        # whether the file lies in the package or outside it, the gate reads the
        # name from the file (a file of the package, a watched path), and the
        # read witness sees the assembler read it; each alone refuses.
        build_rs = (
            "use std::process::Command;\n"
            "fn main() {\n"
            '    let out = std::env::var("OUT_DIR").unwrap();\n'
            '    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());\n'
            '    let status = Command::new(cc).args(["-c", "SOURCE", "-o"])\n'
            '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
            "    assert!(status.success());\n"
            '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
            '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
            "    assert!(status.success());\n"
            "    WATCH\n"
            '    println!("cargo:rustc-link-search=native={out}");\n'
            '    println!("cargo:rustc-link-lib=static=r10blob");\n'
            "}\n"
        )
        blob_s = (
            '#if defined(__APPLE__)\n#define SYM _R10_BLOB\n#else\n#define SYM R10_BLOB\n#endif\n'
            '.data\n.globl SYM\nSYM:\n.incbin "BLOB_PATH"\n'
        )
        lib = (
            'extern "C" { static R10_BLOB: [u8; 4]; }\n'
            "pub fn blob() -> String {\n"
            "    unsafe { String::from_utf8_lossy(&*core::ptr::addr_of!(R10_BLOB)).into_owned() }\n"
            "}\n"
        )
        for source, blob, watch, why in (
            ("src/blob.S", "../../shared/blob.bin", 'println!("cargo:rerun-if-changed=src/blob.S");',
             r"crates/a/src/blob\.S \(a file of package a\)"),
            ("src/blob.S", "../../shared/blob.bin", "", r"crates/a/src/blob\.S \(a file of package a\)"),
            ("../../asm/blob.S", "../../shared/blob.bin", 'println!("cargo:rerun-if-changed=../../asm/blob.S");',
             OUTSIDE_S),
        ):
            with self.subTest(source=source, watch=watch):
                files = {
                    "crates/a/build.rs": build_rs.replace("SOURCE", source).replace("WATCH", watch),
                    "crates/a/src/lib.rs": lib,
                    "shared/blob.bin": "one\n",
                }
                files["crates/a/src/blob.S" if source == "src/blob.S" else "asm/blob.S"] = (
                    blob_s.replace("BLOB_PATH", blob)
                )
                self.repo = GitRepo(Path(self.scratch.name).resolve() / f"shapes-{len(watch)}-{len(source)}")
                pin = self.pin(files)
                self.assert_blob_read(pin, named(why, 9, r"\.\./\.\./shared/blob\.bin"))
                live_main = self.repo.git("rev-parse", "HEAD")
                with without_build_inputs():
                    self.assert_read(pin, live_main, excluding("shared"), WITNESSED.format("bin"))


def named(
    why: str, line: int, name: str, directive: str = r"\.incbin", target: str = r"blob\.bin"
) -> str:
    """The refusal (a regular expression) when the gate read that a build input,
    a file `why` names, names shared/<target> with `directive` on `line`."""
    return (
        rf"shared covers shared/{target}, and {why}, whose '{directive}' on line {line} names "
        rf"'{name}' in whatever search directory a build script gives it, reads shared/{target}"
    )


# The refusal when the gate read a build input that names a file with no
# string literal (a regular expression, `why` the input is one).
UNNAMED = r"{why} spells '{directive}' on line {line} with a file name that is no string literal"
# The refusal when the read witness saw a check read shared/blob.<{}>.
WITNESSED = (
    r"shared covers shared/blob\.{}, and checking the pinned packages \(dev\) read it "
    r"\(its access time moved\)"
)
# The refusal when a string literal of crates/a/build.rs names a path under
# shared/ from the package's directory (BuildInputs.scan_build_scripts).
BUILD_SCRIPT_LITERAL = (
    r"shared covers \S+, and crates/a/build\.rs \(a file of the build script of a\), whose string "
    r"literal on line \d+ names '[^']*shared[^']*' from its package's directory, reads shared"
)
# The refusal when a check failed without the excluded files.
ABSENT = r"removed from the tree of the pin, checking the pinned packages \(dev\) fails where it passed"
ASSEMBLED_LIB = (
    'extern "C" { static R10_BLOB: [u8; 4]; }\n'
    "pub fn blob() -> String {\n"
    "    unsafe { String::from_utf8_lossy(&*core::ptr::addr_of!(R10_BLOB)).into_owned() }\n"
    "}\n"
)
BLOB_SYMBOL = '#if defined(__APPLE__)\n#define SYM _R10_BLOB\n#else\n#define SYM R10_BLOB\n#endif\n'
# Why the gate reads crates/a/src/blob.S, crates/a/build.rs and asm/blob.S, a
# tracked file outside the package (regular expressions).
PACKAGE_S = r"crates/a/src/blob\.S \(a file of package a\)"
PACKAGE_BUILD_RS = r"crates/a/build\.rs \(a file of package a\)"
TRACKED = r"\(a tracked file a build script can hand the tool\)"
OUTSIDE_S = r"asm/blob\.S " + TRACKED
# The data of R10_BLOB, which the C preprocessor includes from shared/.
INCLUDING_S = '.data\n.globl SYM\nSYM:\n#include "../../../shared/blob.inc"\n'


def assembling_build_rs(source: str, define: str = "", watch: str = "") -> str:
    """A build script that assembles `source` with the system C compiler (a .S
    goes through the C preprocessor first), archives it and links it."""
    return (
        "use std::process::Command;\n"
        "fn main() {\n"
        '    let out = std::env::var("OUT_DIR").unwrap();\n'
        '    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();\n'
        "    let _ = &dir;\n"
        '    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());\n'
        "    let mut command = Command::new(cc);\n"
        f"    {define}\n"
        f'    let status = command.args(["-c", "{source}", "-o"])\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        f"    {watch}\n"
        '    println!("cargo:rustc-link-search=native={out}");\n'
        '    println!("cargo:rustc-link-lib=static=r10blob");\n'
        "}\n"
    )


def generating_build_rs(copy: bool) -> str:
    """A build script that writes OUT_DIR/blob.s, `.incbin` of shared/blob.bin
    formatted as Rust quotes a path (`{:?}`), or of a copy of it it makes in
    OUT_DIR, then assembles, archives and links it."""
    blob = (
        '    let blob = format!("{out}/blob.bin");\n'
        '    std::fs::copy(format!("{dir}/../../shared/blob.bin"), &blob).unwrap();\n'
        if copy
        else '    let blob = format!("{dir}/../../shared/blob.bin");\n'
    )
    return (
        "use std::process::Command;\n"
        "fn main() {\n"
        '    let out = std::env::var("OUT_DIR").unwrap();\n'
        '    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();\n'
        '    let apple = std::env::var("CARGO_CFG_TARGET_VENDOR").unwrap() == "apple";\n'
        '    let sym = if apple { "_R10_BLOB" } else { "R10_BLOB" };\n'
        + blob
        + '    let template = format!(".data\\n.globl {sym}\\n{sym}:\\n.incbin {blob:?}\\n");\n'
        '    std::fs::write(format!("{out}/blob.s"), template).unwrap();\n'
        '    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());\n'
        '    let status = Command::new(cc).arg("-c").arg(format!("{out}/blob.s")).arg("-o")\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    println!("cargo:rerun-if-changed=build.rs");\n'
        '    println!("cargo:rustc-link-search=native={out}");\n'
        '    println!("cargo:rustc-link-lib=static=r10blob");\n'
        "}\n"
    )


class ObservedReadTests(OneCrate):
    """What the checks run reads, however it names or reaches the file: a
    build script assembling a .S whose read reaches the assembler through the C
    preprocessor (a -D define, a #define, a #include), through a tracked
    symbolic link it does not watch, or through a template it formats into
    OUT_DIR (trustc lowers format! to a byte template, `b"\\x08.incbin
    \\xc0\\x00"`, so the expansion search misses it). r11 verifier: 003643bd6 and
    c22e1022e exited 0 with `shared` excluded while the consumer printed `one`
    at the pin and `two` at live main. The gate sees each twice over: in the
    files a build script can hand the preprocessor or the assembler (a literal
    name is read wherever it is looked for, any other name refused), whatever
    host builds them; and, with that search off, in what the checks observe
    (the file's access time moves, or the check fails with the file removed)."""

    def assert_blob_read(
        self, pin: str, live_main_files: dict, message: str = WITNESSED.format("bin"),
        main_rs: str = 'fn main() { print!("{}", a::blob()); }\n', observed: Optional[str] = None,
    ) -> None:
        live_main = self.repo.commit(live_main_files)
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [
                consumer_output(self.repo, revision, Path(work), main_rs) for revision in (pin, live_main)
            ]
        # The consumer builds from what shared/ holds ...
        self.assertEqual(printed, ["one\n", "two\n"])
        # ... so `shared` cannot be excluded.
        self.assert_read(pin, live_main, excluding("shared"), message)
        if observed is not None:
            with without_build_inputs():
                self.assert_read(pin, live_main, excluding("shared"), observed)

    def test_an_incbin_name_a_define_the_build_script_passes_supplies_is_seen(self) -> None:
        define = 'command.arg(format!("-DBLOB_PATH=\\"{dir}/../../shared/blob.bin\\""));'
        pin = self.pin({
            "crates/a/build.rs": assembling_build_rs(
                "src/blob.S", define, 'println!("cargo:rerun-if-changed=src/blob.S");'
            ),
            "crates/a/src/lib.rs": ASSEMBLED_LIB,
            "crates/a/src/blob.S": BLOB_SYMBOL + ".data\n.globl SYM\nSYM:\n.incbin BLOB_PATH\n",
            "shared/blob.bin": "one\n",
        })
        self.assert_blob_read(
            pin, {"shared/blob.bin": "two\n"},
            UNNAMED.format(why=PACKAGE_S, directive=r"\.incbin", line=9), observed=WITNESSED.format("bin"),
        )

    def test_an_incbin_name_a_define_of_the_file_supplies_is_seen(self) -> None:
        pin = self.pin({
            "crates/a/build.rs": assembling_build_rs(
                "src/blob.S", "", 'println!("cargo:rerun-if-changed=src/blob.S");'
            ),
            "crates/a/src/lib.rs": ASSEMBLED_LIB,
            "crates/a/src/blob.S": (
                BLOB_SYMBOL + '#define BLOB "../../shared/blob.bin"\n.data\n.globl SYM\nSYM:\n.incbin BLOB\n'
            ),
            "shared/blob.bin": "one\n",
        })
        self.assert_blob_read(
            pin, {"shared/blob.bin": "two\n"},
            UNNAMED.format(why=PACKAGE_S, directive=r"\.incbin", line=10), observed=WITNESSED.format("bin"),
        )

    def test_a_file_the_preprocessor_includes_is_seen(self) -> None:
        pin = self.pin({
            "crates/a/build.rs": assembling_build_rs(
                "src/blob.S", "", 'println!("cargo:rerun-if-changed=src/blob.S");'
            ),
            "crates/a/src/lib.rs": ASSEMBLED_LIB,
            "crates/a/src/blob.S": BLOB_SYMBOL + INCLUDING_S,
            "shared/blob.inc": '.ascii "one\\n"\n',
        })
        self.assert_blob_read(
            pin, {"shared/blob.inc": '.ascii "two\\n"\n'},
            named(PACKAGE_S, 9, r"\.\./\.\./\.\./shared/blob\.inc", "#include", r"blob\.inc"),
            observed=WITNESSED.format("inc"),
        )

    def test_an_unwatched_source_that_is_a_tracked_symbolic_link_is_seen(self) -> None:
        pin = self.pin(
            {
                "crates/a/build.rs": assembling_build_rs("src/blob.S"),
                "crates/a/src/lib.rs": ASSEMBLED_LIB,
                "asm/blob.S": BLOB_SYMBOL + '.data\n.globl SYM\nSYM:\n.incbin "../../shared/blob.bin"\n',
                "shared/blob.bin": "one\n",
            },
            links={"crates/a/src/blob.S": "../../../asm/blob.S"},
        )
        # crates/a/src/blob.S is the link; asm/blob.S, the file it names, is read.
        self.assert_blob_read(
            pin, {"shared/blob.bin": "two\n"}, named(OUTSIDE_S, 9, r"\.\./\.\./shared/blob\.bin"),
            observed=WITNESSED.format("bin"),
        )

    def test_a_directive_a_build_script_formats_into_out_dir_is_seen(self) -> None:
        pin = self.pin({
            "crates/a/build.rs": generating_build_rs(copy=False),
            "crates/a/src/lib.rs": ASSEMBLED_LIB,
            "shared/blob.bin": "one\n",
        })
        self.assert_blob_read(
            pin, {"shared/blob.bin": "two\n"},
            UNNAMED.format(why=PACKAGE_BUILD_RS, directive=r"\.incbin", line=8),
            observed=WITNESSED.format("bin"),
        )

    def test_a_read_that_tolerates_the_files_absence_is_seen(self) -> None:
        # Removing the file cannot show this read; its access time does.
        pin = self.pin({
            "crates/a/build.rs": (
                "fn main() {\n"
                '    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();\n'
                '    let flag = std::fs::read_to_string(format!("{dir}/../../shared/blob.bin"))\n'
                "        .unwrap_or_default();\n"
                '    println!("cargo:rustc-env=A_FLAG={}", flag.trim());\n'
                "}\n"
            ),
            "crates/a/src/lib.rs": 'pub fn flag() -> &\'static str { env!("A_FLAG") }\n',
            "shared/blob.bin": "one\n",
        })
        self.assert_blob_read(
            pin, {"shared/blob.bin": "two\n"}, BUILD_SCRIPT_LITERAL,
            main_rs='fn main() { println!("{}", a::flag()); }\n', observed=WITNESSED.format("bin"),
        )

    def test_a_copy_is_seen(self) -> None:
        # std::fs::copy clones on APFS, which leaves the original's access
        # time as it was; the check then fails without the file.
        pin = self.pin({
            "crates/a/build.rs": generating_build_rs(copy=True),
            "crates/a/src/lib.rs": ASSEMBLED_LIB,
            "shared/blob.bin": "one\n",
        })
        self.assert_blob_read(
            pin, {"shared/blob.bin": "two\n"},
            UNNAMED.format(why=PACKAGE_BUILD_RS, directive=r"\.incbin", line=9),
            observed=f"({WITNESSED.format('bin')}|{ABSENT})",
        )

    def test_a_build_script_that_tests_whether_a_file_exists_is_seen(self) -> None:
        # A test of whether a path exists moves no access time, and the check
        # passes without the file; what the build script prints differs.
        pin = self.pin({
            "crates/a/build.rs": (
                "fn main() {\n"
                '    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();\n'
                '    println!("cargo::rustc-check-cfg=cfg(flag)");\n'
                '    if std::path::Path::new(&format!("{dir}/../../shared/flag")).exists() {\n'
                '        println!("cargo::rustc-cfg=flag");\n'
                "    }\n"
                "}\n"
            ),
            "crates/a/src/lib.rs": (
                '#[cfg(flag)]\npub fn blob() -> &\'static str { "one\\n" }\n'
                '#[cfg(not(flag))]\npub fn blob() -> &\'static str { "two\\n" }\n'
            ),
            "shared/flag": "",
        })
        self.assert_blob_read(
            pin, {"shared/flag": None}, BUILD_SCRIPT_LITERAL,
            observed=(
                r"with the excluded shared/flag removed from the tree of the pin, checking the pinned "
                r"packages \(dev\) passes, but the build script of \S+ leaves otherwise than with them "
                r"\(it printed otherwise\): it reads them"
            ),
        )

    def test_without_the_witness_the_absence_check_alone_sees_a_read_that_needs_the_file(self) -> None:
        with unittest.mock.patch.object(ppp.ReadWitness, "collect", lambda self, what: None):
            pin = self.pin({
                "crates/a/build.rs": assembling_build_rs(
                    "src/blob.S", "", 'println!("cargo:rerun-if-changed=src/blob.S");'
                ),
                "crates/a/src/lib.rs": ASSEMBLED_LIB,
                "crates/a/src/blob.S": BLOB_SYMBOL + INCLUDING_S,
                "shared/blob.inc": '.ascii "one\\n"\n',
            })
            with without_build_inputs():
                self.assert_blob_read(pin, {"shared/blob.inc": '.ascii "two\\n"\n'}, ABSENT)

    def test_a_file_system_that_does_not_record_reads_is_refused(self) -> None:
        pin = self.pin({"crates/a/src/lib.rs": "", "shared/x.txt": "one\n"})
        live_main = self.repo.commit({"shared/x.txt": "two\n"})
        unrecorded = staticmethod(lambda path: ppp.UNREAD_NS)
        with unittest.mock.patch.object(ppp.ReadWitness, "_accessed", unrecorded):
            self.assert_read(pin, live_main, excluding("shared"), "does not record that a file was read")
        # The same pin, on this host's file system, passes.
        self.assert_unread(pin, live_main, excluding("shared"))


def this_host() -> str:
    """This host's CARGO_CFG_TARGET_OS."""
    return "macos" if sys.platform == "darwin" else "linux"


def other_host() -> str:
    """A CARGO_CFG_TARGET_OS no check on this host compiles for (trust-mc also
    builds on Linux and macOS)."""
    return "linux" if sys.platform == "darwin" else "macos"


def gated_build_rs(source: str = "src/blob.S", arguments: str = "", watch: str = "src/blob.S") -> str:
    """A build script that watches `watch` and, only when compiling for OS_NAME,
    assembles `source` with the system C compiler (`arguments`: more of its
    Rust string literal arguments), archives and links it."""
    return (
        "use std::process::Command;\n"
        "fn main() {\n"
        f'    println!("cargo:rerun-if-changed={watch}");\n'
        '    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() != "OS_NAME" { return; }\n'
        '    let out = std::env::var("OUT_DIR").unwrap();\n'
        f'    let status = Command::new("cc").args([{arguments}"-c", "{source}", "-o"])\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    println!("cargo:rustc-link-search=native={out}");\n'
        '    println!("cargo:rustc-link-lib=static=r10blob");\n'
        "}\n"
    )


# crates/a/src/lib.rs for a gated build script: R10_BLOB's bytes on OS_NAME.
GATED_LIB = (
    '#[cfg(target_os = "OS_NAME")]\nextern "C" { static R10_BLOB: [u8; 4]; }\n'
    '#[cfg(target_os = "OS_NAME")]\npub fn blob() -> String {\n'
    "    unsafe { String::from_utf8_lossy(&*core::ptr::addr_of!(R10_BLOB)).into_owned() }\n}\n"
    '#[cfg(not(target_os = "OS_NAME"))]\npub fn blob() -> String { "none\\n".into() }\n'
)
DEFINING_S = BLOB_SYMBOL + ".data\n.globl SYM\nSYM:\n"


class BuildInputTests(OneCrate):
    """What a build script hands the C preprocessor or the assembler, read from
    the files whichever host builds them. r11c verifier: 68402bd9f deleted the
    search of a closure package's files and watched paths for what the
    assembler reads, so a build script that assembles only for another host
    (trust-mc also builds on Linux) passed with `shared` excluded where
    cd838d949 refused it. Each shape is gated on this host, where the consumer
    prints `one` at the pin and `two` at live main (it reads shared/), and on the
    other one, which no check here compiles for."""

    def assert_refused_whichever_host(
        self, files: dict[str, str], live_main_files: dict, message: Any, control: bool = True
    ) -> None:
        """`message`: the refusal, or the refusal by the host the shape is gated on."""
        for os_name in ([this_host()] if control else []) + [other_host()]:
            with self.subTest(gated_on=os_name):
                shapes = tempfile.mkdtemp(prefix=f"shapes-{os_name}-", dir=self.scratch.name)
                self.repo = GitRepo(Path(shapes).resolve())
                pin = self.pin({name: text.replace("OS_NAME", os_name) for name, text in files.items()})
                live_main = self.repo.commit(live_main_files)
                if os_name == this_host():
                    with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
                        printed = [
                            consumer_output(
                                self.repo, revision, Path(work), 'fn main() { print!("{}", a::blob()); }\n'
                            )
                            for revision in (pin, live_main)
                        ]
                    self.assertEqual(printed, ["one\n", "two\n"])
                expected = message[os_name] if isinstance(message, dict) else message
                self.assert_read(pin, live_main, excluding("shared"), expected)

    def test_an_incbin_of_a_file_only_another_host_assembles(self) -> None:
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": gated_build_rs(),
                "crates/a/src/lib.rs": GATED_LIB,
                "crates/a/src/blob.S": DEFINING_S + '.incbin "../../shared/blob.bin"\n',
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            named(PACKAGE_S, 9, r"\.\./\.\./shared/blob\.bin"),
        )

    def test_a_name_found_through_a_search_directory_the_build_script_gives(self) -> None:
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": gated_build_rs(arguments='"-I", "../../shared", '),
                "crates/a/src/lib.rs": GATED_LIB,
                "crates/a/src/blob.S": DEFINING_S + '#include "blob.inc"\n',
                "shared/blob.inc": '.ascii "one\\n"\n',
            },
            {"shared/blob.inc": '.ascii "two\\n"\n'},
            named(PACKAGE_S, 9, r"blob\.inc", "#include", r"blob\.inc"),
        )

    def test_a_name_a_file_the_build_input_names_names(self) -> None:
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": gated_build_rs(arguments='"-I", "../../common", '),
                "crates/a/src/lib.rs": GATED_LIB,
                "crates/a/src/blob.S": DEFINING_S + '#include "defs.inc"\n',
                "common/defs.inc": '#include "../shared/blob.inc"\n',
                "shared/blob.inc": '.ascii "one\\n"\n',
            },
            {"shared/blob.inc": '.ascii "two\\n"\n'},
            named(r"common/defs\.inc " + TRACKED, 1, r"\.\./shared/blob\.inc", "#include", r"blob\.inc"),
        )

    def test_a_watched_file_outside_the_package(self) -> None:
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": gated_build_rs("../../asm/blob.S", watch="../../asm/blob.S"),
                "crates/a/src/lib.rs": GATED_LIB,
                "asm/blob.S": DEFINING_S + '.incbin "../../shared/blob.bin"\n',
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            named(OUTSIDE_S, 9, r"\.\./\.\./shared/blob\.bin"),
        )

    def test_a_name_whose_file_only_live_main_holds(self) -> None:
        # No check can read a file the pin does not hold, and a build at the
        # pin fails without it: only the name shows the read.
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": gated_build_rs(),
                "crates/a/src/lib.rs": GATED_LIB,
                "crates/a/src/blob.S": DEFINING_S + '.incbin "../../shared/new.bin"\n',
                "shared/blob.bin": "one\n",
            },
            {"shared/new.bin": "two\n"},
            named(PACKAGE_S, 9, r"\.\./\.\./shared/new\.bin", target=r"new\.bin"),
            control=False,
        )

    def test_a_name_a_define_supplies_on_another_host(self) -> None:
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": gated_build_rs(
                    arguments='"-DBLOB_PATH=\\"../../shared/blob.bin\\"", '
                ),
                "crates/a/src/lib.rs": GATED_LIB,
                "crates/a/src/blob.S": DEFINING_S + ".incbin BLOB_PATH\n",
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            UNNAMED.format(why=PACKAGE_S, directive=r"\.incbin", line=9),
        )

    def test_what_a_build_input_names_elsewhere_passes(self) -> None:
        # A name that reaches no excluded path, whatever directory it is looked
        # for in, reads nothing excluded (the build runs on this host).
        pin = self.pin({
            "crates/a/build.rs": gated_build_rs(arguments='"-I", "src", ').replace("OS_NAME", this_host()),
            "crates/a/src/lib.rs": GATED_LIB.replace("OS_NAME", this_host()),
            "crates/a/src/blob.S": DEFINING_S + '#include "data.inc"\n',
            "crates/a/src/data.inc": '.ascii "one\\n"\n',
            "shared/blob.bin": "one\n",
        })
        live_main = self.repo.commit({"shared/blob.bin": "two\n"})
        self.assert_unread(pin, live_main, excluding("shared"))


    # r12 verifier: 302fc263e read a file outside the package only when this
    # host's build script watched it, so a build script that assembles one
    # only for another host, watching it there or nowhere, passed with `shared`
    # excluded; so did a CMake-style placeholder in a template the build script
    # fills, and a Rust include only another host compiles.

    def test_a_file_outside_the_package_only_another_host_assembles(self) -> None:
        for watch in (True, False):
            with self.subTest(watch=watch):
                self.assert_refused_whichever_host(
                    {
                        "crates/a/build.rs": outside_build_rs(watch),
                        "crates/a/src/lib.rs": GATED_LIB,
                        "asm/blob.S": DEFINING_S + '.incbin "../../shared/blob.bin"\n',
                        "shared/blob.bin": "one\n",
                    },
                    {"shared/blob.bin": "two\n"},
                    named(OUTSIDE_S, 9, r"\.\./\.\./shared/blob\.bin"),
                )

    def test_a_define_names_what_a_file_outside_the_package_reads_on_another_host(self) -> None:
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": outside_build_rs(
                    False, arguments='"-DBLOB_PATH=\\"../../shared/blob.bin\\"", '
                ),
                "crates/a/src/lib.rs": GATED_LIB,
                "asm/blob.S": DEFINING_S + ".incbin BLOB_PATH\n",
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            UNNAMED.format(why=OUTSIDE_S, directive=r"\.incbin", line=9),
        )

    def test_a_placeholder_a_build_script_fills_on_another_host(self) -> None:
        self.assert_refused_whichever_host(
            {
                "crates/a/build.rs": template_build_rs(),
                "crates/a/src/lib.rs": GATED_LIB,
                "crates/a/src/blob.S.in": DEFINING_S + '.incbin "@BLOB@"\n',
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            UNNAMED.format(
                why=r"crates/a/src/blob\.S\.in \(a file of package a\)", directive=r"\.incbin", line=9
            ),
        )

    def test_a_rust_include_only_another_host_compiles(self) -> None:
        # rustc names in dep-info what this host compiles; for another host the
        # gate reads the include from the source, under whatever cfg.
        included = (
            r"crates/a/src/{} \(a Rust file of package a\), whose {} on line {} names '{}' under "
            "whatever cfg"
        )
        for files, spelled in (
            (
                {"crates/a/src/lib.rs": (
                    '#[cfg(target_os = "OS_NAME")]\n'
                    "pub fn blob() -> &'static str { include_str!(\"../../../shared/blob.bin\") }\n"
                    '#[cfg(not(target_os = "OS_NAME"))]\npub fn blob() -> &\'static str { "none\\n" }\n'
                )},
                ("lib.rs", "include_str!", 2, r"\.\./\.\./\.\./shared/blob\.bin"),
            ),
            (
                {
                    "crates/a/src/lib.rs": (
                        '#[cfg(target_os = "OS_NAME")]\nmod imp;\n'
                        '#[cfg(target_os = "OS_NAME")]\npub use imp::blob;\n'
                        '#[cfg(not(target_os = "OS_NAME"))]\npub fn blob() -> &\'static str { "none\\n" }\n'
                    ),
                    "crates/a/src/imp.rs": (
                        "pub fn blob() -> &'static str {\n"
                        '    include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../shared/blob.bin"))\n}\n'
                    ),
                },
                ("imp.rs", "include_str!", 2, r"/\.\./\.\./shared/blob\.bin"),
            ),
        ):
            with self.subTest(files=sorted(files)):
                self.assert_refused_whichever_host(
                    {**files, "shared/blob.bin": "one\n"},
                    {"shared/blob.bin": "two\n"},
                    {
                        this_host(): r"shared covers shared/blob\.bin, and a \(a\) reads shared/blob\.bin",
                        other_host(): (
                            r"shared covers shared/blob\.bin, and " + included.format(*spelled)
                            + r", reads shared/blob\.bin"
                        ),
                    },
                )

    def test_a_rust_include_no_consumer_compiles_passes(self) -> None:
        # An integration test is compiled by the package's own `cargo test`,
        # never by a consumer (trust-ir's tests include_str! frontend/Cargo.lock).
        pin = self.pin({
            "crates/a/src/lib.rs": "pub fn x() {}\n",
            "crates/a/tests/t.rs": (
                '#[test]\nfn t() { assert!(!include_str!("../../../shared/blob.bin").is_empty()); }\n'
            ),
            "crates/a/benches/b.rs": 'fn main() { let _ = include_bytes!("../../../shared/blob.bin"); }\n',
            "shared/blob.bin": "one\n",
        })
        live_main = self.repo.commit({"shared/blob.bin": "two\n"})
        self.assert_unread(pin, live_main, excluding("shared"))


def outside_build_rs(watch: bool, arguments: str = "") -> str:
    """A build script that, only when compiling for OS_NAME, watches (or not)
    and assembles asm/blob.S, outside its package, with the system C compiler
    (`arguments`: more of its Rust string literal arguments), archives and
    links it: the watch is printed where it assembles, as cc-rs users do."""
    return (
        "use std::process::Command;\n"
        "fn main() {\n"
        '    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() != "OS_NAME" { return; }\n'
        + ('    println!("cargo:rerun-if-changed=../../asm/blob.S");\n' if watch else "")
        + '    let out = std::env::var("OUT_DIR").unwrap();\n'
        f'    let status = Command::new("cc").args([{arguments}"-c", "../../asm/blob.S", "-o"])\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    println!("cargo:rustc-link-search=native={out}");\n'
        '    println!("cargo:rustc-link-lib=static=r10blob");\n'
        "}\n"
    )


def template_build_rs() -> str:
    """A build script that, only when compiling for OS_NAME, fills the
    CMake-style template src/blob.S.in (`@BLOB@`) of its package with the path
    of shared/blob.bin, writes it to OUT_DIR, assembles, archives and links it."""
    return (
        "use std::process::Command;\n"
        "fn main() {\n"
        '    println!("cargo:rerun-if-changed=src/blob.S.in");\n'
        '    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() != "OS_NAME" { return; }\n'
        '    let out = std::env::var("OUT_DIR").unwrap();\n'
        '    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();\n'
        '    let template = std::fs::read_to_string("src/blob.S.in").unwrap();\n'
        '    let source = template.replace("@BLOB@", &format!("{dir}/../../shared/blob.bin"));\n'
        '    std::fs::write(format!("{out}/blob.S"), source).unwrap();\n'
        '    let status = Command::new("cc").arg("-c").arg(format!("{out}/blob.S")).arg("-o")\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    println!("cargo:rustc-link-search=native={out}");\n'
        '    println!("cargo:rustc-link-lib=static=r10blob");\n'
        "}\n"
    )


def archive(scratch: Path, text: str) -> bytes:
    """A static library defining R10_BLOB = `text` and a newline (4 bytes)."""
    with tempfile.TemporaryDirectory(dir=scratch) as work:
        directory = Path(work)
        (directory / "blob.S").write_text(DEFINING_S + f'.ascii "{text}\\n"\n', encoding="utf-8")
        subprocess.run(["cc", "-c", "blob.S", "-o", "blob.o"], cwd=directory, check=True)
        subprocess.run(["ar", "crs", "libr10blob.a", "blob.o"], cwd=directory, check=True)
        return (directory / "libr10blob.a").read_bytes()


class LinkTimeReadTests(OneCrate):
    """The linker (and rustc, bundling a static library into an rlib) reads at
    codegen what a build script put in its OUT_DIR, which the gate treats as
    generated. A symbolic link there to a tracked file is made without reading
    it, even when the file is absent, so neither the read witness nor the
    absence check sees it (r11c verifier: 68402bd9f and cd838d949 exited 0 with
    `shared` excluded while the consumer printed `one` at the pin and `two` at
    live main)."""

    def assert_linked_read(
        self, make: str, message: str, build_rs: Optional[str] = None,
        library: str = "shared/libr10blob.a",
    ) -> None:
        """The build script makes OUT_DIR/libr10blob.a with `make` (or is
        `build_rs`), the linker links `library` of the tree through it. Its
        string literal names the library, which refuses first; `message` is
        the refusal with the files at the pin unread."""
        build_rs = build_rs or (
            "fn main() {\n"
            '    let out = std::env::var("OUT_DIR").unwrap();\n'
            '    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();\n'
            '    let link = format!("{out}/libr10blob.a");\n'
            "    let _ = std::fs::remove_file(&link);\n"
            f"    {make}\n"
            '    println!("cargo:rerun-if-changed=build.rs");\n'
            '    println!("cargo:rustc-link-search=native={out}");\n'
            '    println!("cargo:rustc-link-lib=static=r10blob");\n'
            "}\n"
        )
        scratch = Path(self.scratch.name)
        (self.repo.root / library).parent.mkdir(parents=True, exist_ok=True)
        (self.repo.root / library).write_bytes(archive(scratch, "one"))
        pin = self.pin({"crates/a/build.rs": build_rs, "crates/a/src/lib.rs": ASSEMBLED_LIB})
        (self.repo.root / library).write_bytes(archive(scratch, "two"))
        live_main = self.repo.commit({})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [
                consumer_output(self.repo, revision, Path(work), 'fn main() { print!("{}", a::blob()); }\n')
                for revision in (pin, live_main)
            ]
        self.assertEqual(printed, ["one\n", "two\n"])
        self.assert_read(pin, live_main, excluding("shared"), BUILD_SCRIPT_LITERAL)
        with without_build_inputs():
            self.assert_read(pin, live_main, excluding("shared"), message)

    def test_a_library_the_linker_reads_through_a_symbolic_link_in_out_dir(self) -> None:
        self.assert_linked_read(
            'std::os::unix::fs::symlink(format!("{dir}/../../shared/libr10blob.a"), &link).unwrap();',
            r"shared covers shared/libr10blob\.a, and the linker, searching native=\S+ for the build "
            r"script of a through \S+/libr10blob\.a, reads shared/libr10blob\.a",
        )

    def test_a_library_the_linker_reads_through_a_hard_link_in_out_dir(self) -> None:
        # Tolerant of the file's absence, so the absence check passes too.
        self.assert_linked_read(
            'let _ = std::fs::hard_link(format!("{dir}/../../shared/libr10blob.a"), &link);',
            r"the linker, searching native=\S+ for the build script of a finds \S+/libr10blob\.a, a "
            r"hard link",
        )

    def test_a_library_copied_into_out_dir_tolerating_its_absence(self) -> None:
        # r12 verifier: std::fs::copy clones on APFS, so the original's access
        # time stays, and `let _` passes the check without it. What the build
        # script leaves then differs: its OUT_DIR lacks the copy.
        self.assert_linked_read(
            'let _ = std::fs::copy(format!("{dir}/../../shared/libr10blob.a"), &link);',
            r"with the excluded shared/libr10blob\.a removed from the tree of the pin, checking the "
            r"pinned packages \(dev\) passes, but the build script of \S+ leaves otherwise than with "
            r"them \(file OUT_DIR/libr10blob\.a only with them\): it reads them",
        )

    def test_a_search_directory_that_is_or_lies_beneath_a_symbolic_link_out_of_out_dir(self) -> None:
        # r12 verifier: the search directory is itself a symbolic link to a
        # directory of the tree (or lies beneath one), and was walked as
        # generated, through the link, recording no link inside it.
        for search, library in (("prebuilt", "shared"), (f"prebuilt/{this_host()}", f"shared/{this_host()}")):
            with self.subTest(search=search):
                self.repo = GitRepo(Path(tempfile.mkdtemp(prefix="linked-", dir=self.scratch.name)).resolve())
                build_rs = (
                    "fn main() {\n"
                    '    let out = std::env::var("OUT_DIR").unwrap();\n'
                    '    let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();\n'
                    '    let link = format!("{out}/prebuilt");\n'
                    "    let _ = std::fs::remove_file(&link);\n"
                    '    std::os::unix::fs::symlink(format!("{dir}/../../shared"), &link).unwrap();\n'
                    '    println!("cargo:rerun-if-changed=build.rs");\n'
                    f'    println!("cargo:rustc-link-search=native={{out}}/{search}");\n'
                    '    println!("cargo:rustc-link-lib=static=r10blob");\n'
                    "}\n"
                )
                self.assert_linked_read(
                    "", r"shared covers \S+/libr10blob\.a, and the linker, searching native=\S+/" + search
                    + r" for the build script of a through a symbolic link, reads " + library + "$",
                    build_rs, f"{library}/libr10blob.a",
                )


class TrustLaneTests(unittest.TestCase):
    """`targo trust` compiles a member of the consumer's workspace with
    cfg(trust_verify), which no check sets, and every unit with debug
    assertions and overflow checks on (compile_error! probes, seal 9192: a
    path dependency outside the workspace got both and no trust_verify under
    `targo trust check --release`, neither under `--unverified`)."""

    def test_a_trust_build_that_compiles_a_member_of_the_consumer_is_refused(self) -> None:
        member = "path+file:///c/a#0.1.0"
        graph = {
            "version": 1,
            "units": [{
                "pkg_id": member, "target": {"name": "a", "kind": ["lib"]}, "mode": "check",
                "features": [], "dependencies": [], "profile": {"panic": "unwind"}, "platform": None,
            }],
            "roots": [0],
        }
        packages = {member: {"id": member, "name": "a", "version": "0.1.0", "source": None}}
        for command, members, refused in (
            ("trust check -p a", frozenset({member}), True),
            ("--unverified check -p a", frozenset({member}), False),
            ("trust check -p a", frozenset(), False),
        ):
            with self.subTest(command=command, members=sorted(members)):
                build = ppp.parse_build("lane", command)
                if refused:
                    with self.assertRaisesRegex(ppp.Refusal, "a member of the consumer's workspace"):
                        ppp.build_cone(graph, frozenset({"a"}), packages, build, members)
                else:
                    self.assertEqual(
                        ppp.build_cone(graph, frozenset({"a"}), packages, build, members).compiled,
                        frozenset({"a"}),
                    )



# --- r2 verifiers: reads another host makes, and the runtime layers ------------

MAIN_RS = 'fn main() { print!("{}", a::blob()); }\n'
# The tail of a crates/a/src/lib.rs whose blob() reads a file only on OS_NAME.
GATED_TAIL = '#[cfg(not(target_os = "OS_NAME"))]\npub fn blob() -> &\'static str { "none\\n" }\n'
# crates/a/src/lib.rs for an ungated build script: R10_BLOB's bytes.
LINKED_LIB = (
    'extern "C" { static R10_BLOB: [u8; 4]; }\n'
    "pub fn blob() -> String {\n"
    "    unsafe { String::from_utf8_lossy(&*core::ptr::addr_of!(R10_BLOB)).into_owned() }\n}\n"
)


def literal_read(line: int, spelled: str, target: str = "shared/blob.bin", pattern: str = "shared") -> str:
    """The refusal when a string literal of crates/a/build.rs names `target`."""
    return (
        rf"{pattern} covers {re.escape(target)}, and crates/a/build\.rs \(a file of the build "
        rf"script of a\), whose string literal on line {line} names '{re.escape(spelled)}' from "
        rf"its package's directory, reads {re.escape(target)}"
    )


def strictly_read(name: str, pattern: str, line: int) -> str:
    """The refusal when a file under a reviewed exclusion that a build reads
    spells `.incbin` with no string literal."""
    return (
        rf"{re.escape(name)} \(a tracked file under exclusion {pattern} that a build reads\) "
        rf"spells '\.incbin' on line {line} with a file name that is no string literal"
    )


def build_script_rs(*body: str) -> str:
    """crates/a/build.rs running `body`, watching only itself."""
    return "fn main() {\n" + "".join(f"    {line}\n" for line in body) + (
        '    println!("cargo:rerun-if-changed=build.rs");\n}\n'
    )


def host_gated_build_rs(source: str, arguments: str = "", watch: str = "", gated: bool = True) -> str:
    """cc-rs style: (only when compiling for OS_NAME, where `gated`) assemble
    `source`, archive and link it; `watch` is printed before the host test."""
    return (
        "use std::process::Command;\n"
        "fn main() {\n"
        + (f'    println!("cargo:rerun-if-changed={watch}");\n' if watch else "")
        + ('    if std::env::var("CARGO_CFG_TARGET_OS").unwrap() != "OS_NAME" { return; }\n' if gated else "")
        + '    let out = std::env::var("OUT_DIR").unwrap();\n'
        f'    let status = Command::new("cc").args([{arguments}"-c", "{source}", "-o"])\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
        '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
        "    assert!(status.success());\n"
        '    println!("cargo:rustc-link-search=native={out}");\n'
        '    println!("cargo:rustc-link-lib=static=r10blob");\n'
        "}\n"
    )


class OtherHostReadTests(OneCrate):
    """Reads a consumer makes where a check on this host sees none. The r2
    verifiers of 7621f22a3 measured each shape: gated on this host, the consumer
    prints `one` at the pin and `two` at live main (it reads the excluded
    change), and gated on the other host (trust-mc also builds on Linux), the
    gate at 7621f22a3 returned with no refusal."""

    def refused_whichever_host(
        self, files: dict[str, str], live_main_files: dict, message: Any,
        exclusions: Sequence = ("shared",), links: Optional[dict[str, str]] = None,
        patched: Sequence[str] = (),
    ) -> None:
        """`message`: the refusal, or per host the shape is gated on; `patched`:
        BuildInputs scans switched off, so a later layer refuses alone."""
        for os_name in (this_host(), other_host()):
            with self.subTest(gated_on=os_name):
                shapes = tempfile.mkdtemp(prefix=f"shapes-{os_name}-", dir=self.scratch.name)
                self.repo = GitRepo(Path(shapes).resolve())
                pin = self.pin(
                    {name: text.replace("OS_NAME", os_name) for name, text in files.items()},
                    {name: target for name, target in (links or {}).items()},
                )
                live_main = self.repo.commit(live_main_files)
                if os_name == this_host():
                    with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
                        printed = [consumer_output(self.repo, rev, Path(work), MAIN_RS) for rev in (pin, live_main)]
                    self.assertEqual(printed, ["one\n", "two\n"])
                expected = message[os_name] if isinstance(message, dict) else message
                with contextlib.ExitStack() as stack:
                    for scan in patched:
                        stack.enter_context(
                            unittest.mock.patch.object(ppp.BuildInputs, scan, lambda self, closure: None)
                        )
                    self.assert_read(pin, live_main, excluding(*exclusions), expected)

    def refused_here(self, files: dict[str, str], live_main_files: dict, message: str) -> str:
        """The shape runs on every host; the consumer reads the change. Returns
        the pin and live main, for a layer test."""
        pin = self.pin(files)
        live_main = self.repo.commit(live_main_files)
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [consumer_output(self.repo, rev, Path(work), MAIN_RS) for rev in (pin, live_main)]
        self.assertEqual(printed, ["one\n", "two\n"])
        self.assert_read(pin, live_main, excluding("shared"), message)
        return pin, live_main

    # A build script hands the excluded file itself to the tool, only on one
    # host (r2 R0): no directive lies between.
    def test_an_excluded_source_a_build_script_assembles_only_on_one_host(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/build.rs": host_gated_build_rs("../../shared/blob.S"),
                "crates/a/src/lib.rs": GATED_LIB,
                "shared/blob.S": DEFINING_S + '.ascii "one\\n"\n',
            },
            {"shared/blob.S": DEFINING_S + '.ascii "two\\n"\n'},
            literal_read(5, "../../shared/blob.S", "shared/blob.S"),
        )

    # A build script reads a file of the tree by a literal path only for one
    # host and hands it to rustc through the environment (r2 P5).
    def test_a_build_script_reads_a_literal_path_only_for_one_host(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/build.rs": build_script_rs(
                    'let text = if std::env::var("CARGO_CFG_TARGET_OS").unwrap() == "OS_NAME" {',
                    '    std::fs::read_to_string("../../shared/blob.bin").unwrap()',
                    '} else { "none".to_string() };',
                    'println!("cargo:rustc-env=A_BLOB={}", text.trim());',
                ),
                "crates/a/src/lib.rs": 'pub fn blob() -> String { format!("{}\\n", env!("A_BLOB")) }\n',
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            literal_read(3, "../../shared/blob.bin"),
        )

    # The module files a file a `path` attribute names declares (r2 R3, P1):
    # rustc resolves `mod m;` there beside it, under whatever cfg.
    PLATFORM_LIB = (
        '#[cfg(target_os = "OS_NAME")]\n#[path = "../../../platform/mod.rs"]\nmod platform;\n'
        '#[cfg(target_os = "OS_NAME")]\npub use platform::blob;\n' + GATED_TAIL
    )

    def test_an_include_in_a_module_of_a_path_attribute_target(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/src/lib.rs": self.PLATFORM_LIB,
                "platform/mod.rs": "mod imp;\npub use imp::blob;\n",
                "platform/imp.rs": 'pub fn blob() -> &\'static str { include_str!("../shared/blob.bin") }\n',
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            {
                this_host(): r"shared covers shared/blob\.bin, and ",
                other_host(): (
                    r"shared covers shared/blob\.bin, and platform/imp\.rs \(which `mod imp;` on line 1 "
                    r"of platform/mod\.rs names\), whose include_str! on line 1 names "
                    r"'\.\./shared/blob\.bin' under whatever cfg, reads shared/blob\.bin"
                ),
            },
        )

    def test_a_module_of_a_path_attribute_target_that_is_excluded(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/src/lib.rs": self.PLATFORM_LIB,
                "platform/mod.rs": "mod imp;\npub use imp::blob;\n",
                "platform/imp.rs": 'pub fn blob() -> &\'static str { "one\\n" }\n',
            },
            {"platform/imp.rs": 'pub fn blob() -> &\'static str { "two\\n" }\n'},
            {
                this_host(): r"platform covers platform/imp\.rs, and ",
                other_host(): (
                    r"platform covers platform/imp\.rs, and platform/mod\.rs \(which the path "
                    r"attribute on line 2 of crates/a/src/lib\.rs names\), whose `mod imp;` on line 1 "
                    r"names it under whatever cfg, reads platform/imp\.rs"
                ),
            },
            exclusions=("platform",),
        )

    def test_a_child_module_of_a_path_attributed_file_under_the_exclusion(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/src/lib.rs": (
                    '#[cfg(target_os = "OS_NAME")]\n#[path = "../../../shared/imp.rs"]\nmod imp;\n'
                    '#[cfg(target_os = "OS_NAME")]\npub fn blob() -> &\'static str { imp::blob() }\n'
                    + GATED_TAIL
                ),
                "shared/imp.rs": "mod inner;\npub fn blob() -> &'static str { inner::BLOB }\n",
                "shared/inner.rs": 'pub const BLOB: &str = "one\\n";\n',
            },
            {"shared/inner.rs": 'pub const BLOB: &str = "two\\n";\n'},
            {
                this_host(): r"shared covers shared/inner\.rs, and ",
                other_host(): (
                    r"shared covers shared/inner\.rs, and shared/imp\.rs \(which the path attribute on "
                    r"line 2 of crates/a/src/lib\.rs names\), whose `mod inner;` on line 1 names it"
                ),
            },
        )

    # A tracked symbolic link to a directory of modules in the package (r2
    # P2): rustc reads through it, and `..` climbs from where it points.
    def test_an_include_in_a_module_under_a_linked_directory(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/src/lib.rs": (
                    '#[cfg(target_os = "OS_NAME")]\nmod common;\n'
                    '#[cfg(target_os = "OS_NAME")]\npub fn blob() -> &\'static str { common::blob() }\n'
                    + GATED_TAIL
                ),
                "common/mod.rs": "pub fn blob() -> &'static str { include_str!(\"../shared/blob.bin\") }\n",
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            {
                this_host(): r"shared covers shared/blob\.bin, and ",
                other_host(): (
                    r"shared covers shared/blob\.bin, and crates/a/src/common/mod\.rs \([^)]*\), whose "
                    r"include_str! on line 1 names '\.\./shared/blob\.bin' under whatever cfg"
                ),
            },
            links={"crates/a/src/common": "../../../common"},
        )

    # An include in a macro's body is resolved from the file that calls the
    # macro (r2 P3; rustc's resolve_path takes the call site's span).
    def test_an_include_in_a_macro_body_reads_by_name(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/src/lib.rs": (
                    "#[macro_use]\nmod macros;\n"
                    '#[cfg(target_os = "OS_NAME")]\npub fn blob() -> &\'static str { shared_blob!() }\n'
                    + GATED_TAIL
                ),
                "crates/a/src/macros/mod.rs": (
                    "#[allow(unused_macros)]\n"
                    'macro_rules! shared_blob { () => { include_str!("../../../shared/blob.bin") } }\n'
                ),
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            {
                this_host(): r"shared covers shared/blob\.bin, and ",
                other_host(): (
                    r"shared covers shared/blob\.bin, and crates/a/src/macros/mod\.rs \(a Rust file of "
                    r"package a\), whose include_str! on line 2, in a macro's body, names "
                    r"'\.\./\.\./\.\./shared/blob\.bin' from wherever the macro is called"
                ),
            },
        )

    # An include of literals `concat!` puts together (r2 P4).
    def test_an_include_of_concatenated_literals(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/src/lib.rs": (
                    '#[cfg(target_os = "OS_NAME")]\npub fn blob() -> &\'static str '
                    '{ include_str!(concat!("../../../shared/", "blob.bin")) }\n' + GATED_TAIL
                ),
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            {
                this_host(): r"shared covers shared/blob\.bin, and ",
                other_host(): (
                    r"shared covers shared/blob\.bin, and crates/a/src/lib\.rs \(a Rust file of package "
                    r"a\), whose include_str! on line 2 names '\.\./\.\./\.\./shared/blob\.bin' under "
                    r"whatever cfg"
                ),
            },
        )

    # A library module in the directory of a binary target (r2 P8), which the
    # directory walk skips: the `mod` declaration reaches it.
    def test_a_library_module_in_a_binary_targets_directory(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/Cargo.toml": PACKAGE.format("a") + '\n[[bin]]\nname = "gen"\npath = "src/gen/main.rs"\n',
                "crates/a/src/gen/main.rs": "fn main() {}\n",
                "crates/a/src/lib.rs": (
                    '#[cfg(target_os = "OS_NAME")]\nmod gen;\n'
                    '#[cfg(target_os = "OS_NAME")]\npub fn blob() -> &\'static str { gen::blob() }\n'
                    + GATED_TAIL
                ),
                "crates/a/src/gen/mod.rs": (
                    "pub fn blob() -> &'static str { include_str!(\"../../../../shared/blob.bin\") }\n"
                ),
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            {
                this_host(): r"shared covers shared/blob\.bin, and ",
                other_host(): (
                    r"shared covers shared/blob\.bin, and crates/a/src/gen/mod\.rs \(which `mod gen;` on "
                    r"line 2 of crates/a/src/lib\.rs names\), whose include_str! on line 1"
                ),
            },
        )

    # A file under a reviewed exclusion that a build does read is read strictly
    # (r2 R4, P6, P10, P11): 7621f22a3 read every such file leniently, so a
    # `.incbin` whose name a -D define supplies passed on the other host.
    DEFINED = '"-DBLOB_PATH=\\"../../shared/blob.bin\\"", '

    def test_an_included_file_under_a_reviewed_exclusion_spells_a_define(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/build.rs": host_gated_build_rs("src/blob.S", self.DEFINED, "src/blob.S"),
                "crates/a/src/lib.rs": GATED_LIB,
                "crates/a/src/blob.S": DEFINING_S + '#include "../../../asm/common.inc"\n',
                "asm/common.inc": ".incbin BLOB_PATH\n",
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            strictly_read("asm/common.inc", "asm", 1),
            exclusions=("shared", "asm"),
        )

    def test_a_linked_source_under_a_reviewed_exclusion_spells_a_define(self) -> None:
        self.refused_whichever_host(
            {
                "crates/a/build.rs": host_gated_build_rs("src/blob.S", self.DEFINED, "src/blob.S"),
                "crates/a/src/lib.rs": GATED_LIB,
                "asm/blob.S": DEFINING_S + ".incbin BLOB_PATH\n",
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            strictly_read("asm/blob.S", "asm", 9),
            exclusions=("shared", "asm"),
            links={"crates/a/src/blob.S": "../../../asm/blob.S"},
        )

    def test_a_named_source_under_a_reviewed_exclusion_spells_a_define(self) -> None:
        # The build script names it with a literal, behind the host test.
        self.refused_whichever_host(
            {
                "crates/a/build.rs": host_gated_build_rs("../../asm/blob.S", self.DEFINED),
                "crates/a/src/lib.rs": GATED_LIB,
                "asm/blob.S": DEFINING_S + ".incbin BLOB_PATH\n",
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            strictly_read("asm/blob.S", "asm", 9),
            exclusions=("shared", "asm"),
        )

    def test_a_watched_source_under_a_reviewed_exclusion_spells_a_define(self) -> None:
        # With the build script's literals not read, the watched path, which
        # the build script prints before its host test, is read strictly.
        self.refused_whichever_host(
            {
                "crates/a/build.rs": host_gated_build_rs("../../asm/blob.S", self.DEFINED, "../../asm/blob.S"),
                "crates/a/src/lib.rs": GATED_LIB,
                "asm/blob.S": DEFINING_S + ".incbin BLOB_PATH\n",
                "shared/blob.bin": "one\n",
            },
            {"shared/blob.bin": "two\n"},
            strictly_read("asm/blob.S", "asm", 9),
            exclusions=("shared", "asm"),
            patched=("scan_build_scripts",),
        )

    # What a build script does on this host with the excluded file that neither
    # the read witness nor the absence pass of 7621f22a3 sees: each is refused
    # by the build script's literal, and by its runtime layer alone.
    def test_a_build_script_that_syncs_an_untracked_copy_from_an_excluded_file(self) -> None:
        # r2 R1b: it writes into the tree of the pin, so the checks without the
        # file compile what the checks with it left there.
        pin, live_main = self.refused_here(
            {
                "crates/a/build.rs": (
                    "use std::path::Path;\nfn main() {\n"
                    '    let canonical = Path::new("../../shared/blob.txt");\n'
                    '    let copy = Path::new("src/generated/blob.txt");\n'
                    "    if canonical.exists() {\n"
                    '        std::fs::create_dir_all("src/generated").unwrap();\n'
                    "        let _ = std::fs::remove_file(copy);\n"
                    "        std::fs::copy(canonical, copy).unwrap();\n"
                    "    }\n"
                    '    println!("cargo:rerun-if-changed=build.rs");\n}\n'
                ),
                "crates/a/src/lib.rs": 'pub fn blob() -> &\'static str { include_str!("generated/blob.txt") }\n',
                "shared/blob.txt": "one\n",
            },
            {"shared/blob.txt": "two\n"},
            literal_read(3, "../../shared/blob.txt", "shared/blob.txt"),
        )
        with without_build_inputs():
            self.assert_read(
                pin, live_main, excluding("shared"),
                r"checking the pinned packages changed the tree of the pin \(1 file\(s\) added, first "
                r"crates/a/src/generated/blob\.txt\): a build script writes into it",
            )

    def test_a_prebuilt_object_else_the_packaged_source(self) -> None:
        # r2 R2c: OUT_DIR holds the same names either way; only bytes differ.
        def object_file(text: str) -> bytes:
            with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
                directory = Path(work)
                (directory / "b.S").write_text(DEFINING_S + f'.ascii "{text}\\n"\n', encoding="utf-8")
                subprocess.run(["cc", "-c", "b.S", "-o", "b.o"], cwd=directory, check=True)
                return (directory / "b.o").read_bytes()

        (self.repo.root / "shared").mkdir(parents=True, exist_ok=True)
        (self.repo.root / "shared/blob.o").write_bytes(object_file("one"))
        build_rs = (
            "use std::process::Command;\nfn main() {\n"
            '    let out = std::env::var("OUT_DIR").unwrap();\n'
            '    let prebuilt = std::path::Path::new("../../shared/blob.o");\n'
            "    if prebuilt.exists() {\n"
            '        std::fs::copy(prebuilt, format!("{out}/blob.o")).unwrap();\n'
            "    } else {\n"
            '        let status = Command::new("cc").args(["-c", "src/blob.S", "-o"])\n'
            '            .arg(format!("{out}/blob.o")).status().unwrap();\n'
            "        assert!(status.success());\n"
            "    }\n"
            '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
            '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
            "    assert!(status.success());\n"
            '    println!("cargo:rerun-if-changed=build.rs");\n'
            '    println!("cargo:rustc-link-search=native={out}");\n'
            '    println!("cargo:rustc-link-lib=static=r10blob");\n}\n'
        )
        pin = self.pin({
            "crates/a/build.rs": build_rs,
            "crates/a/src/lib.rs": LINKED_LIB,
            "crates/a/src/blob.S": DEFINING_S + '.ascii "pkg\\n"\n',
        })
        (self.repo.root / "shared/blob.o").write_bytes(object_file("two"))
        live_main = self.repo.commit({})
        with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
            printed = [consumer_output(self.repo, rev, Path(work), MAIN_RS) for rev in (pin, live_main)]
        self.assertEqual(printed, ["one\n", "two\n"])
        self.assert_read(pin, live_main, excluding("shared"), literal_read(4, "../../shared/blob.o", "shared/blob.o"))
        with without_build_inputs():
            self.assert_read(
                pin, live_main, excluding("shared"),
                r"leaves otherwise than with them \(file OUT_DIR/blob\.o holds other bytes\)",
            )

    def test_a_copy_or_default_of_the_same_name(self) -> None:
        # r2 P7: the copy is a clone, and a default of that name replaces it.
        pin, live_main = self.refused_here(
            {
                "crates/a/build.rs": (
                    "use std::process::Command;\nfn main() {\n"
                    '    let out = std::env::var("OUT_DIR").unwrap();\n'
                    '    println!("cargo:rerun-if-changed=build.rs");\n'
                    '    println!("cargo:rerun-if-changed=src/blob.S");\n'
                    '    if std::fs::copy("../../shared/local.inc", format!("{out}/config.inc")).is_err() {\n'
                    '        std::fs::write(format!("{out}/config.inc"), ".ascii \\"none\\"\\n").unwrap();\n'
                    "    }\n"
                    '    let status = Command::new("cc").args(["-c", "src/blob.S", "-I"]).arg(&out).arg("-o")\n'
                    '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
                    "    assert!(status.success());\n"
                    '    let status = Command::new("ar").args(["crs"]).arg(format!("{out}/libr10blob.a"))\n'
                    '        .arg(format!("{out}/blob.o")).status().unwrap();\n'
                    "    assert!(status.success());\n"
                    '    println!("cargo:rustc-link-search=native={out}");\n'
                    '    println!("cargo:rustc-link-lib=static=r10blob");\n}\n'
                ),
                "crates/a/src/lib.rs": LINKED_LIB,
                "crates/a/src/blob.S": DEFINING_S + '#include "config.inc"\n',
                "shared/local.inc": '.ascii "one\\n"\n',
            },
            {"shared/local.inc": '.ascii "two\\n"\n'},
            literal_read(6, "../../shared/local.inc", "shared/local.inc"),
        )
        with without_build_inputs():
            self.assert_read(pin, live_main, excluding("shared"), r"leaves otherwise than with them \(file OUT_DIR/")

    def test_an_optional_file_only_live_main_adds(self) -> None:
        # r2 P9: the pin does not hold it, so no access time or absence shows it.
        self.refused_here(
            {
                "crates/a/build.rs": build_script_rs(
                    'let text = std::fs::read_to_string("../../shared/override.txt")',
                    '    .unwrap_or_else(|_| "one".to_string());',
                    'println!("cargo:rustc-env=A_BLOB={}", text.trim());',
                ),
                "crates/a/src/lib.rs": 'pub fn blob() -> String { format!("{}\\n", env!("A_BLOB")) }\n',
                "shared/README.txt": "overrides go here\n",
            },
            {"shared/override.txt": "two\n"},
            literal_read(2, "../../shared/override.txt", "shared/override.txt"),
        )

    # Controls: shapes the r2 verifiers proposed that 7621f22a3 already refused
    # (the read witness; a read of OUT_DIR through a Rust include).
    def test_a_build_script_that_syncs_a_tracked_copy_from_an_excluded_file(self) -> None:
        pin, live_main = self.refused_here(
            {
                "crates/a/build.rs": build_script_rs(
                    'let canonical = std::path::Path::new("../../shared/blob.txt");',
                    'if canonical.exists() { std::fs::copy(canonical, "src/blob.txt").unwrap(); }',
                ),
                "crates/a/src/lib.rs": 'pub fn blob() -> &\'static str { include_str!("blob.txt") }\n',
                "crates/a/src/blob.txt": "packaged\n",
                "shared/blob.txt": "one\n",
            },
            {"shared/blob.txt": "two\n"},
            literal_read(2, "../../shared/blob.txt", "shared/blob.txt"),
        )
        with without_build_inputs():
            self.assert_read(pin, live_main, excluding("shared"), WITNESSED.format("txt"))

    def test_an_out_dir_file_chosen_by_whether_an_excluded_file_exists(self) -> None:
        for case, body, lib, pin_files, live_main_files in (
            (
                "copy",
                [
                    'let out = std::env::var("OUT_DIR").unwrap();',
                    'let canonical = std::path::Path::new("../../shared/blob.txt");',
                    'let source = if canonical.exists() { canonical } else { std::path::Path::new("data/blob.txt") };',
                    'std::fs::copy(source, format!("{out}/blob.txt")).unwrap();',
                ],
                'pub fn blob() -> &\'static str { include_str!(concat!(env!("OUT_DIR"), "/blob.txt")) }\n',
                {"crates/a/data/blob.txt": "packaged\n", "shared/blob.txt": "one\n"},
                {"shared/blob.txt": "two\n"},
            ),
            (
                "config",
                [
                    'let out = std::env::var("OUT_DIR").unwrap();',
                    'let have = std::path::Path::new("../../shared/flag").exists();',
                    'std::fs::write(format!("{out}/config.rs"), format!("pub const HAVE: bool = {have};\\n")).unwrap();',
                ],
                'include!(concat!(env!("OUT_DIR"), "/config.rs"));\n'
                "pub fn blob() -> &'static str { if HAVE { \"one\\n\" } else { \"two\\n\" } }\n",
                {"shared/flag": ""},
                {"shared/flag": None},
            ),
        ):
            with self.subTest(case=case):
                self.repo = GitRepo(Path(tempfile.mkdtemp(prefix=f"{case}-", dir=self.scratch.name)).resolve())
                pin = self.pin({"crates/a/build.rs": build_script_rs(*body), "crates/a/src/lib.rs": lib, **pin_files})
                live_main = self.repo.commit(live_main_files)
                with tempfile.TemporaryDirectory(dir=self.scratch.name) as work:
                    printed = [consumer_output(self.repo, rev, Path(work), MAIN_RS) for rev in (pin, live_main)]
                self.assertEqual(printed, ["one\n", "two\n"])
                self.assert_read(pin, live_main, excluding("shared"), r"shared covers shared/")
                with without_build_inputs():
                    self.assert_read(
                        pin, live_main, excluding("shared"), r"which is neither in the tree of the pin"
                    )

    def test_literals_naming_what_nothing_excludes_pass(self) -> None:
        # No false refusal: a build script literal, a macro include and a
        # `concat!` include that name files no exclusion covers.
        pin = self.pin({
            "crates/a/build.rs": build_script_rs('let _ = std::fs::read_to_string("../../shared/blob.bin");'),
            "crates/a/src/lib.rs": (
                "macro_rules! text { () => { include_str!(\"data/blob.txt\") } }\n"
                "pub fn blob() -> &'static str { text!() }\n"
                "pub fn other() -> &'static str { include_str!(concat!(\"data/\", \"blob.txt\")) }\n"
            ),
            "crates/a/src/data/blob.txt": "one\n",
            "shared/blob.bin": "one\n",
            "docs/notes.txt": "one\n",
        })
        live_main = self.repo.commit({"docs/notes.txt": "two\n"})
        self.assert_unread(pin, live_main, excluding("docs"))


class RustReadTests(unittest.TestCase):
    def test_what_an_include_names_with_literals_or_none(self) -> None:
        source = (
            'const A: &str = include_str!(concat!("../../../shared/", "a.txt"));\n'
            'const B: &str = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../shared/", "b.txt"));\n'
            'const C: &str = include_str!(concat!(env!("OUT_DIR"), "/c.txt"));\n'
            'const D: &str = include_str!(env!("D_PATH"));\n'
            'const E: &str = include_str!(concat!(env!("HOME"), "/e.txt"));\n'
            'macro_rules! f { ($p:expr) => { include_str!($p) } }\n'
            'macro_rules! g { () => { include_bytes!("../g.bin") } }\n'
            'const H: &str = include_str!(concat!("h", stringify!(x)));\n'
        )
        reads = ppp.rust_reads(source, Path("/t/crates/a/src/lib.rs"), Path("/t/crates/a"))
        self.assertEqual(
            [(read.line, read.what, read.spelled, read.joined and str(read.joined), read.in_macro) for read in reads],
            [
                (1, "include_str!", "../../../shared/a.txt", "/t/crates/a/src/../../../shared/a.txt", False),
                (2, "include_str!", "/../../shared/b.txt", "/t/crates/a/../../shared/b.txt", False),
                (4, "include_str!", None, None, False),
                (5, "include_str!", None, None, False),
                (6, "include_str!", None, None, True),
                (7, "include_bytes!", "../g.bin", "/t/crates/a/src/../g.bin", True),
                (8, "include_str!", None, None, False),
            ],
        )

    def test_a_module_is_looked_for_by_name_unless_a_plain_path_attribute_names_it(self) -> None:
        source = (
            "mod a;\n"
            '#[path = "x.rs"]\nmod b;\n'
            '#[cfg_attr(unix, path = "y.rs")]\nmod c;\n'
            "mod d { fn f() {} }\n"
            "pub(crate) mod r#e;\n"
            "// mod f;\n"
        )
        self.assertEqual(ppp.rust_modules(source), [(1, "a"), (5, "c"), (7, "e")])
        self.assertEqual(
            [str(path) for path in ppp.module_candidates(Path("/t/src/lib.rs"), "a")],
            ["/t/src/a.rs", "/t/src/a/mod.rs", "/t/src/lib/a.rs", "/t/src/lib/a/mod.rs"],
        )

    def test_an_ar_archive_is_compared_without_its_members_times(self) -> None:
        def member(name: bytes, time: bytes, data: bytes) -> bytes:
            header = name.ljust(16) + time.ljust(12) + b"0".ljust(6) + b"0".ljust(6) + b"644".ljust(8)
            header += str(len(data)).encode().ljust(10) + b"`\n"
            return header + data + (b"\n" if len(data) % 2 else b"")

        first = ppp.AR_MAGIC + member(b"a.o/", b"1700000000", b"abc") + member(b"b.o/", b"1", b"de")
        again = ppp.AR_MAGIC + member(b"a.o/", b"1800000000", b"abc") + member(b"b.o/", b"2", b"de")
        other = ppp.AR_MAGIC + member(b"a.o/", b"1700000000", b"abd") + member(b"b.o/", b"1", b"de")
        self.assertEqual(ppp._comparable(first), ppp._comparable(again))
        self.assertNotEqual(ppp._comparable(first), ppp._comparable(other))
        self.assertEqual(ppp._comparable(b"not an archive"), b"not an archive")


if __name__ == "__main__":
    unittest.main()
