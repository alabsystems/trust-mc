#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Unit tests for scripts/check_doc_links.py: only links a change breaks fail."""

from __future__ import annotations

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
_SPEC = importlib.util.spec_from_file_location("check_doc_links", SCRIPTS / "check_doc_links.py")
links = importlib.util.module_from_spec(_SPEC)
sys.modules["check_doc_links"] = links
_SPEC.loader.exec_module(links)


def git(root: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(root), "-c", "user.name=t", "-c", "user.email=t@t", *args],
                          check=True, capture_output=True, text=True).stdout


class DocLinks(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="doc-links-")
        self.root = Path(self.tmp.name)
        (self.root / "docs").mkdir()
        (self.root / "docs" / "a.md").write_text(
            "[b](b.md) [anchor](#x) [web](https://example.com) [old](gone.md) `[code](nope.md)`\n")
        (self.root / "docs" / "b.md").write_text("# b\n")
        (self.root / "src.rs").write_text("\n")
        git(self.root, "init", "-q")
        git(self.root, "add", "-A")
        git(self.root, "commit", "-q", "-m", "base")
        self.base = git(self.root, "rev-parse", "HEAD").strip()

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def run_check(self) -> int:
        return links.main(["--repo", str(self.root), "--base", self.base])

    def test_links_parsed_and_resolved(self) -> None:
        text = (self.root / "docs" / "a.md").read_text()
        self.assertEqual(links.links(text), ["b.md", "#x", "https://example.com", "gone.md"])
        self.assertEqual(links.resolve("docs/a.md", "../src.rs#L1"), "src.rs")
        self.assertIsNone(links.resolve("docs/a.md", "#x"))

    def test_a_link_broken_at_the_base_is_reported_not_failed(self) -> None:
        self.assertEqual(self.run_check(), 0)

    def test_deleting_a_link_target_fails(self) -> None:
        (self.root / "docs" / "b.md").unlink()
        self.assertEqual(self.run_check(), 1)

    def test_a_new_broken_link_fails(self) -> None:
        (self.root / "docs" / "c.md").write_text("[x](missing.md)\n")
        self.assertEqual(self.run_check(), 1)

    def test_a_new_good_link_passes(self) -> None:
        (self.root / "docs" / "c.md").write_text("[x](../src.rs)\n")
        self.assertEqual(self.run_check(), 0)


if __name__ == "__main__":
    unittest.main()
