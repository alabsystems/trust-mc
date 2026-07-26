#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_portable_manifests import find_absolute_manifest_paths


class PortableManifestTests(unittest.TestCase):
    def _find(self, dependency: str) -> list[str]:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Cargo.toml").write_text(
                "[package]\nname = \"fixture\"\nversion = \"0.1.0\"\n"
                f"[dependencies]\ndep = {{ path = {dependency!r} }}\n",
                encoding="utf-8",
            )
            return find_absolute_manifest_paths(root)

    def test_relative_dependency_is_portable(self) -> None:
        self.assertEqual(self._find("../ay/crates/ay-pb"), [])

    def test_unix_absolute_dependency_is_rejected(self) -> None:
        absolute = str(Path("/").joinpath("Users", "example", "ay", "crates", "ay-pb"))
        findings = self._find(absolute)
        self.assertEqual(len(findings), 1)
        self.assertIn("host-absolute path", findings[0])

    def test_windows_absolute_dependency_is_rejected(self) -> None:
        absolute = "/".join(("C:", "Users", "example", "ay", "crates", "ay-pb"))
        findings = self._find(absolute)
        self.assertEqual(len(findings), 1)
        self.assertIn("host-absolute path", findings[0])


if __name__ == "__main__":
    unittest.main()
