#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_first_party_git_pins import audit_repository


REV = "1" * 40


class FirstPartyGitPinTests(unittest.TestCase):
    def _audit(self, repository: str, manifests: dict[str, str]):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for relative, contents in manifests.items():
                manifest = root / relative
                manifest.parent.mkdir(parents=True, exist_ok=True)
                manifest.write_text(contents, encoding="utf-8")
            return audit_repository(root, repository)

    def _ay_manifest(self, replacement: str = "") -> str:
        declarations = []
        for package in [
            "ay",
            "ay-bindings",
            "ay-chc",
            "ay-core",
            "ay-dpll",
            "ay-encode",
            "ay-frontend",
            "ay-sys",
        ]:
            alias = package.replace("-", "_")
            declaration = (
                f'{alias} = {{ package = "{package}", '
                f'git = "https://github.com/alabsystems/ay.git", rev = "{REV}" }}'
            )
            declarations.append(declaration)
        manifest = "[workspace]\n[workspace.dependencies]\n" + "\n".join(declarations)
        return manifest.replace(declarations[0], replacement or declarations[0]) + "\n"

    def _clean_manifest(self, replacement: str = "") -> str:
        declarations = []
        for package in ["clean-kernel", "clean-mathverse", "clean-olean"]:
            alias = package.replace("-", "_")
            declaration = (
                f'{alias} = {{ package = "{package}", '
                f'git = "https://github.com/alabsystems/clean.git", rev = "{REV}" }}'
            )
            declarations.append(declaration)
        manifest = "[dependencies]\n" + "\n".join(declarations)
        return manifest.replace(declarations[0], replacement or declarations[0]) + "\n"

    def test_multiline_exact_declaration_is_accepted(self) -> None:
        manifest = "\n".join(
            line for line in self._ay_manifest().splitlines() if not line.startswith("ay = ")
        )
        manifest += (
            "\n[workspace.dependencies.ay]\n"
            'package = "ay"\n'
            'git = "https://github.com/alabsystems/ay.git"\n'
            f'rev = "{REV}"\n'
        )
        audit = self._audit("ay", {"Cargo.toml": manifest})
        self.assertEqual(audit.revision, REV)
        self.assertEqual(audit.declarations, 8)

    def test_workspace_inheritance_does_not_create_a_second_source(self) -> None:
        audit = self._audit(
            "ay",
            {
                "Cargo.toml": self._ay_manifest(),
                "member/Cargo.toml": (
                    '[package]\nname = "member"\nversion = "0.1.0"\n'
                    "[dependencies]\nay_core = { package = \"ay-core\", workspace = true }\n"
                ),
            },
        )
        self.assertEqual(audit.declarations, 8)

    def test_path_family_dependency_is_rejected(self) -> None:
        replacement = 'ay = { package = "ay", path = "../ay" }'
        with self.assertRaisesRegex(ValueError, "canonical Git source"):
            self._audit("ay", {"Cargo.toml": self._ay_manifest(replacement)})

    def test_new_path_family_dependency_is_rejected(self) -> None:
        manifest = self._ay_manifest() + '[dependencies]\nay-pb = { path = "../ay-pb" }\n'
        with self.assertRaisesRegex(ValueError, "canonical Git source"):
            self._audit("ay", {"Cargo.toml": manifest})

    def test_exact_crate_link_sibling_path_is_the_only_path_exception(self) -> None:
        audit = self._audit(
            "ay",
            {
                "Cargo.toml": self._ay_manifest(),
                "proofs/ay_pb_crate_link/Cargo.toml": (
                    '[package]\nname = "probe"\nversion = "0.1.0"\n'
                    '[dependencies]\nay-pb = { path = "../../../ay/crates/ay-pb" }\n'
                ),
            },
        )
        self.assertEqual(audit.declarations, 8)

    def test_branch_selector_is_rejected(self) -> None:
        replacement = (
            'ay = { package = "ay", '
            'git = "https://github.com/alabsystems/ay.git", '
            f'rev = "{REV}", branch = "main" }}'
        )
        with self.assertRaisesRegex(ValueError, "mixes exact Git authority"):
            self._audit("ay", {"Cargo.toml": self._ay_manifest(replacement)})

    def test_divergent_revision_is_rejected(self) -> None:
        replacement = (
            'ay = { package = "ay", '
            'git = "https://github.com/alabsystems/ay.git", rev = "'
            + "2" * 40
            + '" }'
        )
        with self.assertRaisesRegex(ValueError, "must use one revision"):
            self._audit("ay", {"Cargo.toml": self._ay_manifest(replacement)})

    def test_all_zero_revision_is_rejected(self) -> None:
        manifest = self._ay_manifest().replace(REV, "0" * 40)
        with self.assertRaisesRegex(ValueError, "nonzero full 40-character"):
            self._audit("ay", {"Cargo.toml": manifest})

    def test_missing_required_package_is_rejected(self) -> None:
        manifest = self._ay_manifest().replace(
            'ay_sys = { package = "ay-sys", '
            f'git = "https://github.com/alabsystems/ay.git", rev = "{REV}" }}\n',
            "",
        )
        with self.assertRaisesRegex(ValueError, "missing direct ay declarations"):
            self._audit("ay", {"Cargo.toml": manifest})

    def test_clean_family_exact_declarations_are_accepted(self) -> None:
        audit = self._audit("clean", {"Cargo.toml": self._clean_manifest()})
        self.assertEqual(audit.revision, REV)
        self.assertEqual(audit.declarations, 3)

    def test_clean_family_path_dependency_is_rejected(self) -> None:
        replacement = 'clean_kernel = { package = "clean-kernel", path = "../clean" }'
        with self.assertRaisesRegex(ValueError, "canonical Git source"):
            self._audit("clean", {"Cargo.toml": self._clean_manifest(replacement)})

    def test_clean_family_divergent_revision_is_rejected(self) -> None:
        replacement = (
            'clean_kernel = { package = "clean-kernel", '
            'git = "https://github.com/alabsystems/clean.git", rev = "'
            + "2" * 40
            + '" }'
        )
        with self.assertRaisesRegex(ValueError, "must use one revision"):
            self._audit("clean", {"Cargo.toml": self._clean_manifest(replacement)})


if __name__ == "__main__":
    unittest.main()
