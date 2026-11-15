#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Tests for scripts/ay_cli_lane_config.py: ay's cargo config minus every -Ztrust-* token."""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

if sys.version_info >= (3, 11):
    from tomllib import loads as toml_loads
else:
    from tomli import loads as toml_loads

ROOT = Path(__file__).resolve().parent.parent
TOOL = ROOT / "scripts/ay_cli_lane_config.py"

# ay 4cadc2bf1's posture tables, ay 501caafdf's per-profile/per-triple ones, and
# the two-token `-Z trust-*` spelling, beside the things that must survive.
AY_CONFIG = """# comment
target-applies-to-host = false

[unstable]
target-applies-to-host = true
host-config = true
profile-rustflags = true

[host]
rustflags = ["-Ztrust-verify=on", "-Ztrust-policy=certify", "-Ztrust-ir-lower=strict"]

[target.'cfg(all())']
rustflags = ["-Ztrust-verify=on", "-Ztrust-policy=certify", "-Ztrust-verify-level=2",
    "-Ztrust-ir-lower=strict"]
rustdocflags = ["-Ztrust-verify=on"]

[profile.release.package."*"]
rustflags = ["-Ztrust-verify=off"]

[target.aarch64-apple-darwin]
rustflags = ["-C", "target-cpu=native", "-Ztrust-policy=advisory", "-Z", "trust-verify=off", "-Cdebuginfo=1"]
rustdocflags = ['-Ztrust-verify=off']

[target.x86_64-unknown-linux-musl]
linker = "./scripts/zig-cc-x86_64-linux-musl.sh"
rustflags = ["-C", "target-cpu=x86-64-v3"]

[profile.release]
lto = "thin"

[env]
SCCACHE_CACHE_SIZE = "50G"
CC_x86_64_unknown_linux_musl = { value = "scripts/zig-cc-x86_64-linux-musl.sh", relative = true }
"""


def run(source: str, *, config_name: str = ".cargo/config.toml") -> tuple[subprocess.CompletedProcess[str], str | None, Path]:
    """Derive `source` written as <tree>/<config_name>; returns (result, derived text, <tree>)."""
    with tempfile.TemporaryDirectory(prefix="ay cli lane config ") as tmp:
        tree = Path(tmp).resolve() / "ay"
        src = tree / config_name
        src.parent.mkdir(parents=True)
        out = Path(tmp) / "lane" / ".cargo" / "config.toml"
        src.write_text(source, encoding="utf-8")
        result = subprocess.run(
            [sys.executable, str(TOOL), str(src), str(out)], capture_output=True, text=True
        )
        return result, (out.read_text(encoding="utf-8") if out.exists() else None), tree


class LaneConfigTests(unittest.TestCase):
    def test_every_trust_token_is_removed_and_nothing_else_changes(self) -> None:
        result, text, tree = run(AY_CONFIG)
        self.assertEqual(result.returncode, 0, result.stderr)
        assert text is not None
        self.assertNotIn("trust-", text.split("Do not edit.")[1])
        doc = toml_loads(text)
        self.assertEqual(doc["host"]["rustflags"], [])
        self.assertEqual(doc["target"]["cfg(all())"]["rustflags"], [])
        self.assertEqual(doc["target"]["cfg(all())"]["rustdocflags"], [])
        self.assertEqual(doc["profile"]["release"]["package"]["*"]["rustflags"], [])
        self.assertEqual(
            doc["target"]["aarch64-apple-darwin"]["rustflags"],
            ["-C", "target-cpu=native", "-Cdebuginfo=1"],
        )
        self.assertEqual(doc["target"]["aarch64-apple-darwin"]["rustdocflags"], [])
        self.assertEqual(doc["target"]["x86_64-unknown-linux-musl"]["rustflags"], ["-C", "target-cpu=x86-64-v3"])
        # config-relative paths resolve against ay's tree, not the lane directory cargo runs in
        self.assertEqual(doc["target"]["x86_64-unknown-linux-musl"]["linker"], str(tree / "./scripts/zig-cc-x86_64-linux-musl.sh"))
        self.assertTrue(Path(doc["target"]["x86_64-unknown-linux-musl"]["linker"]).is_absolute())
        self.assertEqual(doc["profile"]["release"]["lto"], "thin")
        self.assertEqual(doc["unstable"], {"target-applies-to-host": True, "host-config": True, "profile-rustflags": True})
        self.assertFalse(doc["target-applies-to-host"])
        self.assertEqual(doc["env"]["SCCACHE_CACHE_SIZE"], "50G")
        self.assertEqual(doc["env"]["CC_x86_64_unknown_linux_musl"], str(tree / "scripts/zig-cc-x86_64-linux-musl.sh"))
        self.assertNotIn("relative", text.split("Do not edit.")[1])

    def test_relative_paths_become_absolute_under_the_source_tree_and_absolute_ones_stay(self) -> None:
        source = (
            "[target.x86_64-unknown-linux-musl]\n"
            'linker = "./scripts/zig-cc.sh"\n'
            "[target.aarch64-unknown-linux-musl]\n"
            'linker = "/opt/zig/zig-cc.sh"\n'
            "[target.aarch64-apple-darwin]\n"
            'linker = "clang"\n'
            "[env]\n"
            'A = { value = "scripts/a.sh", relative = true }\n'
            'B = { relative = true, value = "scripts/b.sh" }\n'
            'C = { value = "/abs/c.sh", relative = true }\n'
            'D = { value = "plain", relative = false }\n'
            'E = "literal"\n'
        )
        result, text, tree = run(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        assert text is not None
        doc = toml_loads(text)
        self.assertEqual(doc["target"]["x86_64-unknown-linux-musl"]["linker"], str(tree / "./scripts/zig-cc.sh"))
        self.assertEqual(doc["target"]["aarch64-unknown-linux-musl"]["linker"], "/opt/zig/zig-cc.sh")
        self.assertEqual(doc["target"]["aarch64-apple-darwin"]["linker"], "clang")  # a PATH lookup, not a path
        self.assertEqual(doc["env"]["A"], str(tree / "scripts/a.sh"))
        self.assertEqual(doc["env"]["B"], str(tree / "scripts/b.sh"))
        self.assertEqual(doc["env"]["C"], "/abs/c.sh")
        self.assertEqual(doc["env"]["D"], {"value": "plain", "relative": False})
        self.assertEqual(doc["env"]["E"], "literal")

    def test_an_input_that_is_not_a_dot_cargo_config_is_refused(self) -> None:
        # Without a `.cargo` parent there is no tree for relative paths to resolve against.
        result, text, _ = run(AY_CONFIG, config_name="config.toml")
        self.assertEqual(result.returncode, 2)
        self.assertIn(".cargo/config.toml", result.stderr)
        self.assertIsNone(text)

    def test_a_relative_env_value_the_tool_cannot_rewrite_textually_is_refused(self) -> None:
        # The dotted-key spelling parses to the same {value, relative} table but the textual
        # rewrite does not match it: the trees differ, so nothing is written.
        source = '[env]\nA.value = "scripts/a.sh"\nA.relative = true\n'
        result, text, _ = run(source)
        self.assertEqual(result.returncode, 2)
        self.assertIn("refusing to write", result.stderr)
        self.assertIsNone(text)

    def test_a_config_without_posture_is_reproduced(self) -> None:
        source = '[profile.release]\nlto = "thin"\n[target.aarch64-apple-darwin]\nrustflags = ["-C", "target-cpu=native"]\n'
        result, text, _ = run(source)
        self.assertEqual(result.returncode, 0, result.stderr)
        assert text is not None
        self.assertEqual(toml_loads(text), toml_loads(source))

    def test_malformed_toml_is_refused_and_nothing_is_written(self) -> None:
        result, text, _ = run("[host\nrustflags = [")
        self.assertEqual(result.returncode, 2)
        self.assertIn("not TOML", result.stderr)
        self.assertIsNone(text)

    def test_an_array_the_tool_cannot_rewrite_is_refused(self) -> None:
        # A non-literal element: the textual rewrite would not match the parsed tree.
        result, text, _ = run('[host]\nrustflags = ["-Ztrust-verify=on", 1]\n')
        self.assertEqual(result.returncode, 2)
        self.assertIsNone(text)

    def test_the_live_ay_config_derives_when_the_sibling_is_present(self) -> None:
        live = ROOT.parent / "ay" / ".cargo" / "config.toml"
        if not live.is_file():
            self.skipTest("no ../ay/.cargo/config.toml beside this checkout")
        result, text, _ = run(live.read_text(encoding="utf-8"))
        self.assertEqual(result.returncode, 0, result.stderr)
        assert text is not None
        for table in toml_loads(text).get("target", {}).values():
            for key in ("rustflags", "rustdocflags"):
                self.assertFalse([t for t in table.get(key, []) if t.startswith("-Ztrust")])
            linker = table.get("linker")
            if isinstance(linker, str) and "/" in linker:
                self.assertTrue(Path(linker).is_absolute(), linker)
        for value in toml_loads(text).get("env", {}).values():
            self.assertFalse(isinstance(value, dict) and value.get("relative") is True, value)
        self.assertFalse([t for t in toml_loads(text).get("host", {}).get("rustflags", []) if t.startswith("-Ztrust")])


if __name__ == "__main__":
    unittest.main()
