#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""Cargo precedence, environment custody and refusal controls for portable AY."""
import json
import os
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import ay_cli_build_policy as policy

HOST = "aarch64-apple-darwin"


def overrides(config):
    args = policy.floor_args(config, HOST, "apple-m1")
    assert args[::2] == ["--config"] * (len(args) // 2)
    return dict(item.split("=", 1) for item in args[1::2])


class BuildPolicyTests(unittest.TestCase):
    def test_nonempty_target_and_cfg_segments_get_suffix_only(self):
        result = overrides({"target": {HOST: {"rustflags": ["-C", "target-cpu=native"]},
                                        "cfg(all())": {"rustflags": ["--cfg", "keep_me"]}}})
        for key in (f'target."{HOST}".rustflags', 'target."cfg(all())".rustflags'):
            self.assertEqual(json.loads(result[key]), ["-C", "target-cpu=apple-m1"])

    def test_empty_segments_do_not_hide_build_fallback(self):
        result = overrides({"target": {HOST: {"rustflags": []}, "cfg(all())": {"rustflags": " "}},
                            "build": {"rustflags": ["--cfg", "build_fallback"]}})
        self.assertFalse(any(key.startswith("target.") for key in result))
        self.assertEqual(json.loads(result["build.rustflags"]), ["-C", "target-cpu=apple-m1"])

    def test_scalar_flags_preserve_original_text(self):
        original = '--cfg=kept -C target-cpu=native'
        result = overrides({"build": {"rustflags": original}})
        self.assertEqual(json.loads(result["build.rustflags"]), original + " -C target-cpu=apple-m1")

    def test_specific_host_linker_table_does_not_inherit_default_flags(self):
        result = overrides({"host": {"rustflags": ["--cfg", "default_only"], HOST: {"linker": "/owned/linker"}}})
        self.assertIn(f'host."{HOST}".rustflags', result)
        self.assertNotIn("host.rustflags", result)

    def test_default_host_is_not_shadowed_by_an_invented_specific_table(self):
        result = overrides({"host": {"rustflags": ["--cfg", "default_only"]}})
        self.assertIn("host.rustflags", result)
        self.assertNotIn(f'host."{HOST}".rustflags', result)

    def test_invalid_policy_and_native_target_routing_refuse(self):
        for config in ([], {"build": {"target": HOST}}, {"build": {"target": [HOST]}},
                       {"build": {"rustflags": 12}}, {"target": {HOST: {"rustflags": [False]}}},
                       {"host": {HOST: False}}, {"build": {"rustc-wrapper": "/ambient/wrapper"}},
                       {"env": {"CARGO_BUILD_RUSTC": "/ambient/rustc"}},
                       {"env": {"CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS": "-C target-cpu=native"}}):
            with self.subTest(config=config), self.assertRaises(ValueError):
                overrides(config)

    def test_query_and_build_share_scrubbed_flags_and_exact_compiler(self):
        builder = {"identity": {"build_policy": {"host": HOST}},
                   "trustc": "/exact/bin/trustc", "targo": "/exact/bin/targo"}
        names = ["RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "CARGO_BUILD_TARGET", "CARGO_TARGET_DIR",
                 "CARGO_BUILD_RUSTC", "CARGO_TARGET_AARCH64_APPLE_DARWIN_RUSTFLAGS", "CARGO_HOST_RUSTFLAGS",
                 "RUSTC_WRAPPER", "TRUST_STAGE2_BIN", "RUSTUP_TOOLCHAIN"]
        with patch.dict(os.environ, {**dict.fromkeys(names, "hostile"), "CARGO_HOME": "/owned/cache"}):
            env = policy.environment(builder)
        for key in names:
            if key != "CARGO_BUILD_RUSTC":
                self.assertNotIn(key, env)
        self.assertEqual(env["RUSTC"], builder["trustc"])
        self.assertEqual(env["CARGO_BUILD_RUSTC"], builder["trustc"])
        self.assertEqual(env["CARGO_HOME"], "/owned/cache")
        self.assertTrue(env["PATH"].startswith("/exact/bin" + os.pathsep))


if __name__ == "__main__":
    unittest.main()
