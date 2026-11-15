# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
import contextlib
import io
import json
import subprocess
import unittest
from pathlib import Path

from fixture import Workspace, git
from kani_spec import SpecError
from kani_spec.cli import main
from kani_spec.generate import generate_rev
from kani_spec.overlay import load_overlay
from kani_spec.pins import load_pins


def run_cli(ws, *args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = main(["--pins", str(ws.pins), "--spec-dir", str(ws.spec), *args])
    return code, out.getvalue(), err.getvalue()


class DeterminismTests(unittest.TestCase):
    def test_two_generations_are_byte_identical_and_sorted(self):
        with Workspace() as ws:
            pin = load_pins(ws.pins).revs["fixture"]
            overlay_path = ws.spec / "overlay.toml"
            overlay = load_overlay(overlay_path)
            first = generate_rev(pin, overlay, overlay_path.read_bytes())
            second = generate_rev(pin, overlay, overlay_path.read_bytes())
            self.assertEqual(first, second)
            ids = [json.loads(line)["id"] for line in first["units.jsonl"].decode().splitlines()]
            self.assertEqual(ids, sorted(ids))
            for line in first["oracles.jsonl"].decode().splitlines():
                self.assertEqual(line, json.dumps(json.loads(line), sort_keys=True, ensure_ascii=False,
                                                  separators=(",", ":")))
            manifest = json.loads(first["manifest.json"])
            self.assertEqual(manifest["spec_version"], f"kani@{pin.rev}+spec.1")
            self.assertEqual(manifest["kani_nightly"], "nightly-2099-01-01")
            self.assertNotIn(str(ws.cache), first["manifest.json"].decode())
            self.assertEqual(manifest["totals"]["units"], 16)
            self.assertEqual(manifest["totals"]["harnesses_cfg_inactive"], 3)

    def test_check_passes_after_generate_and_catches_edits(self):
        with Workspace() as ws:
            self.assertEqual(run_cli(ws, "generate")[0], 0)
            code, out, _ = run_cli(ws, "--check")
            self.assertEqual(code, 0, out)
            units = ws.spec / ws.rev / "units.jsonl"
            units.write_bytes(units.read_bytes().replace(b'"kani/Arith/add.rs"', b'"kani/Arith/ADD.rs"', 1))
            code, _, err = run_cli(ws, "check")
            self.assertEqual(code, 1)
            self.assertIn("units.jsonl: differs", err)

    def test_stale_overlay_blast_radius_is_refused(self):
        with Workspace() as ws:
            (ws.spec / "overlay.toml").write_text(
                'schema = "trust-mc.kani-spec.overlay/v1"\n[[correction]]\nid = "t"\nkind = "oracle"\n'
                'rule = "legacy-verdict:verification-successful-line"\nsource = "s"\naudit = "a"\n'
                f'[correction.blast_radius]\n"{ws.rev}" = []\n')
            code, _, err = run_cli(ws, "generate")
            self.assertEqual(code, 1)
            self.assertIn("blast radius", err)

    def test_dirty_or_moved_checkout_is_refused(self):
        with Workspace() as ws:
            pin = load_pins(ws.pins).revs["fixture"]
            overlay_path = ws.spec / "overlay.toml"
            (ws.checkout / "tests" / "kani" / "Arith" / "new.rs").write_text("#[kani::proof]\nfn n() {}\n")
            with self.assertRaises(SpecError):
                generate_rev(pin, load_overlay(overlay_path), overlay_path.read_bytes())
            (ws.checkout / "tests" / "kani" / "Arith" / "new.rs").unlink()
            (ws.checkout / "extra.txt").write_text("x")
            git(["add", "extra.txt"], ws.checkout)
            git(["commit", "--quiet", "-m", "moved"], ws.checkout)
            with self.assertRaises(SpecError):
                generate_rev(pin, load_overlay(overlay_path), overlay_path.read_bytes())

    def test_wrapper_script_runs_check(self):
        with Workspace() as ws:
            self.assertEqual(run_cli(ws, "generate")[0], 0)
            tool = Path(__file__).resolve().parents[1] / "kani-spec"
            proc = subprocess.run([str(tool), "--pins", str(ws.pins), "--spec-dir", str(ws.spec), "--check"],
                                  text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            self.assertEqual(proc.returncode, 0, proc.stderr)


if __name__ == "__main__":
    unittest.main()
