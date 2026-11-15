#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Regression tests for tools/port/trust_only_arms.py."""

from __future__ import annotations

import contextlib
import io
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import trust_only_arms as toa  # noqa: E402

ROW = ("probe.rs", "operand_place", "op", 1, "RC(_)", "None", "no-place")
ARM = "#[cfg(trust_toolchain)]\n        Operand::RuntimeChecks(_) => None,"


def source(arms: str) -> str:
    return (
        "fn operand_place(op: &Operand) -> Option<Place> {\n"
        "    match op {\n"
        f"{arms}"
        "    }\n"
        "}\n"
    )


class ApplyRowTests(unittest.TestCase):
    def test_mention_in_body_or_comment_is_not_an_arm(self) -> None:
        # Behind the catch-all the compiler reports no E0004, so a name that only appears in a
        # comment or an arm body must not make the row look covered.
        src = source(
            "        // RuntimeChecks has no place\n"
            "        Operand::Copy(place) | Operand::Move(place) => Some(place.clone()),\n"
            '        other => describe(other, "RuntimeChecks"),\n'
        )
        new, status = toa.apply_row(src, ROW)
        self.assertEqual(status, "added")
        self.assertIn(ARM + "\n        other =>", new)

    def test_variant_in_nested_match_is_not_an_arm_of_the_outer_match(self) -> None:
        src = source(
            "        Operand::Copy(place) => Some(place.clone()),\n"
            "        _ => match inner { Operand::RuntimeChecks(_) => None, _ => None },\n"
        )
        new, status = toa.apply_row(src, ROW)
        self.assertEqual(status, "added")
        self.assertIn(ARM + "\n        _ => match inner", new)

    def test_arm_pattern_naming_the_variant_is_present(self) -> None:
        src = source(
            "        Operand::Copy(place) => Some(place.clone()),\n"
            "        #[cfg(trust_toolchain)]\n"
            "        Operand::RuntimeChecks(_) => None,\n"
            "        _ => None,\n"
        )
        new, status = toa.apply_row(src, ROW)
        self.assertEqual(status, "present")
        self.assertEqual(new, src)

    def test_variant_arm_behind_a_catch_all_is_stale(self) -> None:
        src = source(
            "        Operand::Copy(place) => Some(place.clone()),\n"
            "        _ => None,\n"
            "        Operand::RuntimeChecks(_) => None,\n"
        )
        with self.assertRaisesRegex(toa.StaleRow, "follows a catch-all arm"):
            toa.apply_row(src, ROW)

    def test_versioned_layout_macro_rows_still_require_the_scalable_vector_arm(self) -> None:
        for function, scrutinee, body in (
            ("try_from_ty", "layout_value_abi!(shape)", "None"),
            ("kani_mem_ty_validity_free", "&layout_value_abi!(shape)", "false"),
        ):
            with self.subTest(function=function):
                row, = (row for row in toa.ROWS if row[1] == function)
                src = (
                    f"fn {function}() {{\n"
                    f"    match {scrutinee} {{\n"
                    f"        ValueAbi::Scalar(_) => {body},\n"
                    f"        _ => {body},\n"
                    "    }\n"
                    "}\n"
                )
                new, status = toa.apply_row(src, row)
                self.assertEqual(status, "added")
                arm = f"ValueAbi::ScalableVector {{ .. }} => {body},"
                self.assertIn(f"{toa.CFG_TRUST}\n        {arm}", new)
                self.assertLess(new.index(arm), new.index(f"_ => {body},"))
                again, status = toa.apply_row(new, row)
                self.assertEqual(status, "present")
                self.assertEqual(again, new)


class MainTests(unittest.TestCase):
    def run_main(self, root: Path, rows: list, argv: list[str]) -> tuple[int, str]:
        stderr = io.StringIO()
        with mock.patch.object(toa, "SRC", root), mock.patch.object(toa, "ROWS", rows), \
                contextlib.redirect_stderr(stderr), contextlib.redirect_stdout(io.StringIO()):
            code = toa.main(argv)
        return code, stderr.getvalue()

    def test_every_stale_row_is_reported_before_a_nonzero_exit(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            good = source("        Operand::Copy(place) => Some(place.clone()),\n        _ => None,\n")
            (root / "probe.rs").write_text(good, encoding="utf-8")
            rows = [
                ("probe.rs", "moved_away", "op", 1, "RC(_)", "None", "no-place"),
                ROW,
                ("gone.rs", "operand_place", "op", 1, "RC(_)", "None", "no-place"),
            ]

            code, stderr = self.run_main(root, rows, ["--check"])
            self.assertEqual(code, 2)
            self.assertIn("probe.rs: no `match op` #1 in fn moved_away", stderr)
            self.assertIn("gone.rs: file not found", stderr)
            self.assertIn("1 arms missing; 3 rows; 2 stale", stderr)
            self.assertEqual((root / "probe.rs").read_text(encoding="utf-8"), good)

            # Without --check the rows that still match are applied, and the run still fails.
            code, stderr = self.run_main(root, rows, [])
            self.assertEqual(code, 2)
            self.assertIn(ARM, (root / "probe.rs").read_text(encoding="utf-8"))

    def test_clean_run_exits_zero(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "probe.rs").write_text(
                source("        Operand::Copy(place) => Some(place.clone()),\n        _ => None,\n"),
                encoding="utf-8",
            )
            self.assertEqual(self.run_main(root, [ROW], [])[0], 0)
            code, stderr = self.run_main(root, [ROW], ["--check"])
            self.assertEqual(code, 0)
            self.assertIn("0 arms missing; 1 rows; 0 stale", stderr)


if __name__ == "__main__":
    unittest.main(verbosity=2)
