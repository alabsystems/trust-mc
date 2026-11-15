#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT

"""Unit tests for scripts/advisory_lane_floor.py (no compiler is run)."""

from __future__ import annotations

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))

import advisory_lane_floor as floor  # noqa: E402


def counts(**overrides: int) -> dict[str, int]:
    base = {"total": 30, "proved": 10, "failed": 0, "unknown": 18,
            "runtime_checked": 2, "assumed": 0}
    base.update(overrides)
    return base


class FloorTests(unittest.TestCase):
    def setUp(self) -> None:
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.report = Path(tmp.name) / "report.json"

    def write(self, payload: object) -> None:
        self.report.write_text(json.dumps(payload), encoding="utf-8")

    def run_main(self, floor_value: int) -> int:
        return floor.main([str(self.report), "--floor", str(floor_value)])

    def test_meets_floor(self) -> None:
        self.write({"verification_gate": {"counts": counts()}})
        self.assertEqual(self.run_main(10), 0)

    def test_failed_row_refuses_even_above_floor(self) -> None:
        self.write({"verification_gate": {"counts": counts(failed=1)}})
        self.assertEqual(self.run_main(0), 1)

    def test_unknown_rows_never_count_toward_floor(self) -> None:
        self.write({"verification_gate": {"counts": counts(proved=3, unknown=500, total=503)}})
        self.assertEqual(self.run_main(4), 1)

    def test_vacuous_lane_refuses(self) -> None:
        self.write({"verification_gate": {"counts": counts(total=0, proved=0, unknown=0,
                                                           runtime_checked=0)}})
        self.assertEqual(self.run_main(0), 1)

    def test_missing_or_malformed_counts_refuse(self) -> None:
        for payload in ({}, {"verification_gate": {}}, [],
                        {"verification_gate": {"counts": {**counts(), "proved": True}}},
                        {"verification_gate": {"counts": {**counts(), "failed": -1}}},
                        {"verification_gate": {"counts": {k: v for k, v in counts().items()
                                                          if k != "unknown"}}}):
            with self.subTest(payload=payload):
                self.write(payload)
                self.assertEqual(self.run_main(0), 1)

    def test_missing_report_refuses(self) -> None:
        self.assertEqual(self.run_main(0), 1)


if __name__ == "__main__":
    unittest.main()
