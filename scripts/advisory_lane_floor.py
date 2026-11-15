#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Hold an advisory-lane Targo report to its committed floor.

`targo trust check --allow-l0-gaps` exits 0 on a CONDITIONAL-PASS: no failed
row, but any number of unknown, runtime-checked or assumed rows. That exit
status alone would let a lane silently lose proofs (a proved row turning
unknown) without anyone noticing. This check reads the report's own gate
counts and refuses when

* the report or its `verification_gate.counts` is missing or malformed,
* any row failed,
* the lane has no rows at all (a vacuous lane proves nothing), or
* fewer rows were proved than the committed floor.

Only `proved` counts toward the floor. Unknown, runtime-checked, assumed and
mandated rows never do. Passing this check is NOT a proof claim: the advisory
lane admits L0 gaps by construction.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

COUNT_KEYS = ("total", "proved", "failed", "unknown", "runtime_checked", "assumed")


class FloorError(Exception):
    """The report does not meet the lane's floor."""


def gate_counts(report: Path) -> dict[str, int]:
    try:
        data = json.loads(report.read_text(encoding="utf-8"))
    except (OSError, ValueError) as err:
        raise FloorError(f"cannot read {report}: {err}") from err
    gate = data.get("verification_gate") if isinstance(data, dict) else None
    counts = gate.get("counts") if isinstance(gate, dict) else None
    if not isinstance(counts, dict):
        raise FloorError(f"{report} has no verification_gate.counts")
    out: dict[str, int] = {}
    for key in COUNT_KEYS:
        value = counts.get(key)
        # bool is an int subclass; a boolean count is malformed, not 0/1.
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise FloorError(f"{report}: verification_gate.counts.{key} is {value!r}")
        out[key] = value
    return out


def check_floor(counts: dict[str, int], floor: int) -> None:
    if counts["failed"] > 0:
        raise FloorError(f"{counts['failed']} failed row(s)")
    if counts["total"] == 0:
        raise FloorError("no rows: a vacuous lane proves nothing")
    if counts["proved"] < floor:
        raise FloorError(
            f"{counts['proved']} proved < floor {floor} (unknown rows never count)"
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("report", type=Path, help="report.json written by --report-dir")
    parser.add_argument("--floor", type=int, required=True, help="minimum proved rows")
    parser.add_argument("--label", default="lane", help="name printed with the verdict")
    args = parser.parse_args(argv)
    if args.floor < 0:
        parser.error("--floor must be >= 0")
    try:
        counts = gate_counts(args.report)
        summary = ", ".join(f"{k}={counts[k]}" for k in COUNT_KEYS)
        check_floor(counts, args.floor)
    except FloorError as err:
        print(f"advisory-lane-floor: {args.label}: REFUSED: {err}", file=sys.stderr)
        return 1
    print(
        f"advisory-lane-floor: {args.label}: floor {args.floor} held ({summary}); "
        "advisory only, not a proof claim"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
