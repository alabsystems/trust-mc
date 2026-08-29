#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path

from direct_driver_proof_core import (
    DEFAULT_INVENTORY,
    _derive_rows,
    _load_proof_inventory,
    _read_json_object,
    _repo_root_from_script,
    _validate_log,
    derive_direct_driver_report,
)


def _parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build a Rust-audit-compatible schema-v2 proof report from clean "
            "direct ./scripts/trust-mc --harness evidence."
        )
    )
    parser.add_argument("manifest", nargs="?", type=Path, help="Direct-driver proof manifest JSON")
    parser.add_argument("output_report", nargs="?", type=Path, help="Report JSON to write")
    parser.add_argument(
        "--inventory",
        type=Path,
        default=DEFAULT_INVENTORY,
        help=f"Proof inventory JSON path (default: {DEFAULT_INVENTORY})",
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=_repo_root_from_script(),
        help="TrustMC repository root",
    )
    parser.add_argument("--solver", default="ay", help="Solver binary name to attest")
    parser.add_argument("--self-test", action="store_true", help="Run parser self-tests")
    return parser.parse_args(argv)


def _proof_log_text() -> str:
    return "\n".join(
        [
            "Checking harness proof_one...",
            "[AY:PROOF] CHC verification: property proven",
            "[AY:PROOF_QUALIFIERS:clean]",
            "VERIFICATION:- SUCCESSFUL",
        ]
    )


def _write_self_test_inventory(path: Path) -> None:
    path.write_text(
        json.dumps(
            {
                "schema_version": 1,
                "denominator": 1,
                "rows": [
                    {
                        "file": "tests/trust-mc/example.rs",
                        "harness": "proof_one",
                        "expected": "PROOF",
                    }
                ],
            }
        ),
        encoding="utf-8",
    )


def _self_test_manifest(log_path: Path) -> dict[str, object]:
    return {
        "schema_version": 1,
        "runs": [
            {
                "file": "tests/trust-mc/example.rs",
                "harness": "proof_one",
                "log": str(log_path),
                "exit_code": 0,
                "command": [
                    "./scripts/trust-mc",
                    "-Z",
                    "unstable-options",
                    "--backend=ay",
                    "--ay-solver=ay",
                    "--ay-chc",
                    "--ay-chc-track=mem",
                    "--harness",
                    "proof_one",
                    "tests/trust-mc/example.rs",
                ],
                "time_sec": 0.125,
            }
        ],
    }


def _run_self_test() -> None:
    repo_root = _repo_root_from_script()
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        log_path = tmp_path / "proof.log"
        log_path.write_text(_proof_log_text(), encoding="utf-8")
        inventory_path = tmp_path / "inventory.json"
        _write_self_test_inventory(inventory_path)

        manifest_path = tmp_path / "manifest.json"
        manifest = _self_test_manifest(log_path)
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        rows = _derive_rows(
            manifest_path,
            manifest,
            repo_root=repo_root,
            proof_keys=_load_proof_inventory(inventory_path, repo_root),
        )
        assert rows[0]["proof_qualifiers"] == "clean"

        bad_log = "Checking harness proof_one...\n[AY:PROOF]\n[AY:PROOF_QUALIFIERS:sound_fallback=1]\n"
        try:
            _validate_log(bad_log, harness="proof_one", label="self-test")
        except ValueError as err:
            assert "not clean" in str(err)
        else:
            raise AssertionError("dirty proof qualifier should be rejected")


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(sys.argv[1:] if argv is None else argv)
    try:
        if args.self_test:
            _run_self_test()
            return 0
        if args.manifest is None or args.output_report is None:
            raise ValueError("manifest and output_report are required unless --self-test is used")
        repo_root = args.repo_root.resolve()
        manifest_path = args.manifest.resolve()
        inventory_path = args.inventory if args.inventory.is_absolute() else repo_root / args.inventory
        report = derive_direct_driver_report(
            manifest_path,
            _read_json_object(manifest_path),
            repo_root=repo_root,
            inventory_path=inventory_path,
            solver=args.solver,
        )
        args.output_report.parent.mkdir(parents=True, exist_ok=True)
        args.output_report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    except (AssertionError, ValueError) as err:
        print(f"error: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
