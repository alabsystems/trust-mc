# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
"""kani-spec command line."""
from __future__ import annotations

import argparse
import difflib
import json
import shutil
import sys
import tempfile
from pathlib import Path

from . import SpecError
from .checkout import ensure_checkout
from .generate import compute_radii, generate_rev
from .overlay import load_overlay
from .pins import load_pins

TOOL_DIR = Path(__file__).resolve().parents[1]
REPO = TOOL_DIR.parents[1]
SPEC_FILES = ("clauses.json", "manifest.json", "oracles.jsonl", "units.jsonl")


def _selected(pins, names):
    if not names:
        return list(pins.revs.values())
    return [pins.by_rev(n) for n in names]


def _overlay(spec_dir: Path):
    path = spec_dir / "overlay.toml"
    return load_overlay(path), path.read_bytes()


def write_rev(spec_dir: Path, rev: str, files: dict) -> None:
    out = spec_dir / rev
    out.mkdir(parents=True, exist_ok=True)
    for name in SPEC_FILES:
        (out / name).write_bytes(files[name])


def cmd_fetch(args, pins):
    for pin in _selected(pins, args.rev):
        path = ensure_checkout(pins, pin, seeds=args.seed or (), offline=args.offline)
        print(f"{pin.name} {pin.rev} {path}")
    return 0


def cmd_generate(args, pins):
    spec_dir = Path(args.spec_dir)
    overlay, overlay_bytes = _overlay(spec_dir)
    for pin in _selected(pins, args.rev):
        files = generate_rev(pin, overlay, overlay_bytes)
        write_rev(spec_dir, pin.rev, files)
        manifest = json.loads(files["manifest.json"])
        print(f"{pin.name} {pin.rev}: {manifest['totals']['units']} units -> {spec_dir / pin.rev}")
    return 0


def cmd_check(args, pins):
    spec_dir = Path(args.spec_dir)
    overlay, overlay_bytes = _overlay(spec_dir)
    failures = []
    with tempfile.TemporaryDirectory(prefix="kani-spec-check-") as tmp:
        for pin in _selected(pins, args.rev):
            files = generate_rev(pin, overlay, overlay_bytes)
            write_rev(Path(tmp), pin.rev, files)
            for name in SPEC_FILES:
                fresh = Path(tmp) / pin.rev / name
                committed = spec_dir / pin.rev / name
                if not committed.is_file():
                    failures.append(f"{committed}: missing")
                    continue
                if fresh.read_bytes() != committed.read_bytes():
                    diff = difflib.unified_diff(
                        committed.read_text(encoding="utf-8").splitlines(),
                        fresh.read_text(encoding="utf-8").splitlines(),
                        str(committed), "regenerated", lineterm="", n=0)
                    failures.append(f"{committed}: differs\n" + "\n".join(list(diff)[:40]))
        if not args.rev:
            pinned = {p.rev for p in pins.revs.values()}
            for child in sorted(spec_dir.iterdir()):
                if child.is_dir() and child.name not in pinned:
                    failures.append(f"{child}: spec directory for an unpinned rev")
    if failures:
        print("kani-spec check FAILED:\n" + "\n".join(failures), file=sys.stderr)
        return 1
    print("kani-spec check: spec/kani regenerates byte-identically for "
          + ", ".join(p.rev[:12] for p in _selected(pins, args.rev)))
    return 0


def cmd_radius(args, pins):
    spec_dir = Path(args.spec_dir)
    overlay, _ = _overlay(spec_dir)
    for pin in _selected(pins, args.rev):
        for cid, ids in compute_radii(pin, overlay).items():
            print(f"# {cid} @ {pin.rev[:12]}: {len(ids)}")
            print(f'"{pin.rev}" = ' + json.dumps(ids, indent=2).replace("\n]", ",\n]") if ids else f'"{pin.rev}" = []')
    return 0


def cmd_counts(args, pins):
    spec_dir = Path(args.spec_dir)
    for pin in _selected(pins, args.rev):
        manifest = json.loads((spec_dir / pin.rev / "manifest.json").read_text(encoding="utf-8"))
        print(f"{pin.name} {pin.rev} ({manifest['kani_nightly']})")
        for s in manifest["suites"]:
            print(f"  {s['suite']:<18} {s['mode']:<16} units {s['units']:>4}  collected {s['upstream_collected']:>4}"
                  f"  harnesses {s['harnesses']:>4}  {s['classification']}")
        t = manifest["totals"]
        print(f"  {'TOTAL':<35} units {t['units']:>4}  collected {t['upstream_collected']:>4}"
              f"  harnesses {t['harnesses']:>4}  {t['classification']}")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(prog="kani-spec", description=__doc__)
    parser.add_argument("--pins", default=str(TOOL_DIR / "pins.toml"))
    parser.add_argument("--spec-dir", default=str(REPO / "spec" / "kani"))
    parser.add_argument("--check", action="store_true", help="same as the `check` subcommand")
    sub = parser.add_subparsers(dest="cmd")
    p = sub.add_parser("fetch", help="create or verify pinned checkouts in the cache")
    p.add_argument("--rev", action="append")
    p.add_argument("--seed", action="append", help="local clone to fetch pinned commits from first")
    p.add_argument("--offline", action="store_true")
    for name, help_text in (("generate", "write spec/kani/<rev>/"),
                            ("check", "regenerate into a temp dir and byte-compare with spec/kani"),
                            ("radius", "print computed overlay blast radii"),
                            ("counts", "print the committed per-suite table")):
        q = sub.add_parser(name, help=help_text)
        q.add_argument("--rev", action="append")
    args = parser.parse_args(argv)
    if args.check:
        args.cmd = "check"
        args.rev = getattr(args, "rev", None)
    if not args.cmd:
        parser.print_help()
        return 2
    pins = load_pins(Path(args.pins))
    try:
        return {"fetch": cmd_fetch, "generate": cmd_generate, "check": cmd_check,
                "radius": cmd_radius, "counts": cmd_counts}[args.cmd](args, pins)
    except SpecError as exc:
        print(f"kani-spec: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
