#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
"""Codegen determinism gate over the soundness duals.

Compiles every file of ``tools/soundness-duals/manifest.toml`` ``--runs`` times
per lane (``bmc`` = default lane, ``chc`` = ``--ay-chc``) with
``--only-codegen --keep-temps`` and compares, per harness, the ``.smt2`` text
each run handed the solver. No solver runs.

Two texts are STRUCTURALLY EQUAL when they differ at most by a renaming of
declared symbols and by the order of the declarations: every declared name is
renamed by its first appearance in the non-declaration lines, the renamed
declarations are sorted, and everything else -- builtins, literals, the order
of assertions, rules and conjuncts -- is compared as written. A structural
difference is a different query: the solver sees other conjuncts, in another
order, or other constants, and a verdict that depends on that order flips from
run to run on one bundle (measured 2026-10-01: the BMC lane's allocation-root
disjointness order and the CHC lane's HashMap-ordered conjuncts and relation
columns).

Exit status: 0 when every harness is structurally equal across its runs (with
``--raw``, byte-identical), 1 when any is not, 2 on a refusal (no bundle, an
unreadable manifest, or a run that produced no text at all -- an empty
comparison must never read as a pass). A JSON report is written to
``--report`` when given.

Usage:
  scripts/check-codegen-determinism.py --bundle target/trust-mc --ay-dir DIR [--runs 3]
      [--jobs 3] [--lane bmc|chc]... [--only SUBSTR]... [--raw]
      [--keep DIR] [--report FILE]
"""

from __future__ import annotations

import argparse
import concurrent.futures
import glob
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

if sys.version_info < (3, 11):  # pragma: no cover - interpreter guard
    sys.exit("check-codegen-determinism.py needs python >= 3.11 (tomllib)")
import tomllib

REPO_ROOT = Path(__file__).resolve().parent.parent
DUALS = REPO_ROOT / "tools" / "soundness-duals"
LANES = ("bmc", "chc")

# A declaration line names its symbol right after the command.
_DECL_RE = re.compile(r"^\((declare-(?:const|var|fun|rel|datatypes?|sort))\s+(\|[^|]*\||[^\s()]+)")
_SYM_RE = re.compile(r"\|[^|]*\||[A-Za-z_~!@$%^&*+=<>.?/\-][A-Za-z0-9_~!@$%^&*+=<>.?/\-#']*")


def structure(text: str) -> str:
    """Canonical form of an SMT-LIB/CHC text up to renaming of declared symbols
    and declaration order (see the module docstring)."""
    lines = text.splitlines()
    declared = set()
    decls, body = [], []
    for line in lines:
        m = _DECL_RE.match(line)
        if m:
            declared.add(m.group(2))
            decls.append(line)
        else:
            body.append(line)
    names: dict[str, str] = {}

    def rename(mo: re.Match[str]) -> str:
        tok = mo.group(0)
        if tok not in declared:
            return tok
        if tok not in names:
            names[tok] = f"$v{len(names)}"
        return names[tok]

    out_body = [_SYM_RE.sub(rename, line) for line in body]
    out_decls = sorted(_SYM_RE.sub(rename, line) for line in decls)
    return "\n".join(out_decls) + "\n;;;;\n" + "\n".join(out_body)


def sha(data: str | bytes) -> str:
    if isinstance(data, str):
        data = data.encode("utf-8", "surrogateescape")
    return hashlib.sha256(data).hexdigest()[:16]


def load_tasks(manifest: Path, lanes: list[str], only: list[str], runs: int):
    data = tomllib.loads(manifest.read_text(encoding="utf-8"))
    tasks = []
    for entry in data.get("entry", []):
        path = entry["path"]
        if only and not any(s in path for s in only):
            continue
        for lane in entry.get("lanes", list(LANES)):
            if lane not in lanes:
                continue
            for i in range(runs):
                tasks.append((path, tuple(entry.get("flags", [])), lane, i))
    return tasks


def run_one(task, bundle: Path, env: dict, keep: Path | None, timeout: int):
    path, flags, lane, i = task
    src = (DUALS / path).resolve()
    with tempfile.TemporaryDirectory(prefix="det-") as work:
        shutil.copyfile(src, os.path.join(work, src.name))
        cmd = [str(bundle / "bin" / "trust-mc-driver"), src.name, "-Z", "unstable-options",
               "--only-codegen", "--keep-temps"]
        if lane == "chc":
            cmd.append("--ay-chc")
        cmd += list(flags)
        try:
            proc = subprocess.run(cmd, cwd=work, env=env, capture_output=True, timeout=timeout)
            rc: int | str = proc.returncode
        except subprocess.TimeoutExpired:
            rc = "timeout"
        texts = {}
        for f in sorted(glob.glob(os.path.join(work, "*.smt2"))):
            raw = open(f, "rb").read()
            name = os.path.basename(f)
            texts[name] = (sha(raw), sha(structure(raw.decode("utf-8", "surrogateescape"))))
            if keep is not None:
                shutil.copyfile(f, keep / f"{lane}-{i}-{name}")
        return path, lane, i, rc, texts


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--bundle", type=Path, required=True)
    ap.add_argument("--ay-dir", type=Path,
                    help="directory with the pinned ay CLI, put first on PATH (the driver refuses to "
                         "run without an ay binary, even for --only-codegen)")
    ap.add_argument("--manifest", type=Path, default=DUALS / "manifest.toml")
    ap.add_argument("--runs", type=int, default=3)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--lane", action="append", choices=LANES, dest="lanes")
    ap.add_argument("--only", action="append", default=[], help="manifest path substring filter")
    ap.add_argument("--raw", action="store_true", help="require byte-identical texts")
    ap.add_argument("--keep", type=Path, help="copy every emitted .smt2 here as <lane>-<run>-<name>")
    ap.add_argument("--report", type=Path)
    ap.add_argument("--timeout", type=int, default=600, help="per-compile timeout, seconds")
    args = ap.parse_args(argv)
    lanes = args.lanes or list(LANES)
    driver = args.bundle / "bin" / "trust-mc-driver"
    if not driver.is_file() or args.runs < 2 or args.jobs < 1:
        print(f"[determinism] REFUSED: need {driver} and --runs >= 2", file=sys.stderr)
        return 2
    try:
        tasks = load_tasks(args.manifest, lanes, args.only, args.runs)
    except (OSError, tomllib.TOMLDecodeError, KeyError) as err:
        print(f"[determinism] REFUSED: manifest: {err}", file=sys.stderr)
        return 2
    if args.keep is not None:
        args.keep.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env.pop("TRUST_MC_AY_BIN", None)
    if args.ay_dir is not None:
        env["PATH"] = f"{args.ay_dir}{os.pathsep}{env.get('PATH', '')}"
    if shutil.which("ay", path=env.get("PATH")) is None:
        print("[determinism] REFUSED: no ay binary on PATH; pass --ay-dir", file=sys.stderr)
        return 2
    env["TRUST_MC_SYSROOT"] = str(args.bundle)
    env["RUSTFLAGS"] = "-Awarnings"
    print(f"[determinism] {len(tasks)} compiles ({args.runs} runs, lanes={','.join(lanes)}, "
          f"jobs={args.jobs}), driver {sha(driver.read_bytes())}", flush=True)
    results = []
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for res in pool.map(lambda t: run_one(t, args.bundle, env, args.keep, args.timeout), tasks):
            results.append(res)

    groups: dict[tuple[str, str], list] = defaultdict(list)
    for path, lane, i, rc, texts in results:
        groups[(path, lane)].append((i, rc, texts))
    rows, refusals = [], []
    for (path, lane), runs in sorted(groups.items()):
        names = set()
        for _, _, texts in runs:
            names |= set(texts)
        if not names:
            refusals.append(f"{lane} {path}: no .smt2 emitted (exit {[r for _, r, _ in runs]})")
            continue
        for name in sorted(names):
            raw = [texts.get(name, ("missing", "missing"))[0] for _, _, texts in runs]
            st = [texts.get(name, ("missing", "missing"))[1] for _, _, texts in runs]
            if "missing" in raw:
                status = "missing-in-some-run"
            elif len(set(st)) > 1:
                status = "structural"
            elif len(set(raw)) > 1:
                status = "rename-only"
            else:
                status = "identical"
            rows.append({"lane": lane, "path": path, "smt2": name, "status": status,
                         "raw": raw, "structure": st})
    counts: dict[str, int] = defaultdict(int)
    for r in rows:
        counts[f"{r['lane']}:{r['status']}"] += 1
    bad = [r for r in rows
           if r["status"] in ("structural", "missing-in-some-run")
           or (args.raw and r["status"] == "rename-only")]
    for r in bad:
        print(f"[determinism] {r['status'].upper()} {r['lane']} {r['path']} {r['smt2']} "
              f"({len(set(r['structure']))} structures, {len(set(r['raw']))} texts)")
    for msg in refusals:
        print(f"[determinism] REFUSED: {msg}", file=sys.stderr)
    print("[determinism] " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    if args.report:
        args.report.write_text(json.dumps({"bundle": str(args.bundle), "runs": args.runs,
                                           "lanes": lanes, "raw_required": args.raw,
                                           "counts": counts, "rows": rows,
                                           "refusals": refusals}, indent=1))
    if refusals or not rows:
        return 2
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
