#!/usr/bin/env python3
"""Detect per-harness verdict INVERSIONS that file-level scoring cannot see.

A row whose file summary agrees with Kani can still have its individual harness
verdicts inverted -- trust-mc proving what Kani fails and failing what Kani
proves. `expected/ptr_to_ref_cast/invalid/test.rs` does exactly that, and its
summary line is byte-identical to Kani's, so no aggregate check can catch it.

Reports only; changes no classification.
"""
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parents[2]
TESTS = ROOT / "target/kani-domination/kani/tests"
DRIVER = ROOT / "target/trust-mc/bin/trust-mc-driver"

def expected_fail_set(exp_path):
    txt = exp_path.read_text(errors="replace")
    return set(re.findall(r"Verification failed for\s*-\s*(\S+)", txt))

def declared_flags(src):
    out = []
    for line in src.read_text(errors="replace").splitlines()[:15]:
        m = re.search(r"kani-flags:\s*(.*)", line)
        if m: out += m.group(1).split()
    return out

def actual_verdicts(src, flags):
    cmd = [str(DRIVER), "--ay-chc", "-Z", "unstable-options",
           "--harness-timeout=15s", *flags, str(src)]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=180)
    except subprocess.TimeoutExpired:
        return None
    out = p.stdout + p.stderr
    verdicts, cur = {}, None
    for line in out.splitlines():
        m = re.search(r"Checking harness ([A-Za-z0-9_:]+)", line)
        if m: cur = m.group(1); continue
        if cur and line.startswith("VERIFICATION:-"):
            verdicts[cur] = "FAIL" if "FAILED" in line or "VACUOUS" in line or "INCONCLUSIVE" in line else "PASS"
            cur = None
    return verdicts

def main():
    exps = sorted(TESTS.glob("**/*expected*"))
    rows = []
    for exp in exps:
        if exp.is_dir(): continue
        want_fail = expected_fail_set(exp)
        if not want_fail: continue
        # locate the test source next to the expected file
        cands = [p for p in exp.parent.glob("*.rs")]
        if len(cands) != 1: continue
        rows.append((cands[0], exp, want_fail))
    print(f"scanning {len(rows)} rows with per-harness oracles\n")
    inverted = []
    for src, exp, want_fail in rows:
        got = actual_verdicts(src, declared_flags(src))
        if not got: continue
        # harnesses Kani FAILS but trust-mc PASSES == potential missed bug
        missed = sorted(h for h in want_fail if got.get(h) == "PASS")
        # harnesses Kani PASSES but trust-mc FAILS == false positive
        fps = sorted(h for h, v in got.items() if v == "FAIL" and h not in want_fail)
        if missed:
            inverted.append((src, missed, fps))
            rel = src.relative_to(TESTS)
            print(f"  MISSED-BUG SHAPE  {rel}")
            print(f"      Kani fails, trust-mc PASSES: {missed}")
            if fps: print(f"      (also FP-shaped: {fps})")
    print(f"\n=== rows where trust-mc PASSES a harness Kani FAILS: {len(inverted)} ===")

main()
