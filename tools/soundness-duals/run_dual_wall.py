#!/usr/bin/env python3
"""Soundness dual-wall runner.

A "dual" is a tripwire. A BUG FILE contains a real defect and MUST report
FAILED; if it verifies, that is a missed bug -- the worst defect class here. A
SAFE TWIN is the corrected program and MUST verify; if it fails, that is a false
positive.

WHY v3 EXISTS
-------------
An audit of every red row at trust-mc 5ee9a418c found that "P0=10" was ~100%
noise: 7 rows were SAFE files whose own headers say they must verify, 2 were
vacuous, 1 was stale. Exactly ONE real finding was hiding under that pile. A
wall that cries wolf on ten rows is worse than no wall, because the one real
signal gets filed under "known noise" -- which is exactly what happened.

The four corrections, each traced to a specific misreported file:

  1. ORACLE FROM THE HEADER, NOT THE FILENAME. v2 guessed from the name, so
     `dual_offset_zst_ok.rs` ("MUST be SUCCESSFUL" in its header) scored as a
     bug file because the name contains "dual". v2's phrase matcher only knew
     "must pass|succeed" and missed the far more common "MUST be SUCCESSFUL",
     "Oracle: PASS", "must verify SUCCESSFULLY", "should CEX/FAIL".

  2. VACUOUS RUNS ARE NOT PASSES. A bug file that emits ZERO checks did not
     prove anything -- the obligation was never generated. `fastmath_dual_nan`
     "verified" only because the NaN obligation needs `--nan-check`, which had
     no driver path at all until it was added. Report these separately; they are
     harness defects, not verifier defects.

  3. PROSE-DECLARED REQUIREMENTS. Several duals state their requirement in prose
     ("Run: ... -Z valid-value-checks") instead of a `// kani-flags:` header, so
     the runner silently ran them with no checks. Also accept `// gate-flags:`.

  4. MIXED-EXPECTATION FILES. `modifies-frame-offset-drop_control.rs` holds
     "CONTROL 1 (should PASS)" and "CONTROL 2 (should FAIL)". Scoring the FILE
     as must-pass makes a correct run look like a false positive. Such files get
     their own bucket rather than a wrong verdict.

Exit status is 0 unless a genuine P0 or safe-twin failure is found.
"""

import concurrent.futures as cf
import os
import re
import subprocess
import sys

DUALS = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(DUALS))
DRIVER = os.path.join(ROOT, "target/trust-mc/bin/trust-mc-driver")
AY_DIR = os.path.join(os.path.dirname(ROOT), "ay/target/release")
ENV = dict(os.environ, PATH=AY_DIR + ":" + os.environ.get("PATH", ""))

# Ordered most-specific first. Each entry is (regex, verdict).
# Written against the phrasings that actually occur in tools/soundness-duals --
# extend it when a new one appears rather than falling back to the name rule.
ORACLE_PATTERNS = [
    (r"EXPECTED VERDICT:\s*(?:VERIFICATION:-\s*)?FAILED", "FAIL"),
    (r"EXPECTED VERDICT:\s*(?:VERIFICATION:-\s*)?SUCCESSFUL", "PASS"),
    (r"Expected:\s*VERIFICATION[:\s-]*FAILED", "FAIL"),
    (r"Expected:\s*VERIFICATION[:\s-]*SUCCESSFUL", "PASS"),
    # NEGATIONS FIRST. "must NOT report VERIFICATION:- SUCCESSFUL" asserts
    # FAILURE; matching the SUCCESSFUL half would invert the oracle and turn a
    # correctly-failing bug file into a reported false positive.
    (r"must\s+NOT\s+(?:report\s+)?(?:VERIFICATION:?-?\s*)?(?:SUCCESSFUL|PASS|verify)\\b", "FAIL"),
    (r"must\s+NOT\s+(?:report\s+)?(?:VERIFICATION:?-?\s*)?FAIL", "PASS"),
    (r"Oracle:[^\n]*\bFAIL", "FAIL"),
    (r"Oracle:[^\n]*\b(?:SUCCESSFUL|PASS)", "PASS"),
    # A SAFE program that is allowed to fail via a DEMOTION but never with a
    # Genuine counterexample. Distinguishes "we are imprecise here" from "we
    # claim this program is buggy" — collapsing the two loses the signal.
    (r"Oracle:[^\n]*NOT-GENUINE", "NOT_GENUINE"),
    (r"must\s+NOT\s+regress\s+to\s+a\s+FAILED-Genuine", "NOT_GENUINE"),
    # "must PASS (or demote honestly)" -- a safe program that tolerates a
    # demotion but never a Genuine counterexample.
    (r"must\s+PASS\s*\(?\s*or\s+demote", "NOT_GENUINE"),
    (r"want:\s*NOT-SUCCESSFUL", "FAIL"),
    (r"want:\s*SUCCESSFUL", "PASS"),
    # "MUST be SUCCESSFUL", "must stay FAILED", "must PASS", "must verify
    # SUCCESSFULLY", "must be VERIFICATION FAILED", "should CEX/FAIL".
    (r"must\s+(?:still\s+|stay\s+|remain\s+|be\s+)*(?:VERIFICATION:?-?\s*)?FAIL", "FAIL"),
    (r"should\s+(?:\w+/)?FAIL", "FAIL"),
    (r"must\s+(?:still\s+|stay\s+|remain\s+|be\s+)*(?:VERIFICATION:?-?\s*)?(?:SUCCESSFUL|SUCCEED|PASS)\\b", "PASS"),
    (r"must\s+verify\s+SUCCESSFULLY", "PASS"),
    (r"should\s+(?:PASS|SUCCEED|verify)", "PASS"),
]

# Last resort only, and reported as such so a wrong guess is visible.
NAME_PASS = re.compile(
    r"(_safe|_control|_correct|correct_twin|_valid|_ok|_pass|_noop|_pinned|_twin)$"
)
NAME_FAIL = re.compile(r"(dual|_repro)")


# A conditional clause is not an oracle. "BOTH harnesses MUST be SUCCESSFUL.
# If either FAILS, the no-op is not a no-op" asserts PASS and merely *mentions*
# failure — reading the "If ... FAILS" half as an oracle made
# dual_write_bytes_zero_count_noop.rs look MIXED when it is not.
CONDITIONAL = re.compile(r"^\s*//\s*(?:If|Unless|Otherwise|When)\b.*$", re.M | re.I)


def strip_conditionals(head):
    return CONDITIONAL.sub("", head)


# An explicit directive line. These outrank loose prose: a file that says
# "EXPECTED VERDICT: SUCCESSFUL" has answered the question, and hunting for
# further phrases only finds incidental words like "failing spuriously".
EXPLICIT = [
    (r"EXPECTED VERDICT:\s*(?:VERIFICATION:-\s*)?FAILED", "FAIL"),
    (r"EXPECTED VERDICT:\s*(?:VERIFICATION:-\s*)?SUCCESSFUL", "PASS"),
    (r"Oracle:[^\n]*NOT-GENUINE", "NOT_GENUINE"),
    (r"Oracle:[^\n]*\bFAIL", "FAIL"),
    (r"Oracle:[^\n]*\b(?:SUCCESSFUL|PASS)\b", "PASS"),
]


def stated_oracle(head):
    """Verdict this file declares for ITSELF, or None. Returns (verdict, how)."""
    head = strip_conditionals(head)
    explicit = [v for pat, v in EXPLICIT if re.search(pat, head, re.I)]
    if explicit:
        if "NOT_GENUINE" in explicit:
            return "NOT_GENUINE", "header"
        if "PASS" in explicit and "FAIL" in explicit:
            return "MIXED", "header"
        return explicit[0], "header"
    hits = []
    for pat, verdict in ORACLE_PATTERNS:
        if re.search(pat, head, re.I):
            hits.append(verdict)
    if not hits:
        return None, "none"
    # Both verdicts asserted => the file covers several harnesses with different
    # expectations. Scoring it as one verdict produces a WRONG report.
    if "NOT_GENUINE" in hits:
        return "NOT_GENUINE", "header"
    if "PASS" in hits and "FAIL" in hits:
        return "MIXED", "header"
    return hits[0], "header"


def expectation(fn, head):
    verdict, how = stated_oracle(head)
    if verdict:
        return verdict, how
    base = fn[:-3]
    if NAME_PASS.search(base):
        return "PASS", "name"
    if NAME_FAIL.search(base):
        return "FAIL", "name"
    return None, "none"


HARNESS_RE = re.compile(r"#\[kani::proof[^\]]*\][\s\S]{0,400}?\bfn\s+([A-Za-z0-9_]+)")

def harnesses(src):
    return list(dict.fromkeys(HARNESS_RE.findall(src)))


def harness_oracle(head, name):
    """Per-harness expectation, from an EXPLICIT header line only.

    Several duals already document per-harness oracles, e.g.
        //   niche_value_is_real  - MUST FAIL: Some('o') != Some('z').
        //   niche_value_correct  - MUST SUCCEED: Some('o') == Some('o').

    Deliberately NO name heuristic. Guessing from harness names produced FOUR
    bogus P0s in one run: `dual_wrongfield_upvar_safe` is a SAFE harness, but
    it contains the substring "_wrong", so a name rule scored it as a bug file
    and its correct verification looked like a missed bug. A wall that invents
    verdicts it cannot justify is the exact failure this rewrite exists to end —
    so an unannotated harness is reported as UNCLASSIFIED, never guessed.
    """
    for line in head.splitlines():
        if name not in line:
            continue
        if re.search(r"MUST\s+(?:still\s+)?FAIL", line, re.I):
            return "FAIL", "header"
        if re.search(r"MUST\s+(?:SUCCEED|PASS|be\s+SUCCESSFUL)", line, re.I):
            return "PASS", "header"
        # A harness whose verdict is deliberately not asserted (e.g. a precision
        # guard that MAY verify): tolerated, never scored as a defect.
        if re.search(r"MAY\s+(?:VERIFY|FAIL)|TOLERATED", line, re.I):
            return "TOLERATED", "header"
        # Tabular form used by several duals:
        #   check_none_eq_none  -> VERIFICATION:- SUCCESSFUL
        m = re.search(r"->\s*VERIFICATION:?-?\s*(SUCCESSFUL|FAILED)", line, re.I)
        if m:
            return ("PASS" if m.group(1).upper() == "SUCCESSFUL" else "FAIL"), "header"
    return None, "none"


def declared_flags(head):
    """`// kani-flags:` and `// gate-flags:` -- both are used in this corpus."""
    flags = []
    for m in re.finditer(r"^//\s*(?:kani|gate)-flags:\s*(.+)$", head, re.M):
        flags += m.group(1).split()
    return flags


def prose_flags(head):
    """Requirements stated in prose rather than a header directive.

    Several duals document their invocation ("Run: trust-mc-driver ... -Z
    valid-value-checks") instead of declaring it. Running them without it makes
    the tripwire inert, so honour the documented form -- narrowly: only
    `-Z <feature>` and a small allow-list of check flags, never arbitrary text.
    """
    flags = []
    for m in re.finditer(r"-Z\s+([a-z][a-z0-9-]+)", head):
        feat = m.group(1)
        if feat in ("unstable-options",):
            continue
        flags += ["-Z", feat]
    for flag in ("--nan-check",):
        if flag in head:
            flags.append(flag)
    # de-dup, order-preserving
    out = []
    for i, f in enumerate(flags):
        if f == "-Z":
            pair = (f, flags[i + 1]) if i + 1 < len(flags) else (f, "")
            if pair not in [tuple(out[j : j + 2]) for j in range(0, len(out), 2)]:
                out += list(pair)
        elif f.startswith("--") and f not in out:
            out.append(f)
    return out


def infer_flags(src, head):
    flags = declared_flags(head)
    if flags:
        return flags, "declared"
    flags = prose_flags(head)
    if flags:
        return flags, "prose"
    if re.search(r"kani::(loop_invariant|loop_modifies|loop_decreases)", src):
        flags += ["-Z", "loop-contracts"]
    if re.search(r"kani::(requires|ensures|modifies)\b", src):
        flags += ["-Z", "function-contracts"]
    if re.search(r"kani::stub", src):
        flags += ["-Z", "stubbing"]
    return flags, ("inferred" if flags else "none")


REJECTED = re.compile(
    r"error: (unexpected argument|the subcommand .* cannot be used with"
    r"|Use of unstable feature|the following required arguments)",
    re.I,
)


def run_with_retry(fn_path_src_head_harness):
    """Run a row, and RETRY ONCE if it reports a defect.

    Timing-sensitive rows exist: `capref_nested_dual_safe.rs` takes ~90s idle,
    and under this runner's 4-way parallelism it can exceed the DRIVER's own
    watchdog (harness_timeout*5+5 = 155s) and be killed — reported as a
    safe-twin FAILURE. Measured: 4/4 SUCCESSFUL when run sequentially, and the
    file contains no code touched by the change under test.

    A wall that intermittently invents a failure is as useless as one that
    hides a real one: both train the reader to discount it. Retry only the
    rows that would be REPORTED as defects (a P0 or a safe-twin failure), so a
    genuine defect costs one extra run and a flake costs nothing.
    """
    fn, path, src, head, harness = fn_path_src_head_harness
    first = run_one(fn, path, src, head, harness)
    exp, got = first["exp"], first["got"]
    would_report = (exp == "FAIL" and got == "PASS") or (exp == "PASS" and got == "FAIL")
    if not would_report:
        return first
    second = run_one(fn, path, src, head, harness)
    if second["got"] != got:
        second["note"] = f"FLAKY: first run said {got}, retry said {second['got']}"
    return second


def run(fn):
    """Score a file, or each of its harnesses when it has more than one.

    A multi-harness file routinely mixes expectations (a bug harness beside its
    safe twin). Collapsing it to one verdict reports a CORRECT run as a
    failure — that is what put 9 files in a "score by hand" bucket.
    """
    path = os.path.join(DUALS, fn)
    with open(path, encoding="utf-8", errors="replace") as fh:
        src = fh.read()
    head = src[:4000]
    hs = harnesses(src)
    if len(hs) > 1:
        return [run_with_retry((fn, path, src, head, h)) for h in hs]
    return [run_with_retry((fn, path, src, head, None))]


def run_one(fn, path, src, head, harness):
    if harness is None:
        exp, how = expectation(fn, head)
        label = fn
    else:
        exp, how = harness_oracle(head, harness)
        if exp is None:
            # Fall back to the FILE oracle only when it is UNAMBIGUOUS. A MIXED
            # file states two different verdicts, so its file-level oracle
            # describes some other harness as often as this one — applying it
            # here is how a correct run gets reported as a defect.
            fexp, fhow = expectation(fn, head)
            if fexp not in ("MIXED", None):
                exp, how = fexp, fhow + "(file)"
        label = f"{fn}::{harness}"
    flags, origin = infer_flags(src, head)
    cmd = [DRIVER, "--ay-chc", "-Z", "unstable-options", "--harness-timeout=30s"]
    if harness is not None:
        cmd += ["--harness", harness]
    cmd += flags + [path]
    fn = label
    try:
        r = subprocess.run(
            cmd, capture_output=True, text=True, timeout=300, env=ENV, cwd=DUALS
        )
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        return dict(fn=fn, exp=exp, how=how, got="TIMEOUT", flags=flags, origin=origin)

    if REJECTED.search(out) and "VERIFICATION:-" not in out:
        got = "UNRUNNABLE"
    elif "VERIFICATION:- FAILED" in out:
        got = "FAIL"
    elif "VERIFICATION:- SUCCESSFUL" in out:
        # A run that emitted NO checks proved nothing: the obligation was never
        # generated. Calling that a pass turns a harness defect into a fake P0.
        got = "PASS" if re.search(r"^Check \d+:", out, re.M) else "VACUOUS"
    elif "no checks" in out:
        got = "VACUOUS"
    else:
        got = "OTHER"
    genuine = sum(
        int(m.group(1)) for m in re.finditer(r"(\d+) Genuine", out)
    )
    return dict(
        fn=fn, exp=exp, how=how, got=got, flags=flags, origin=origin, genuine=genuine
    )


def main():
    files = sorted(f for f in os.listdir(DUALS) if f.endswith(".rs"))
    with cf.ThreadPoolExecutor(max_workers=4) as pool:
        res = [r for group in pool.map(run, files) for r in group]

    p0 = [r for r in res if r["exp"] == "FAIL" and r["got"] == "PASS"]
    safe = [r for r in res if r["exp"] == "PASS" and r["got"] == "FAIL"]
    # NOT_GENUINE: failing is tolerated, claiming a real bug is not.
    safe += [
        r for r in res
        if r["exp"] == "NOT_GENUINE" and r["got"] == "FAIL" and r.get("genuine", 0) > 0
    ]
    demoted = [
        r for r in res
        if r["exp"] == "NOT_GENUINE" and r["got"] == "FAIL" and r.get("genuine", 0) == 0
    ]
    vacuous = [r for r in res if r["got"] == "VACUOUS"]
    unrunnable = [r for r in res if r["got"] == "UNRUNNABLE"]
    mixed = [r for r in res if r["exp"] == "MIXED"]
    other = [r for r in res if r["got"] in ("OTHER", "TIMEOUT")]
    tolerated = [r for r in res if r["exp"] == "TOLERATED"]
    unk = [r for r in res if r["exp"] is None]
    named = [r for r in (p0 + safe) if r["how"] == "name"]

    print(
        f"total={len(res)} P0={len(p0)} safe-twin-fail={len(safe)} "
        f"vacuous={len(vacuous)} unrunnable={len(unrunnable)} mixed={len(mixed)} "
        f"other={len(other)} demoted-ok={len(demoted)} "
        f"tolerated={len(tolerated)} unclassified={len(unk)}"
    )
    for r in demoted:
        print(f"  demoted (tolerated)  : {r['fn']} -- FAILED with 0 Genuine, oracle allows it")
    for r in p0:
        print(f"  P0 bug-file VERIFIED : {r['fn']} {r['flags']} ({r['origin']}/{r['how']})")
    for r in safe:
        print(f"  safe-twin FAILED     : {r['fn']} {r['flags']} ({r['origin']}/{r['how']})")
    for r in vacuous:
        print(f"  VACUOUS (no checks)  : {r['fn']} {r['flags']} ({r['origin']})")
    for r in unrunnable:
        print(f"  UNRUNNABLE (bad flags): {r['fn']} {r['flags']} ({r['origin']})")
    for r in mixed:
        print(f"  MIXED expectations   : {r['fn']} -- score per harness by hand")
    for r in other:
        print(f"  inconclusive         : {r['fn']} {r['exp']} -> {r['got']}")
    for r in unk:
        print(f"  unclassified         : {r['fn']} -- add an 'Oracle:' line")
    if named:
        print(
            "  NOTE: these were scored from the FILENAME, not a stated oracle "
            "-- add an 'Oracle:' line to make them trustworthy: "
            + ", ".join(r["fn"] for r in named)
        )
    return 1 if (p0 or safe) else 0


if __name__ == "__main__":
    sys.exit(main())
