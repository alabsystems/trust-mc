#!/usr/bin/env python3
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

"""Route duals: the same Kani fixtures through the Trustc route and the DevCli route.

Every fixture under tests/trust-lane/{casts,coercion,enum-eq,float-intrinsics,should-panic,vacuity}
is a set of pass/fail duals: a harness named `*_holds` must verify SUCCESSFUL, a harness named
`*_refuted` must verify FAILED, a harness named `*_unprovable` asserts a property the program may
violate when it runs (a Rust non-determinism) and must never be SUCCESSFUL, and a harness named
`*_vacuous` has contradictory assumptions, so it verifies NOTHING and must report VACUOUS — in the
default BMC lane and in the --ay-chc lane, on BOTH compiler routes. tests/trust-lane/float-intrinsics-direct
holds one fixture per route (`trust.rs` spells Trust core's intrinsics, `nightly.rs` the frozen
nightly's) with the same harnesses. tests/trust-lane/harness-names/modules.rs checks that both
routes report the same harness names and that --harness / --exact select the same harnesses
(Kani's crate-relative names). Harness names are unique across the dual fixtures, because the
tables below are keyed by lane and harness.

A case passes only when each route meets the expectation AND the two routes agree
harness by harness, counterexample category included.

Soundness rules, checked on every route: a `*_refuted`, `*_unprovable` or `*_vacuous` harness is
never SUCCESSFUL (that is a missed bug, a false proof, or a green proof of nothing), and a
`*_holds` harness without `#[kani::should_panic]` is never refuted by a counterexample the engine
certified as `Genuine` (that is a false bug report the engine vouches for).

The engine does not decide every dual. KNOWN_GAPS lists the honest non-proof outcomes it
reports (an uncertified FAILED, an INCONCLUSIVE, a fail-closed FAILED); both routes must
report exactly that verdict and category. KNOWN_DEFECTS lists places where the engine BREAKS
a soundness rule; a match prints a DEFECT line AND fails its case, so a run with a known
defect never exits 0. Any other deviation, including an engine improvement over a table
entry, fails the case until the table is updated. Prints one line per case; exits 1 when
any case is not as expected.
Every run's argv, stdout, stderr and exit code stay under OUT/<case>/<route>/.

Inputs (environment; defaults in brackets):
  TRUST_MC_DUALS_TRUSTC   canonical trustc      [bin/trustc of the seal scripts/resolve-trust-tool.sh
                          resolves: TRUST_MC_TRUST_TOOLCHAIN when set, else rust-toolchain.toml]
  TRUST_MC_DUALS_KEY      KEY directory          [target/trust-mc/keyed/driver-<PROVENANCE sha[:16]>]
  TRUST_MC_DUALS_DRIVER   Trust-built driver     [target/debug/trust-mc-driver]
  TRUST_MC_DUALS_DEVCLI   frozen DevCli bundle   [target/trust-mc]  STOCK-AS-ORACLE: the
                          nightly-built comparison bundle, kept by the owner's 2026-09-29 ruling;
                          `targo --unverified build-dev` now builds target/trust-mc on Trust
  TRUST_MC_DUALS_AY_BIN   pinned ay CLI          [scripts/build-pinned-ay-cli.sh --print-path]
  TRUST_MC_DUALS_OUT      run directory          [~/Library/Caches/trust-mc-t1/trust-lane-route-duals]
  TRUST_MC_DUALS_TIMEOUT  seconds per run        [900]
  TRUST_MC_DUALS_ONLY     comma-separated case-name substrings to run (default: all)
The run directory must not be under /tmp: trustc and the route preflight refuse
world-writable directories.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HOME = Path.home()
STORE = HOME / "Library/Application Support/aterm/pkg/store/trust"
FIXTURES = ROOT / "tests/trust-lane"

HARNESS_RE = re.compile(r"^Checking harness (\S+)\.\.\.$")
VERDICT_RE = re.compile(r"^VERIFICATION:- (\S+)")


def die(message: str) -> None:
    print(f"trust-lane-route-duals: error: {message}", file=sys.stderr)
    sys.exit(2)


def env_path(name: str, default: Path) -> Path:
    value = os.environ.get(name)
    return Path(value) if value else default


def driver_sha(sysroot: Path) -> str:
    provenance = sysroot / "PROVENANCE"
    if provenance.is_file():
        for line in provenance.read_text().splitlines():
            if line.startswith("artifact_driver_sha256="):
                return line.split("=", 1)[1].strip()
    import hashlib

    (driver,) = sorted((sysroot / "lib").glob("librustc_driver-*"))
    return hashlib.sha256(driver.read_bytes()).hexdigest()


def pinned_trustc() -> Path:
    """`bin/trustc` of the seal `scripts/resolve-trust-tool.sh` resolves (`TRUST_MC_TRUST_TOOLCHAIN`
    when set, else `rust-toolchain.toml`), as the smoke does; never a seal number written here."""
    resolver = ROOT / "scripts/resolve-trust-tool.sh"
    try:
        sysroot = subprocess.run([str(resolver), "sysroot"], capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as err:
        die(f"cannot resolve the pinned Trust sysroot: {err}")
    return Path(sysroot) / "bin/trustc"


def pinned_ay_cli() -> Path:
    """The ay CLI built at the Cargo.toml AY pin (`scripts/build-pinned-ay-cli.sh --print-path`)."""
    script = ROOT / "scripts/build-pinned-ay-cli.sh"
    try:
        return Path(subprocess.run([str(script), "--print-path"], capture_output=True, text=True, check=True).stdout.strip())
    except (OSError, subprocess.CalledProcessError) as err:
        die(f"cannot name the pinned ay CLI: {err}")


TRUSTC = env_path("TRUST_MC_DUALS_TRUSTC", Path("unset")) if os.environ.get("TRUST_MC_DUALS_TRUSTC") else pinned_trustc()
SYSROOT = TRUSTC.parent.parent
KEY = env_path(
    "TRUST_MC_DUALS_KEY",
    ROOT / "target/trust-mc/keyed" / f"driver-{driver_sha(SYSROOT)[:16]}" if TRUSTC.exists() else Path("missing"),
)
DYLIB = KEY / "codegen-backends/librustc_codegen_trust_mc.dylib"
DRIVER = env_path("TRUST_MC_DUALS_DRIVER", ROOT / "target/debug/trust-mc-driver")
DEVCLI = env_path("TRUST_MC_DUALS_DEVCLI", ROOT / "target/trust-mc")
AY_BIN = Path(os.environ["TRUST_MC_DUALS_AY_BIN"]) if os.environ.get("TRUST_MC_DUALS_AY_BIN") else pinned_ay_cli()
OUT = env_path("TRUST_MC_DUALS_OUT", HOME / "Library/Caches/trust-mc-t1/trust-lane-route-duals")
TIMEOUT = int(os.environ.get("TRUST_MC_DUALS_TIMEOUT", "900"))
ONLY = [s for s in os.environ.get("TRUST_MC_DUALS_ONLY", "").split(",") if s]


def child_env(sysroot: Path) -> dict[str, str]:
    """Nothing that could change what is compiled or solved, as the smoke does."""
    env = {
        k: v
        for k, v in os.environ.items()
        if not (k.startswith("TRUST_MC_") or k.startswith("AY_"))
        and k not in ("RUSTFLAGS", "RUSTC", "RUSTC_WRAPPER", "RUSTUP_TOOLCHAIN", "CARGO_TARGET_DIR", "CARGO_BUILD_TARGET_DIR")
    }
    env["TRUST_MC_SYSROOT"] = str(sysroot)
    env["TRUST_MC_AY_BIN"] = str(AY_BIN)
    return env


SHOULD_PANIC_RE = re.compile(r"#\[kani::should_panic\]\s*(?:#\[[^\]]*\]\s*)*fn\s+(\w+)")
HARNESS_FN_RE = re.compile(r"#\[kani::proof\]\s*(?:#\[[^\]]*\]\s*)*fn\s+(\w+)")


def should_panic_harnesses(fixture: Path) -> set[str]:
    """Harnesses in `fixture` carrying `#[kani::should_panic]` (attribute order free)."""
    text = fixture.read_text()
    found = set(SHOULD_PANIC_RE.findall(text))
    # `#[kani::should_panic]` may also follow `#[kani::proof]`.
    for m in re.finditer(r"#\[kani::proof\]\s*#\[kani::should_panic\]\s*(?:#\[[^\]]*\]\s*)*fn\s+(\w+)", text):
        found.add(m.group(1))
    return found


def run(case: str, route: str, fixture: Path, args: list[str]) -> dict:
    run_dir = OUT / case / route
    subprocess.run(["rm", "-rf", str(run_dir)], check=True)
    (run_dir / "target").mkdir(parents=True)
    if route == "trustc":
        argv = [str(DRIVER), str(fixture), *args, "--compiler-route", "trustc", "--trustc", str(TRUSTC),
                "--backend-dylib", str(DYLIB)]
        env = child_env(KEY)
    else:
        argv = [str(DEVCLI / "bin/trust-mc-driver"), str(fixture), *args]
        env = child_env(DEVCLI)
    argv += ["--target-dir", str(run_dir / "target")]
    (run_dir / "argv.json").write_text(json.dumps(argv, indent=1))
    try:
        proc = subprocess.run(argv, cwd=run_dir, env=env, stdin=subprocess.DEVNULL, capture_output=True,
                              text=True, timeout=TIMEOUT)
        code, stdout, stderr = proc.returncode, proc.stdout, proc.stderr
    except subprocess.TimeoutExpired as err:
        code = "timeout"
        stdout = err.stdout.decode(errors="replace") if isinstance(err.stdout, bytes) else (err.stdout or "")
        stderr = err.stderr.decode(errors="replace") if isinstance(err.stderr, bytes) else (err.stderr or "")
    (run_dir / "stdout.txt").write_text(stdout)
    (run_dir / "stderr.txt").write_text(stderr)
    (run_dir / "exit.txt").write_text(f"{code}\n")
    verdicts: dict[str, str] = {}
    order: list[str] = []
    current = None
    for line in stdout.splitlines():
        m = HARNESS_RE.match(line)
        if m:
            current = m.group(1)
            order.append(current)
            continue
        m = VERDICT_RE.match(line)
        if m and current is not None:
            verdicts[current] = m.group(1)
            current = None
    return {
        "exit": code,
        "harnesses": order,
        "verdicts": verdicts,
        "panicked": "panicked at" in stderr or "unexpectedly panicked" in stderr,
        "route_markers": sum(1 for l in stdout.splitlines() if l.startswith("[AY:COMPILER_ROUTE route=trustc ")),
        "errors": [l for l in (stdout + stderr).splitlines() if l.startswith("error")][:6],
        "stdout": stdout,
    }


# (lane, harness) -> (verdict, required [AY:CTREX_CAT:...] prefix, why). Honest non-proofs the engine
# reports on BOTH routes: an uncertified FAILED, an INCONCLUSIVE, a fail-closed FAILED, or a
# VACUOUS where the dual expected a decided answer. Measured
# 2026-09-12 after the parity-1 soundness repairs (Trustc route at the repair head; the DevCli
# bundle must reproduce every entry). None is a Trust difference.
GAP_BMC_BOX = "BMC: the call through Box/Rc/Arc<dyn> reads a receiver the encoding synthesized (unsupported_construct_fallback, pointee_synthesis_fallback)"
GAP_BMC_VIRTUAL = "BMC: a virtual call BMC cannot resolve runs no callee body and is counted (unsupported_construct_fallback)"
GAP_F16 = "no engine models f16/f128 min/max; the call fails closed (abs is modelled as a sign-bit clear)"
GAP_FN_ITEM_BMC = "BMC: a renamed float intrinsic reached as a fn item (F: Fn, &dyn Fn, Box<dyn Fn>, reduce, fold) has no body to inline on either route; the declined call is counted (unsupported_construct_fallback)"
GAP_FN_ITEM_CHC = "CHC: a renamed float intrinsic reached as a fn item has no body on either route; the call is an over-approximation (chc_sound_havoc_drop)"
GAP_ARITH_BMC = "BMC: the solver does not decide FP-theory arithmetic over the min/max relation's fresh choice"
GAP_ENUM_EQ_BMC = "BMC: the solver does not decide the REFUTATION of a derived `PartialEq` over a higher-order enum combinator's result (the `_holds` twins all verify)"
KNOWN_GAPS: dict[tuple[str, str], tuple[str, str, str]] = {
    ("bmc", "box_dyn_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "rc_dyn_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "arc_dyn_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "nonnull_slice_holds"): ("FAILED", "EncodingGap", "BMC: NonNull<[u8]>::len has no BV->Slice_bv8 cast encoding (unconstrained_assignment)"),
    ("bmc", "custom_slice_holds"): ("FAILED", "EncodingGap", "BMC: the slice behind a custom CoerceUnsized pointer is unconstrained (unconstrained_assignment)"),
    ("bmc", "custom_dyn_holds"): ("FAILED", "EncodingGap", "BMC: the receiver behind MyPtr<dyn Shape> is a fat pointer, never its own pointee; the read fails closed (unsupported_construct_fallback, unconstrained_assignment). Was a KNOWN_DEFECT: certified Genuine."),
    ("bmc", "box_id_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "rc_id_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "arc_id_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "nonnull_id_holds"): ("FAILED", "EncodingGap", GAP_BMC_VIRTUAL + ". Was certified Genuine (review C1)."),
    ("bmc", "nonnull_calm_callee_holds"): ("FAILED", "EncodingGap", GAP_BMC_VIRTUAL),
    ("bmc", "box_choice_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "box_size_of_val_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "rc_align_of_val_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "box_any_holds"): ("INCONCLUSIVE", "Unknown", "BMC: the solver runs out of memory on Box<dyn Any>::downcast_ref"),
    ("bmc", "upcast_box_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "upcast_rc_holds"): ("FAILED", "", "BMC: Rc<dyn Sub> -> Rc<dyn B> upcast fails with no counterexample category"),
    ("bmc", "rc_area_overflow_should_panic_holds"): ("FAILED", "EncodingGap", GAP_BMC_BOX),
    ("bmc", "f16_min_holds"): ("FAILED", "EncodingGap", GAP_F16),
    ("bmc", "f16_min_value_holds"): ("FAILED", "EncodingGap", GAP_F16),
    ("bmc", "f128_max_holds"): ("FAILED", "EncodingGap", GAP_F16),
    ("bmc", "direct_minimum32_nan_holds"): ("INCONCLUSIVE", "Unknown", "BMC: the solver does not decide the NaN-propagating minimumf32 over a symbolic float"),
    ("bmc", "direct_minimum32_nan_refuted"): ("INCONCLUSIVE", "Unknown", "BMC: the solver does not decide the NaN-propagating minimumf32 over a symbolic float"),
    ("chc", "nonnull_slice_holds"): ("FAILED", "EncodingGap", "CHC: NonNull<[u8]>::len falls back on signedness (signedness_fallback)"),
    ("chc", "custom_slice_holds"): ("FAILED", "EncodingGap", "CHC: the slice behind a custom CoerceUnsized pointer falls back on signedness"),
    ("chc", "custom_dyn_holds"): ("FAILED", "OverApproximation", "CHC: expression translations dropped behind the custom dyn pointer (chc_translation_drop)"),
    ("chc", "box_any_holds"): ("FAILED", "OverApproximation", "CHC: Box<dyn Any>::downcast_ref drops two havocs (chc_sound_havoc_drop=2)"),
    ("chc", "nonnull_panicking_callee_refuted"): ("INCONCLUSIVE", "", "CHC: the panicking virtual callee behind NonNull<dyn Tick> is not decided"),
    ("chc", "sp_unreachable_unchecked_holds"): ("FAILED", "Genuine", "CHC: the ub_checks precondition panic of unreachable_unchecked reaches a bare error head; V7 refuses a should_panic that rests on the anonymous chc.0 check (fail closed)"),
    ("chc", "f16_min_holds"): ("FAILED", "OverApproximation", GAP_F16 + " (chc_translation_drop, unhandled_calls)"),
    ("chc", "f16_min_value_holds"): ("FAILED", "OverApproximation", GAP_F16 + " (chc_translation_drop, unhandled_calls)"),
    ("chc", "f128_max_holds"): ("FAILED", "OverApproximation", GAP_F16 + " (chc_translation_drop, unhandled_calls)"),
    # The intrinsic as a FUNCTION ITEM (parity-1 second review, F-dyn). No engine runs a body for it on
    # either route: the nightly's `minnumf32` has none, and `callee_body` refuses Trust's fallback body.
    # BMC counts the declined call (it used to leave a free result and certify it Genuine); CHC keeps an
    # over-approximation. Honest non-proofs on both routes; the `_unprovable` twins are FAILED.
    ("bmc", "fnitem_min_value_holds"): ("FAILED", "EncodingGap", GAP_FN_ITEM_BMC),
    ("bmc", "dynfn_min_value_holds"): ("FAILED", "EncodingGap", GAP_FN_ITEM_BMC),
    ("bmc", "boxdynfn_max_value_holds"): ("FAILED", "EncodingGap", GAP_FN_ITEM_BMC),
    ("bmc", "fold_max_value_holds"): ("FAILED", "EncodingGap", GAP_FN_ITEM_BMC),
    ("bmc", "method_dynfn_max_value_holds"): ("FAILED", "EncodingGap", GAP_FN_ITEM_BMC),
    ("chc", "fnitem_min_value_holds"): ("FAILED", "OverApproximation", GAP_FN_ITEM_CHC),
    ("chc", "dynfn_min_value_holds"): ("FAILED", "OverApproximation", GAP_FN_ITEM_CHC),
    ("chc", "boxdynfn_max_value_holds"): ("FAILED", "OverApproximation", GAP_FN_ITEM_CHC),
    ("chc", "fold_max_value_holds"): ("FAILED", "OverApproximation", GAP_FN_ITEM_CHC + " (chc_translation_drop)"),
    ("chc", "method_dynfn_max_value_holds"): ("FAILED", "OverApproximation", GAP_FN_ITEM_CHC),
    # A min/max result in further float arithmetic (F-arith), BMC lane: the FP-theory binop over the
    # relation's fresh choice is not decided by the solver. CHC decides all of them exactly.
    ("bmc", "arith_add_pz_sign_holds"): ("INCONCLUSIVE", "Unknown", GAP_ARITH_BMC),
    ("bmc", "arith_recip_infinite_holds"): ("INCONCLUSIVE", "Unknown", GAP_ARITH_BMC),
    ("bmc", "arith_mul_neg_one_eq_zero_holds"): ("INCONCLUSIVE", "Unknown", GAP_ARITH_BMC),
    ("bmc", "arith_sub_zero_is_zero_holds"): ("INCONCLUSIVE", "Unknown", GAP_ARITH_BMC),
    ("bmc", "arith_sym_sum_is_x_holds"): ("INCONCLUSIVE", "Unknown", GAP_ARITH_BMC),
    # The `_refuted` twin of `arith_sym_sum_is_x_holds`, on the same symbolic sum. At ay
    # `501caafdf` the solver found the counterexample; at the pin main declares, `4cadc2bf1`
    # (measured 2026-09-13, both routes, `UNKNOWN_REASON:UndecidedModel`), it leaves the same
    # FP-theory sum undecided. An honest non-proof: never SUCCESSFUL, and identical on both routes.
    ("bmc", "arith_sym_sum_sign_refuted"): ("INCONCLUSIVE", "Unknown", GAP_ARITH_BMC),
    # `enum-eq/joined_option_eq.rs`: the CHC lane decides all 21, which is the point of the
    # file — the m3/chc-joined-option-eq campaign fixed the false proof and the false Genuine
    # certificate there. BMC proves every `_holds` but leaves the five REFUTATIONS undecided:
    # refuting `<Option<T> as PartialEq>::eq` needs the whole inlined comparison, and the solver
    # returns `UNKNOWN_REASON:UndecidedModel`. An honest non-proof, never SUCCESSFUL, identical
    # on both routes.
    ("bmc", "eqj_map_eq_none_refuted"): ("INCONCLUSIVE", "Unknown", GAP_ENUM_EQ_BMC),
    ("bmc", "eqj_map_eq_wrong_payload_refuted"): ("INCONCLUSIVE", "Unknown", GAP_ENUM_EQ_BMC),
    ("bmc", "eqj_and_then_eq_none_refuted"): ("INCONCLUSIVE", "Unknown", GAP_ENUM_EQ_BMC),
    ("bmc", "eqj_result_map_eq_wrong_refuted"): ("INCONCLUSIVE", "Unknown", GAP_ENUM_EQ_BMC),
    ("bmc", "eqj_map_f64_max_eq_wrong_refuted"): ("INCONCLUSIVE", "Unknown", GAP_ENUM_EQ_BMC),
}

# (lane, harness) -> (failing check, evidence). A known soundness defect: a SUCCESSFUL on a harness
# that must not verify, or a counterexample certified Genuine on one that holds. A match prints a
# DEFECT line and FAILS its case. The three recorded before the parity-1 repairs (BMC
# custom_dyn_holds, CHC rc_dyn_holds and arc_dyn_holds, all certified Genuine) are fixed; see
# docs/trust-lane-trustc-route.md.
KNOWN_DEFECTS: dict[tuple[str, str], tuple[str, str]] = {}

# (lane, harness) -> {route: required evidence line under the harness}, why. The two routes reach the
# SAME verdict for the SAME recorded approximation but report it differently, because Trust std and
# nightly std lower the construct differently. The verdict still has to agree and meet the table.
ROUTE_DIFFERENCES: dict[tuple[str, str], tuple[dict[str, str], str]] = {
    ("chc", "nonnull_len_should_panic_refuted"): (
        {"devcli": "[AY:CTREX_CAT:EncodingGap:signedness_fallback=1]", "trustc": "[AY:DEMOTION_REASONS:signedness_fallback=1]"},
        "The nonnull_slice_holds difference under should_panic: Trust std proves NonNull<[u8]>::len and demotes the proof "
        "(no panic, FAILED); nightly std gives an uncertified counterexample that V6 refuses. Both FAILED, fail closed.",
    ),
    ("chc", "nonnull_slice_holds"): (
        {"devcli": "[AY:CTREX_CAT:EncodingGap:signedness_fallback=1]", "trustc": "[AY:DEMOTION_REASONS:signedness_fallback=1]"},
        "Trust std: CHC proves NonNull<[u8]>::len and demotes the proof for signedness_fallback=1; nightly std: an uncertified "
        "counterexample for the same signedness_fallback=1. Both are FAILED and fail closed.",
    ),
    ("chc", "reduce_min_nz_pz_positive_unprovable"): (
        {"devcli": "[AY:CTREX_CAT:OverApproximation:chc_sound_havoc_drop=1]",
         "trustc": "[AY:CTREX_CAT:OverApproximation:chc_sound_havoc_drop=2]"},
        "Iterator::reduce over the direct intrinsic: the two routes run DIFFERENT fixtures "
        "(trust.rs spells `minimum_number_nsz_f32`, nightly.rs `minnumf32`) and the Trust spelling "
        "carries a fallback body `callee_body` refuses, so the Trust route declines one more call "
        "and drops one more havoc. Same verdict, same category KIND, same fail-closed direction; "
        "only the COUNT differs. Measured 2026-09-14 after the rebase onto main 086a91501, whose "
        "m3/chc-joined-option-eq campaign changed the inline fallback accounting "
        "(codegen_call_fn_inline.rs, codegen_call_virtual_inline/*, codegen_stmt_fallback.rs); "
        "the counts matched at 348e55554.",
    ),
}
DEFECTS_SEEN: list[str] = []

RESULTS: list[dict] = []
FAILURES = 0


def report(case: str, problems: list[str], detail: str) -> None:
    global FAILURES
    if problems:
        FAILURES += 1
        print(f"FAIL  {case:44} {detail}: {'; '.join(problems)}", flush=True)
    else:
        print(f"ok    {case:44} {detail}", flush=True)


def harness_lines(stdout: str) -> dict[str, list[str]]:
    """Every line printed under each `Checking harness` line, up to its verdict."""
    out: dict[str, list[str]] = {}
    current = None
    for line in stdout.splitlines():
        m = HARNESS_RE.match(line)
        if m:
            current = m.group(1)
            out.setdefault(current, [])
        elif current is not None:
            out[current].append(line)
            if VERDICT_RE.match(line):
                current = None
    return out


def harness_ctrex_categories(stdout: str) -> dict[str, list[str]]:
    """The `[AY:CTREX_CAT:...]` values printed under each `Checking harness` line."""
    out: dict[str, list[str]] = {}
    current = None
    for line in stdout.splitlines():
        m = HARNESS_RE.match(line)
        if m:
            current = m.group(1)
            out.setdefault(current, [])
        elif current is not None and line.startswith("[AY:CTREX_CAT:"):
            out[current].append(line[len("[AY:CTREX_CAT:"):].rstrip("]"))
    return out


def route_sanity(route: str, result: dict) -> list[str]:
    problems = []
    if result["panicked"]:
        problems.append(f"{route}: the compiler panicked")
    if route == "trustc" and result["route_markers"] != 1 and not result["errors"]:
        problems.append(f"trustc: {result['route_markers']} route markers")
    if route == "devcli" and result["route_markers"] != 0:
        problems.append("devcli: printed a trustc route marker")
    return problems


def duals(case: str, fixture: Path, lane_args: list[str], devcli_fixture: Path | None = None) -> None:
    if ONLY and not any(s in case for s in ONLY):
        return
    fixtures = {"trustc": fixture, "devcli": devcli_fixture or fixture}
    results = {route: run(case, route, fixtures[route], lane_args) for route in ("trustc", "devcli")}
    problems: list[str] = []
    lane = "chc" if "--ay-chc" in lane_args else "bmc"
    for route, result in results.items():
        should_panic = should_panic_harnesses(fixtures[route])
        problems += route_sanity(route, result)
        if not result["verdicts"]:
            problems.append(f"{route}: no verdicts (exit {result['exit']}, {result['errors'][:2]})")
        categories = harness_ctrex_categories(result["stdout"])
        for harness, verdict in result["verdicts"].items():
            cats = categories.get(harness, [])
            genuine = any(cat.startswith("Genuine") for cat in cats)
            defect = KNOWN_DEFECTS.get((lane, harness))
            if defect is not None:
                # A known soundness defect is reported AND fails the case: a run that still
                # contains one must never read "all cases as expected".
                DEFECTS_SEEN.append(f"{case} {route}: {harness} {verdict} {cats}: {defect[0]}: {defect[1]}")
                problems.append(f"{route}: {harness} is a KNOWN_DEFECT ({defect[0]})")
                continue
            if harness.endswith("_refuted") or harness.endswith("_unprovable") or harness.endswith("_vacuous"):
                if verdict == "SUCCESSFUL":
                    what = {
                        "_refuted": "a missed bug",
                        "_unprovable": "a false proof of a property the program may violate",
                        "_vacuous": "a clean green proof of a harness whose assumptions are contradictory: nothing was verified",
                    }["_" + harness.rsplit("_", 1)[1]]
                    problems.append(f"{route}: {harness} SUCCESSFUL: {what}")
                    continue
                if harness.endswith("_unprovable"):
                    # Any non-proof is honest here: the property can fail when the program runs,
                    # so a counterexample (certified or not) and INCONCLUSIVE are both allowed.
                    gap = KNOWN_GAPS.get((lane, harness))
                    if gap is not None and (verdict != gap[0] or not any(cat.startswith(gap[1]) for cat in cats)):
                        problems.append(f"{route}: {harness} {verdict} {cats}, KNOWN_GAPS says {gap[0]} {gap[1]}")
                    # A recorded route difference is a CLAIM about what each route prints, so it is
                    # checked here too; otherwise the entry would only silence the category
                    # comparison below without pinning anything.
                    difference = ROUTE_DIFFERENCES.get((lane, harness))
                    if difference is not None:
                        evidence = difference[0][route]
                        if evidence not in harness_lines(result["stdout"]).get(harness, []):
                            problems.append(f"{route}: {harness} lacks {evidence} (ROUTE_DIFFERENCES)")
                    continue
                # V4: the assumptions are contradictory, so every check under them is
                # unreachable and the run proved nothing. Both lanes must SAY so — the
                # CHC lane used to report SUCCESSFUL + PROOF_QUALIFIERS:clean here
                # (parity-1 third review, finding 8.6), fail-open on the project's own
                # `--allow-vacuous` default.
                expected = ("VACUOUS", "") if harness.endswith("_vacuous") else ("FAILED", "")
            elif harness.endswith("_holds"):
                if genuine and harness not in should_panic and (lane, harness) not in KNOWN_GAPS:
                    problems.append(f"{route}: {harness} refuted by a counterexample certified Genuine: a false bug report")
                    continue
                expected = ("SUCCESSFUL", "")
            else:
                problems.append(
                    f"{route}: harness {harness} is none of _holds / _refuted / _unprovable / _vacuous"
                )
                continue
            gap = KNOWN_GAPS.get((lane, harness))
            want_verdict, want_category = (gap[0], gap[1]) if gap else expected
            difference = ROUTE_DIFFERENCES.get((lane, harness))
            if verdict != want_verdict:
                source = "KNOWN_GAPS" if gap else "the dual"
                problems.append(f"{route}: {harness} {verdict} {cats}, {source} says {want_verdict}")
            elif difference is not None:
                evidence = difference[0][route]
                if evidence not in harness_lines(result["stdout"]).get(harness, []):
                    problems.append(f"{route}: {harness} lacks {evidence} (ROUTE_DIFFERENCES)")
            elif want_category and not any(cat.startswith(want_category) for cat in cats):
                problems.append(f"{route}: {harness} categories {cats}, KNOWN_GAPS says {want_category}")
        want_exit = 0 if all(v == "SUCCESSFUL" for v in result["verdicts"].values()) else 1
        if result["verdicts"] and result["exit"] != want_exit:
            problems.append(f"{route}: exit {result['exit']}, expected {want_exit}")
    if results["trustc"]["verdicts"] != results["devcli"]["verdicts"]:
        problems.append("the routes disagree harness by harness")
    if sorted(results["trustc"]["harnesses"]) != sorted(results["devcli"]["harnesses"]):
        problems.append("the routes report different harness names")
    # The same verdict for a different reason is still a route difference: a Genuine
    # counterexample on one route and an uncertified one on the other means one engine
    # fell back where the other did not.
    trust_categories = harness_ctrex_categories(results["trustc"]["stdout"])
    devcli_categories = harness_ctrex_categories(results["devcli"]["stdout"])
    for harness in sorted(set(trust_categories) | set(devcli_categories)):
        if (lane, harness) in ROUTE_DIFFERENCES:
            continue
        if trust_categories.get(harness) != devcli_categories.get(harness):
            problems.append(
                f"{harness}: counterexample categories {trust_categories.get(harness)} (trustc) vs "
                f"{devcli_categories.get(harness)} (devcli)"
            )
    n = len(results["trustc"]["verdicts"])
    report(case, problems, f"{n} harnesses")
    RESULTS.append({"case": case, "fixture": {route: str(path.relative_to(ROOT)) for route, path in fixtures.items()},
                    "args": lane_args, "problems": problems,
                    **{route: {k: v for k, v in r.items() if k != "stdout"} for route, r in results.items()}})


def selection(case: str, args: list[str], want_harnesses: list[str] | None, want_error: str | None) -> None:
    if ONLY and not any(s in case for s in ONLY):
        return
    fixture = FIXTURES / "harness-names/modules.rs"
    results = {route: run(case, route, fixture, args) for route in ("trustc", "devcli")}
    problems: list[str] = []
    for route, result in results.items():
        problems += route_sanity(route, result)
        if want_error is None:
            if sorted(result["harnesses"]) != sorted(want_harnesses or []):
                problems.append(f"{route}: harnesses {sorted(result['harnesses'])}, expected {sorted(want_harnesses or [])}")
            if result["exit"] != 0:
                problems.append(f"{route}: exit {result['exit']}")
            if set(result["verdicts"].values()) - {"SUCCESSFUL"}:
                problems.append(f"{route}: verdicts {result['verdicts']}")
        else:
            if result["exit"] == 0:
                problems.append(f"{route}: expected a nonzero exit")
            if result["harnesses"]:
                problems.append(f"{route}: checked {result['harnesses']}")
            if want_error not in result["stdout"]:
                problems.append(f"{route}: no '{want_error}'")
    if sorted(results["trustc"]["harnesses"]) != sorted(results["devcli"]["harnesses"]):
        problems.append("the routes selected different harnesses")
    report(case, problems, " ".join(args) or "(no filter)")
    RESULTS.append({"case": case, "fixture": str(fixture.relative_to(ROOT)), "args": args, "problems": problems,
                    **{route: {k: v for k, v in r.items() if k != "stdout"} for route, r in results.items()}})


def main() -> None:
    for path, what in ((TRUSTC, "trustc"), (DRIVER, "trust-mc-driver"), (AY_BIN, "ay CLI"),
                       (DEVCLI / "bin/trust-mc-driver", "DevCli bundle driver"), (KEY / "KEY.json", "KEY.json"),
                       (DYLIB, "backend dylib")):
        if not path.exists():
            die(f"no {what} at {path}")
    if str(OUT.resolve()).startswith(("/tmp/", "/private/tmp/")):
        die("TRUST_MC_DUALS_OUT must not be under /tmp")
    OUT.mkdir(parents=True, exist_ok=True)
    print(f"trust-lane-route-duals: trustc={TRUSTC} key={KEY} devcli={DEVCLI} out={OUT}", flush=True)

    dual_fixtures = [
        fixture
        for directory in ("casts", "coercion", "enum-eq", "float-intrinsics", "should-panic", "vacuity")
        for fixture in sorted((FIXTURES / directory).glob("*.rs"))
    ]
    direct = FIXTURES / "float-intrinsics-direct"
    seen: dict[str, Path] = {}
    for fixture in dual_fixtures + [direct / "trust.rs"]:
        for name in HARNESS_FN_RE.findall(fixture.read_text()):
            if name in seen:
                die(f"harness {name} is defined in both {seen[name]} and {fixture}; the tables need unique names")
            seen[name] = fixture
    if sorted(HARNESS_FN_RE.findall((direct / "trust.rs").read_text())) != sorted(
        HARNESS_FN_RE.findall((direct / "nightly.rs").read_text())
    ):
        die("float-intrinsics-direct/trust.rs and nightly.rs must define the same harnesses")

    for fixture in dual_fixtures:
        stem = f"{fixture.parent.name}-{fixture.stem}"
        duals(f"bmc-{stem}", fixture, [])
        duals(f"chc-{stem}", fixture, ["--ay-chc"])
    duals("bmc-float-intrinsics-direct", direct / "trust.rs", [], direct / "nightly.rs")
    duals("chc-float-intrinsics-direct", direct / "trust.rs", ["--ay-chc"], direct / "nightly.rs")

    everything = ["top", "first::check", "second::check", "second::inner::check_inner"]
    selection("names-no-filter", [], everything, None)
    selection("names-substring", ["--harness", "check"], ["first::check", "second::check", "second::inner::check_inner"], None)
    selection("names-exact-qualified", ["--harness", "first::check", "--exact"], ["first::check"], None)
    selection("names-exact-nested", ["--harness", "second::inner::check_inner", "--exact"], ["second::inner::check_inner"], None)
    selection("names-exact-top", ["--harness", "top", "--exact"], ["top"], None)
    selection("names-exact-unqualified-refused", ["--harness", "check", "--exact"], None,
              "Failed to match the following harness(es)")
    selection("names-exact-crate-qualified-refused", ["--harness", "modules::top", "--exact"], None,
              "Failed to match the following harness(es)")

    for line in DEFECTS_SEEN:
        print(f"DEFECT {line}")
    (OUT / "results.json").write_text(json.dumps({"cases": RESULTS, "known_defects_seen": DEFECTS_SEEN}, indent=1))
    if FAILURES:
        print(f"trust-lane-route-duals: {FAILURES} case(s) not as expected")
        sys.exit(1)
    print("trust-lane-route-duals: all cases as expected")


if __name__ == "__main__":
    main()
