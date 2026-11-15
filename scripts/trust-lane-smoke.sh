#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>

# T1 step S6, first green: canonical trustc loads librustc_codegen_trust_mc.dylib
# and trust-mc-driver decides the Kani pair from the VCs the dylib writes, in the
# default BMC lane and the --ay-chc lane. Then the route's refusals (including
# an engine flag smuggled through RUSTFLAGS, which would otherwise turn a failing
# harness into SUCCESSFUL), and the vacuity rule on a harness with nothing to check.
#
# T1 step S7 adds cargo units: the pass/fail pair of tests/trust-lane/cargo-pair
# (a build script and a proc-macro dependency each) through the driver's
# `cargo trust-mc` identity on the Trustc route, in both lanes. Every cargo case
# also reads cargo's own -v log: each compile ran trustc itself (no wrapper),
# build scripts and proc-macros got the host posture and neither the backend, the
# KEY sysroot nor engine arguments, the package loaded the backend against the KEY
# sysroot with a pct1 engine-argument group, and the target directory is the
# route's backend- and KEY-keyed namespace. Then a hostile cargo configuration
# (rustc wrappers that would smuggle --no-unwinding-checks into the target units,
# and a [host.<triple>] table), the cargo launcher's refusals (wrapper variables,
# RUSTFLAGS, an engine knob in the environment, an engine knob in a cargo [env]
# table, a CARGO_HOST_* engine flag), a KEY whose library is replaced in place
# between two runs on one target dir (must recompile or refuse, never a verdict
# from the previous library's artifacts), and the engine itself refusing a knob
# set in its own environment when trustc loads the backend directly.
#
# Prints one line per case and exits 1 when any outcome is not the expected one.
# Every run's stdout, stderr and exit code stay under $TRUST_MC_SMOKE_OUT/<case>/.
#
# Inputs (environment; defaults in brackets):
#   TRUST_MC_SMOKE_TRUSTC     canonical trustc      [bin/trustc of the seal scripts/resolve-trust-tool.sh
#                             resolves: TRUST_MC_TRUST_TOOLCHAIN when set, else rust-toolchain.toml]
#   TRUST_MC_SMOKE_REFUSED_TRUSTC  trustc from another seal [the highest-numbered other ready seal
#                             under TRUST_MC_SMOKE_STORE whose driver sha256 differs: PROVENANCE's,
#                             else the sha256 of its one librustc_driver, as for this seal;
#                             when there is none, that case prints a SKIPPED line]
#   TRUST_MC_SMOKE_STORE      seal store searched for that other seal; when set it must be an
#                             existing directory [~/Library/Application Support/aterm/pkg/store/trust]
#   TRUST_MC_SMOKE_REQUIRE_OTHER_SEAL  1: no other seal is a failure, not a SKIPPED line [0]
#   TRUST_MC_SMOKE_KEY        KEY directory         [target/trust-mc/keyed/driver-<driver sha[:16]>]
#   TRUST_MC_SMOKE_DRIVER     trust-mc-driver       [target/debug/trust-mc-driver]
#   TRUST_MC_SMOKE_AY_BIN     pinned ay CLI         [scripts/build-pinned-ay-cli.sh --print-path]
#   TRUST_MC_SMOKE_OUT        run directory         [~/Library/Caches/trust-mc-t1/trust-lane-smoke]
#   TRUST_MC_SMOKE_TIMEOUT    seconds per run       [900]
# The run directory must not sit under /tmp: trustc refuses world-writable
# directories and so does the route's preflight.

set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." >/dev/null 2>&1 && pwd)"
die() { printf 'trust-lane-smoke: error: %s\n' "$*" >&2; exit 2; }

DEFAULT_STORE="$HOME/Library/Application Support/aterm/pkg/store/trust"
# A named store that is not a directory is a mistake, never "no other seal".
if [[ -n "${TRUST_MC_SMOKE_STORE+set}" ]]; then
    [[ -d "$TRUST_MC_SMOKE_STORE" ]] \
        || die "TRUST_MC_SMOKE_STORE is not an existing directory: '$TRUST_MC_SMOKE_STORE'"
    STORE="$TRUST_MC_SMOKE_STORE"
else
    STORE="$DEFAULT_STORE"
fi
case "${TRUST_MC_SMOKE_REQUIRE_OTHER_SEAL:-0}" in
    0|1) REQUIRE_OTHER_SEAL="${TRUST_MC_SMOKE_REQUIRE_OTHER_SEAL:-0}" ;;
    *) die "TRUST_MC_SMOKE_REQUIRE_OTHER_SEAL must be 0 or 1, not '$TRUST_MC_SMOKE_REQUIRE_OTHER_SEAL'" ;;
esac
if [[ -n "${TRUST_MC_SMOKE_TRUSTC-}" ]]; then
    TRUSTC="$TRUST_MC_SMOKE_TRUSTC"
else
    # The seal's own path, never a link: the route refuses a trustc outside the
    # sysroot it reports, and the marker names the canonical path.
    TRUST_SYSROOT="$("$ROOT/scripts/resolve-trust-tool.sh" sysroot)" \
        || die "cannot resolve the Trust toolchain (scripts/resolve-trust-tool.sh sysroot)"
    TRUSTC="$(cd "$TRUST_SYSROOT" && pwd -P)/bin/trustc"
fi
DRIVER="${TRUST_MC_SMOKE_DRIVER:-$ROOT/target/debug/trust-mc-driver}"
# The CLI built at the Cargo.toml AY pin (an unkeyed cache goes stale on a bump).
if [[ -n "${TRUST_MC_SMOKE_AY_BIN-}" ]]; then
    AY_BIN="$TRUST_MC_SMOKE_AY_BIN"
else
    AY_BIN="$("$ROOT/scripts/build-pinned-ay-cli.sh" --print-path)" \
        || die "cannot derive the pinned ay CLI path (scripts/build-pinned-ay-cli.sh --print-path)"
fi
OUT="${TRUST_MC_SMOKE_OUT:-$HOME/Library/Caches/trust-mc-t1/trust-lane-smoke}"
TIMEOUT="${TRUST_MC_SMOKE_TIMEOUT:-900}"
LANE_FIXTURES="$ROOT/tests/trust-lane"
FIXTURES="$LANE_FIXTURES/kani-pair"

[[ -x "$TRUSTC" ]] || die "no trustc at $TRUSTC"
[[ -x "$DRIVER" ]] || die "no trust-mc-driver at $DRIVER"
[[ -x "$AY_BIN" ]] || die "no ay CLI at $AY_BIN"
case "$OUT" in /tmp/*|/private/tmp/*) die "TRUST_MC_SMOKE_OUT must not be under /tmp";; esac

SYSROOT="$(dirname "$(dirname "$TRUSTC")")"
DRIVER_LIB="$(cd "$SYSROOT/lib" && ls librustc_driver-* 2>/dev/null)"
[[ -n "$DRIVER_LIB" && "$DRIVER_LIB" != *$'\n'* ]] || die "$SYSROOT/lib must ship exactly one librustc_driver-*"
DRIVER_SHA="$(sed -n 's/^artifact_driver_sha256=//p' "$SYSROOT/PROVENANCE" 2>/dev/null)"
[[ -n "$DRIVER_SHA" ]] || DRIVER_SHA="$(shasum -a 256 "$SYSROOT/lib/$DRIVER_LIB" | cut -d' ' -f1)"
KEY="${TRUST_MC_SMOKE_KEY:-$ROOT/target/trust-mc/keyed/driver-${DRIVER_SHA:0:16}}"

# The other seal: the highest-numbered ready seal in the store that is not this
# trustc's and whose driver sha256 differs (two seals with one driver sha256 are
# one build, and the route would rightly accept it). A seal without PROVENANCE is
# identified by the sha256 of its one librustc_driver, exactly as this seal and
# the route identify theirs. Seals come and go with promotions, so none is named
# here.
REFUSED_TRUSTC="${TRUST_MC_SMOKE_REFUSED_TRUSTC-}"
REFUSED_SKIP=""
if [[ -z "$REFUSED_TRUSTC" ]]; then
    OWN_SEAL="$(cd "$SYSROOT" && pwd -P)"
    while IFS= read -r build; do
        seal="$STORE/$build"
        [[ -f "$STORE/$build.ready" && -d "$seal" && ! -L "$seal" && -x "$seal/bin/trustc" ]] || continue
        [[ "$(cd "$seal" && pwd -P)" != "$OWN_SEAL" ]] || continue
        other_sha="$(sed -n 's/^artifact_driver_sha256=//p' "$seal/PROVENANCE" 2>/dev/null)"
        if [[ -z "$other_sha" ]]; then
            other_lib="$(cd "$seal/lib" 2>/dev/null && ls librustc_driver-* 2>/dev/null)"
            [[ -n "$other_lib" && "$other_lib" != *$'\n'* ]] || continue
            other_sha="$(shasum -a 256 "$seal/lib/$other_lib" | cut -d' ' -f1)"
        fi
        [[ -n "$other_sha" && "$other_sha" != "$DRIVER_SHA" ]] || continue
        REFUSED_TRUSTC="$seal/bin/trustc"
    done < <(ls "$STORE" 2>/dev/null | grep -E '^[0-9]+$' | sort -n)
    if [[ -z "$REFUSED_TRUSTC" && ! -d "$STORE" ]]; then
        REFUSED_SKIP="no seal store at $STORE"
    elif [[ -z "$REFUSED_TRUSTC" ]]; then
        REFUSED_SKIP="no other ready numbered seal with another driver sha256 under $STORE"
    fi
fi
[[ -d "$KEY" ]] || die "no KEY directory at $KEY (run build-trust-mc build-keyed --backend first)"
[[ -f "$KEY/KEY.json" ]] || die "no KEY.json in $KEY (run build-trust-mc build-keyed --backend first)"
# The driver canonicalizes the KEY and the dylib, and its marker and recorded argv
# name those paths (a `target -> target.noindex` link is common here), so a KEY
# reached through a link would fail every argv check below on a run that is right.
KEY="$(cd "$KEY" && pwd -P)" || die "cannot canonicalize the KEY directory $KEY"
DYLIB="$KEY/codegen-backends/librustc_codegen_trust_mc.dylib"
[[ -f "$DYLIB" ]] || die "no backend dylib at $DYLIB"
# The marker pct1-escapes its values; the seal paths carry only spaces to escape.
MARKER_TRUSTC="trustc=${TRUSTC// /%20}"

mkdir -p "$OUT" || die "cannot create $OUT"
OUT="$(cd "$OUT" && pwd -P)"

# The runs inherit nothing that could change what is compiled or solved: every
# TRUST_MC_* and AY_* variable (the route refuses engine knobs), and the rustc
# and cargo selectors. A case that needs RUSTFLAGS sets CASE_RUSTFLAGS for itself.
while IFS= read -r name; do
    unset "$name"
done < <(env | sed -n 's/^\(\(TRUST_MC_\|AY_\)[A-Za-z0-9_]*\)=.*/\1/p')
unset RUSTFLAGS RUSTC RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER CARGO_BUILD_RUSTC_WRAPPER \
    CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER RUSTUP_TOOLCHAIN CARGO_TARGET_DIR CARGO_BUILD_TARGET_DIR \
    CARGO_ENCODED_RUSTFLAGS CARGO_BUILD_RUSTFLAGS

FAILURES=0
SKIPPED=()

# run <case> <sysroot KEY> -- <driver args...>: runs the driver from the case
# directory with its own target dir, recording stdout, stderr and exit. A
# non-empty CASE_RUSTFLAGS becomes that run's RUSTFLAGS.
run() {
    local name="$1" key="$2"; shift 3
    local dir="$OUT/$name"
    local vars=(TRUST_MC_SYSROOT="$key" TRUST_MC_AY_BIN="$AY_BIN")
    [[ -z "${CASE_RUSTFLAGS-}" ]] || vars+=(RUSTFLAGS="$CASE_RUSTFLAGS")
    rm -rf "$dir"; mkdir -p "$dir/target"
    ( cd "$dir" && env "${vars[@]}" \
        perl -e 'alarm shift; exec @ARGV or die "exec: $!"' "$TIMEOUT" \
        "$DRIVER" "$@" --target-dir "$dir/target" \
        </dev/null >"$dir/stdout.txt" 2>"$dir/stderr.txt" )
    echo $? >"$dir/exit.txt"
}

count() { grep -c -- "$1" "$2" 2>/dev/null; true; }

# report <case> <problems...>: one line per case; no problems means as expected.
report() {
    local name="$1"; shift
    local dir="$OUT/$name" verdict
    verdict="$(grep -m1 -o 'VERIFICATION:- .*' "$dir/stdout.txt" 2>/dev/null)"
    if [[ $# -eq 0 ]]; then
        printf 'ok    %-26s exit=%s %s\n' "$name" "$(cat "$dir/exit.txt")" "${verdict:-no-verdict}"
    else
        FAILURES=$((FAILURES + 1))
        printf 'FAIL  %-26s exit=%s %s: %s\n' "$name" "$(cat "$dir/exit.txt")" \
            "${verdict:-no-verdict}" "$(IFS=';'; echo "$*")"
    fi
}

# The checks every run that reached the compile must pass.
route_problems() {
    local dir="$1" stdout="$1/stdout.txt" markers argv
    markers="$(grep -c '^\[AY:COMPILER_ROUTE route=trustc ' "$stdout")"
    [[ "$markers" == 1 ]] || echo "route markers=$markers"
    if ! grep '^\[AY:COMPILER_ROUTE route=trustc ' "$stdout" | grep -qF -- "$MARKER_TRUSTC "; then
        echo "marker does not name $TRUSTC"
    fi
    if ! grep '^\[AY:COMPILER_ROUTE route=trustc ' "$stdout" | grep -qF -- " driver=$DRIVER_LIB "; then
        echo "marker does not name $DRIVER_LIB"
    fi
    [[ "$(count '\[AY:SOLVER_PIN_MISMATCH' "$stdout")" == 0 ]] || echo "unpinned-solver marker"
    argv="$(grep '^\[trust_mc\] Running: ' "$stdout")"
    grep -qF -- "-Zcodegen-backend=$DYLIB" <<<"$argv" || echo "no recorded trustc compile argv loading $DYLIB"
    ! grep -q 'trust-mc-compiler' <<<"$argv" || echo "recorded argv names trust-mc-compiler"
    if [[ -n "${CASE_RUSTFLAGS-}" ]]; then
        grep -qF -- "$CASE_RUSTFLAGS" <<<"$argv" || echo "RUSTFLAGS '$CASE_RUSTFLAGS' not in the recorded argv"
    fi
    [[ -n "$(find "$dir/target" -name '*.vc.json' -print -quit)" ]] || echo "no *.vc.json in the target dir"
}

# lane <case> <fixture> <expected exit> <expected verdict> [extra driver args...]
# <fixture> is a name in tests/trust-lane/kani-pair, or a path with a '/' read
# relative to tests/trust-lane (so the kani-std cases name their own directory).
# A FAILED lane requires a FAILURE check whose description matches FAILED_CHECK
# (default: the kani-pair assertion "sum reaches 150"); a SUCCESSFUL lane
# requires a SUCCESS check whose description contains SUCCESS_CHECK (default:
# the kani-pair assertion "assertion failed: a + b < 200").
lane() {
    local name="$1" fixture="$2" want_exit="$3" want="$4"; shift 4
    local dir="$OUT/$name" stdout="$OUT/$name/stdout.txt" problems=() path
    case "$fixture" in */*) path="$LANE_FIXTURES/$fixture" ;; *) path="$FIXTURES/$fixture" ;; esac
    run "$name" "$KEY" -- "$path" --compiler-route trustc --trustc "$TRUSTC" \
        --backend-dylib "$DYLIB" --verbose --keep-temps "$@"
    [[ "$(cat "$dir/exit.txt")" == "$want_exit" ]] || problems+=("expected exit $want_exit")
    local verdicts
    verdicts="$(grep -o 'VERIFICATION:- .*' "$stdout" | sort -u)"
    [[ "$verdicts" == "VERIFICATION:- $want" ]] || problems+=("expected only 'VERIFICATION:- $want'")
    [[ "$(count UNVALIDATED "$stdout")" == 0 ]] || problems+=("UNVALIDATED")
    # The checks must be the fixtures' own assertions, in both lanes. The Kani
    # std overrides turn `assert!` into `kani::assert`, which carries the message;
    # when they are bypassed (a std prelude that shadows them) BMC reports the
    # assertion as a generic panic and the CHC lane loses the property entirely,
    # while the verdict alone still looks right.
    case "$want" in
        SUCCESSFUL)
            grep -A1 'Status: SUCCESS' "$stdout" | grep -F -- 'Description: ' \
                | grep -qF -- "${SUCCESS_CHECK:-assertion failed: a + b < 200}" \
                || problems+=("no SUCCESS check '${SUCCESS_CHECK:-assertion failed: a + b < 200}'")
            ;;
        FAILED)
            grep -A1 'Status: FAILURE' "$stdout" | grep -q "Description: .*${FAILED_CHECK:-sum reaches 150}" \
                || problems+=("the failed check is not '${FAILED_CHECK:-sum reaches 150}'")
            ;;
    esac
    if [[ " $* " == *" --ay-chc "* ]]; then
        grep -q 'Detected HORN logic' "$stdout" || problems+=("no HORN logic line")
        if [[ "$want" == FAILED ]]; then
            grep -q '^\[AY:CTREX_CAT:Genuine\]' "$stdout" || problems+=("CHC failure is not a Genuine counterexample")
        fi
    fi
    while IFS= read -r p; do [[ -n "$p" ]] && problems+=("$p"); done < <(route_problems "$dir")
    report "$name" ${problems[@]+"${problems[@]}"}
}

# refusal <case> <sysroot KEY> <driver args...>: must exit nonzero before any verdict.
# REFUSAL_FIXTURE picks the fixture (default pass.rs); REFUSAL_WANT is a string the
# refusal must contain besides 'compiler route trustc refused'.
refusal() {
    local name="$1" key="$2"; shift 2
    local stdout="$OUT/$name/stdout.txt" problems=()
    run "$name" "$key" -- "$FIXTURES/${REFUSAL_FIXTURE:-pass.rs}" --compiler-route trustc "$@"
    [[ "$(cat "$OUT/$name/exit.txt")" != 0 ]] || problems+=("expected a nonzero exit")
    [[ "$(count 'VERIFICATION:-' "$stdout")" == 0 ]] || problems+=("printed a VERIFICATION line")
    [[ "$(count '^\[AY:COMPILER_ROUTE' "$stdout")" == 0 ]] || problems+=("printed a route marker")
    grep -q 'compiler route trustc refused' "$stdout" || problems+=("no 'compiler route trustc refused'")
    if [[ -n "${REFUSAL_WANT-}" ]]; then
        grep -qF -- "$REFUSAL_WANT" "$stdout" || problems+=("the refusal does not say '$REFUSAL_WANT'")
    fi
    report "$name" ${problems[@]+"${problems[@]}"}
}

echo "trust-lane-smoke: trustc=$TRUSTC driver=$DRIVER_LIB key=$KEY out=$OUT"
echo "trust-lane-smoke: other-seal trustc=${REFUSED_TRUSTC:-none}"

lane bmc-pass pass.rs 0 SUCCESSFUL
lane bmc-fail fail.rs 1 FAILED
lane chc-pass pass.rs 0 SUCCESSFUL --ay-chc
lane chc-fail fail.rs 1 FAILED --ay-chc

# T1 S10, the M4 Vec case: a harness that reaches into std. It is not a
# parity-vs-smoke discriminator (Vec's methods are generic, so their MIR ships in
# any std; see the fixture's own header for what was measured), so what these two
# cases hold is that std library code is modeled through the Trustc route and that
# both lanes agree with the frozen DevCli route on this file.
SUCCESS_CHECK='the vector holds both pushes' \
    lane bmc-vec-push-len kani-std/vec_push_len.rs 0 SUCCESSFUL
SUCCESS_CHECK='the vector holds both pushes' \
    lane chc-vec-push-len kani-std/vec_push_len.rs 0 SUCCESSFUL --ay-chc

# The engine-flag fixture: its loop outruns #[kani::unwind(3)], so the unwinding
# assertion fails. With --no-unwinding-checks the run would report SUCCESSFUL.
FAILED_CHECK='unwinding assertion loop 0' lane bmc-unwind-bound unwind_bound.rs 1 FAILED
# RUSTFLAGS that leave the route's options alone (a compile-flags header) are
# forwarded, and the verdict and its check are unchanged.
CASE_RUSTFLAGS='--cfg trust_mc_smoke_forwarded' lane bmc-fail-forwarded-rustflags fail.rs 1 FAILED
# That engine flag smuggled through RUSTFLAGS -Cllvm-args, attached and behind an
# argfile rustc would expand: refused before any compile.
CASE_RUSTFLAGS='-Cllvm-args=--no-unwinding-checks' REFUSAL_FIXTURE=unwind_bound.rs \
    REFUSAL_WANT='RUSTFLAGS token(s) ["-Cllvm-args=--no-unwinding-checks"]' \
    refusal refuse-rustflags-engine-flag "$KEY" --trustc "$TRUSTC" --backend-dylib "$DYLIB"
printf '%s\n' '-Cllvm-args=--no-unwinding-checks' >"$OUT/engine-flag.args"
CASE_RUSTFLAGS="@$OUT/engine-flag.args" REFUSAL_FIXTURE=unwind_bound.rs \
    REFUSAL_WANT="RUSTFLAGS token(s) [\"@$OUT/engine-flag.args\"]" \
    refusal refuse-rustflags-argfile "$KEY" --trustc "$TRUSTC" --backend-dylib "$DYLIB"

# ---------------------------------------------------------------------------
# The engine's own refusal of a knob in its environment. The driver keeps its
# environment clean, but a cargo [env] table or a wrapper can set a knob on the
# rustc process itself; the hosted backend refuses in init, whatever set it.
# trustc is run directly here with the flags the driver recorded for bmc-pass
# (the driver would refuse the knob before any compile): the control run must
# compile and write kani-metadata.json, the knob run must refuse and write none.

DRIVER_VERSION="$("$DRIVER" --version 2>/dev/null | awk 'NR==1 {print $2}')"
[[ -n "$DRIVER_VERSION" ]] || die "$DRIVER --version reports no version"
engine_direct() {
    local name="$1" knob="$2"
    local dir="$OUT/$name"
    rm -rf "$dir"; mkdir -p "$dir"
    local vars=(RUSTC_BOOTSTRAP=1 RUST_MIN_STACK=16777216)
    [[ -z "$knob" ]] || vars+=("$knob")
    ( cd "$dir" && env "${vars[@]}" \
        perl -e 'alarm shift; exec @ARGV or die "exec: $!"' "$TIMEOUT" \
        "$TRUSTC" \
        "-Cllvm-args=--trust-mc-engine-args=pct1:4 --check-version=$DRIVER_VERSION --log-level=info --assertion-reach-checks --reachability=harnesses" \
        -C overflow-checks=on -Z unstable-options -Z trim-diagnostic-paths=no \
        -Z human_readable_cgu_names -Z always-encode-mir --cfg=kani --cfg=trust_mc \
        -Z 'crate-attr=feature(register_tool)' -Z 'crate-attr=register_tool(kanitool)' \
        -Z 'crate-attr=register_tool(trust_mctool)' --sysroot "$KEY" -L "$KEY/lib" \
        --extern kani --extern "noprelude:std=$KEY/lib/libstd.rlib" -C panic=abort \
        -C symbol-mangling-version=v0 -Z panic_abort_tests=yes \
        -Z mir-enable-passes=-RemoveStorageMarkers -Z inline-mir=no --check-cfg='cfg(kani)' \
        -Clinker=echo "-Zcodegen-backend=$DYLIB" -Ztrust-verify=off "$FIXTURES/pass.rs" \
        --out-dir "$dir" --crate-name pass --crate-type lib \
        </dev/null >"$dir/stdout.txt" 2>"$dir/stderr.txt" )
    echo $? >"$dir/exit.txt"
}
engine_direct engine-direct-control ""
problems=()
[[ "$(cat "$OUT/engine-direct-control/exit.txt")" == 0 ]] || problems+=("expected exit 0")
[[ -n "$(find "$OUT/engine-direct-control" -name '*kani-metadata.json' -print -quit)" ]] \
    || problems+=("the control compile wrote no kani-metadata.json")
report engine-direct-control ${problems[@]+"${problems[@]}"}
engine_direct engine-direct-refuses-knob TRUST_MC_NO_LOOP_RULE=1
problems=()
[[ "$(cat "$OUT/engine-direct-refuses-knob/exit.txt")" != 0 ]] || problems+=("expected a nonzero exit")
grep -q 'engine environment knob(s) TRUST_MC_NO_LOOP_RULE set' "$OUT/engine-direct-refuses-knob/stderr.txt" \
    || problems+=("no refusal naming TRUST_MC_NO_LOOP_RULE")
[[ -z "$(find "$OUT/engine-direct-refuses-knob" -name '*kani-metadata.json' -print -quit)" ]] \
    || problems+=("the refused compile wrote kani-metadata.json")
report engine-direct-refuses-knob ${problems[@]+"${problems[@]}"}

# ---------------------------------------------------------------------------
# Cargo units (S7).

CARGO_FIXTURES="$ROOT/tests/trust-lane/cargo-pair"
HOST_TRIPLE="$("$TRUSTC" -vV | sed -n 's/^host: //p')"
[[ -n "$HOST_TRIPLE" ]] || die "$TRUSTC -vV reports no host triple"
COMMIT12="$("$TRUSTC" -vV | sed -n 's/^commit-hash: //p' | cut -c1-12)"
[[ ${#COMMIT12} == 12 ]] || die "$TRUSTC -vV reports no commit-hash"
BACKEND_SHA="$(shasum -a 256 "$DYLIB" | cut -d' ' -f1)"
# KEY and DYLIB are canonical (above); cargo's -v log shows those paths.
KEY_CANON="$KEY"
DYLIB_CANON="$DYLIB"
# The namespace ends in the KEY's content identity (sha256 over KEY.json and the
# library fingerprint), which only the driver computes; the prefix is checked
# exactly and the suffix for shape.
NAMESPACE_PREFIX="kani-trustc-$COMMIT12-${BACKEND_SHA:0:12}-"

# cargo_run <case> <pass|fail> -- <driver args...>: copies the cargo pair into the
# case directory (outside this checkout, whose .cargo/config.toml names a rustc
# wrapper: cargo reads configuration from the directory it runs in and every
# ancestor) and runs the driver in its `cargo trust-mc` identity from the package.
# CASE_RUSTFLAGS becomes RUSTFLAGS, CASE_ENV is one more NAME=value for the run,
# CASE_WRAPPER_ENV names one rustc-wrapper variable to set to the injector,
# CASE_CARGO_CONFIG is written as the package's .cargo/config.toml, and CASE_KEY
# is another KEY directory to compile against (default: $KEY).
cargo_run() {
    local name="$1" half="$2"; shift 3
    local dir="$OUT/$name"
    local vars=(TRUST_MC_SYSROOT="${CASE_KEY:-$KEY}" TRUST_MC_AY_BIN="$AY_BIN")
    [[ -z "${CASE_RUSTFLAGS-}" ]] || vars+=(RUSTFLAGS="$CASE_RUSTFLAGS")
    [[ -z "${CASE_ENV-}" ]] || vars+=("$CASE_ENV")
    [[ -z "${CASE_WRAPPER_ENV-}" ]] || vars+=("$CASE_WRAPPER_ENV=$INJECTOR")
    rm -rf "$dir"; mkdir -p "$dir/target" "$dir/ws"
    cp -R "$CARGO_FIXTURES/pair-macros" "$CARGO_FIXTURES/$half" "$dir/ws/"
    if [[ -n "${CASE_CARGO_CONFIG-}" ]]; then
        mkdir -p "$dir/ws/$half/.cargo"
        printf '%s\n' "$CASE_CARGO_CONFIG" >"$dir/ws/$half/.cargo/config.toml"
    fi
    ( cd "$dir/ws/$half" && env "${vars[@]}" INJECTOR_LOG="$dir/wrapper.log" \
        perl -e 'alarm shift; exec @ARGV or die "exec: $!"' "$TIMEOUT" \
        "$DRIVER" trust-mc "$@" --target-dir "$dir/target" \
        </dev/null >"$dir/stdout.txt" 2>"$dir/stderr.txt" )
    echo $? >"$dir/exit.txt"
}

# cargo_rerun <case> <pass|fail> -- <driver args...>: runs the driver again in an
# existing case directory, sources and target dir untouched (so cargo's own
# fingerprints decide what is fresh), recording stdout2/stderr2/exit2.
cargo_rerun() {
    local name="$1" half="$2"; shift 3
    local dir="$OUT/$name"
    local vars=(TRUST_MC_SYSROOT="${CASE_KEY:-$KEY}" TRUST_MC_AY_BIN="$AY_BIN")
    ( cd "$dir/ws/$half" && env "${vars[@]}" \
        perl -e 'alarm shift; exec @ARGV or die "exec: $!"' "$TIMEOUT" \
        "$DRIVER" trust-mc "$@" --target-dir "$dir/target" \
        </dev/null >"$dir/stdout2.txt" 2>"$dir/stderr2.txt" )
    echo $? >"$dir/exit2.txt"
}

# A rustc wrapper that logs every call and appends --no-unwinding-checks to any
# unit that selects the engine (a codegen backend, or DevCli's --kani-compiler).
# Honored, it turns the unwind-bound harness from FAILED into SUCCESSFUL.
INJECTOR="$OUT/injector.sh"
cat >"$INJECTOR" <<'EOF_INJECTOR'
#!/bin/sh
echo "wrapper $*" >>"${INJECTOR_LOG:-/dev/null}"
for arg in "$@"; do
    case "$arg" in -Zcodegen-backend=*|--kani-compiler) exec "$@" -Cllvm-args=--no-unwinding-checks ;; esac
done
exec "$@"
EOF_INJECTOR
chmod 755 "$INJECTOR"

lines() { grep -c . <<<"$1"; true; }

# cargo_problems <case dir> <package crate name>: what cargo's -v log must show.
# cargo renders each compile as `Running `<env> <program> <args>``, single-quoting
# any value with a space (the seal path has one), so trustc may appear quoted.
cargo_problems() {
    local dir="$1" crate="$2" stderr="$1/stderr.txt" compiles host package n ns
    local key_canon="${CASE_KEY:-$KEY_CANON}"
    compiles="$(grep -E -- 'Running `.* --crate-name [A-Za-z0-9_]+ ' "$stderr")"
    if [[ -z "$compiles" ]]; then
        echo "no cargo -v compile lines"
        return
    fi
    n="$(grep -vcF -e "'$TRUSTC' --crate-name " -e " $TRUSTC --crate-name " \
        -e "\`$TRUSTC --crate-name " <<<"$compiles")"
    [[ "$n" == 0 ]] || echo "$n compile(s) not run by $TRUSTC itself"
    host="$(grep -E -- '--crate-name build_script_build |--crate-type proc-macro ' <<<"$compiles")"
    n="$(lines "$host")"
    [[ "$n" -ge 2 ]] || echo "expected a build-script and a proc-macro compile, found $n"
    [[ "$(grep -c -- '-Zcodegen-backend' <<<"$host")" == 0 ]] || echo "a host unit selected a codegen backend"
    [[ "$(grep -c -- 'llvm-args' <<<"$host")" == 0 ]] || echo "a host unit got -Cllvm-args"
    [[ "$(grep -cF -- "$key_canon" <<<"$host")" == 0 ]] || echo "a host unit compiled against the KEY"
    [[ "$(grep -c -- '-Ztrust-verify=off' <<<"$host")" == "$n" ]] || echo "a host unit without -Ztrust-verify=off"
    [[ "$(grep -c -- '--cfg=kani_host' <<<"$host")" == "$n" ]] || echo "a host unit without --cfg=kani_host"
    package="$(grep -E -- "--crate-name $crate " <<<"$compiles")"
    [[ "$(lines "$package")" == 1 ]] || echo "expected one compile of $crate"
    grep -qF -- "-Zcodegen-backend=$DYLIB_CANON" <<<"$package" || echo "$crate did not load $DYLIB_CANON"
    grep -qF -- "--sysroot $key_canon " <<<"$package" || echo "$crate did not compile against the KEY sysroot $key_canon"
    grep -qF -- "-Ztrust-verify=off" <<<"$package" || echo "$crate compiled without -Ztrust-verify=off"
    grep -qF -- "-Cllvm-args=--trust-mc-engine-args=pct1:" <<<"$package" || echo "$crate got no pct1 engine-argument group"
    [[ "$(count 'Unknown command line argument' "$stderr")" == 0 ]] || echo "LLVM saw an engine argument"
    ns="$(cd "$dir/target" 2>/dev/null && ls -d kani-trustc-* 2>/dev/null)"
    [[ "$ns" =~ ^"$NAMESPACE_PREFIX"[0-9a-f]{12}$ ]] \
        || echo "target-dir namespace '${ns//$'\n'/ }' is not ${NAMESPACE_PREFIX}<KEY sha256[:12]>"
}

# cargo_lane <case> <pass|fail> <expected exit> <expected verdict> [driver args...]
# CARGO_SUCCESS / CARGO_FAILURES: '|'-separated check descriptions that must
# report SUCCESS / FAILURE.
cargo_lane() {
    local name="$1" half="$2" want_exit="$3" want="$4"; shift 4
    local dir="$OUT/$name" stdout="$OUT/$name/stdout.txt" problems=() verdicts check
    cargo_run "$name" "$half" -- --compiler-route trustc --trustc "$TRUSTC" \
        --backend-dylib "$DYLIB" --verbose --keep-temps "$@"
    [[ "$(cat "$dir/exit.txt")" == "$want_exit" ]] || problems+=("expected exit $want_exit")
    verdicts="$(grep -o 'VERIFICATION:- .*' "$stdout" | sort -u)"
    [[ "$verdicts" == "VERIFICATION:- $want" ]] || problems+=("expected only 'VERIFICATION:- $want'")
    [[ "$(count UNVALIDATED "$stdout")" == 0 ]] || problems+=("UNVALIDATED")
    local IFS='|'
    # A message-bearing assertion's Description carries the message's own quotes
    # (`Description: ""sum reaches the macro limit""`), so match the text.
    for check in ${CARGO_SUCCESS-}; do
        grep -A1 'Status: SUCCESS' "$stdout" | grep -F -- 'Description: ' | grep -qF -- "$check" \
            || problems+=("no SUCCESS check '$check'")
    done
    for check in ${CARGO_FAILURES-}; do
        grep -A1 'Status: FAILURE' "$stdout" | grep -F -- 'Description: ' | grep -qF -- "$check" \
            || problems+=("no FAILURE check '$check'")
    done
    unset IFS
    if [[ " $* " == *" --ay-chc "* ]]; then
        grep -q 'Detected HORN logic' "$stdout" || problems+=("no HORN logic line")
        if [[ "$want" == FAILED ]]; then
            grep -q '^\[AY:CTREX_CAT:Genuine\]' "$stdout" || problems+=("CHC failure is not a Genuine counterexample")
        fi
    fi
    while IFS= read -r p; do [[ -n "$p" ]] && problems+=("$p"); done < <(route_problems "$dir")
    while IFS= read -r p; do [[ -n "$p" ]] && problems+=("$p"); done \
        < <(cargo_problems "$dir" "cargo_pair_$half")
    if [[ -n "${CASE_EXPECT_HOST_CFG-}" ]] \
        && ! grep -E -- '--crate-name build_script_build ' "$dir/stderr.txt" | grep -qF -- "$CASE_EXPECT_HOST_CFG"; then
        problems+=("the build script compile does not carry $CASE_EXPECT_HOST_CFG: the configuration was not read")
    fi
    [[ ! -e "$dir/wrapper.log" ]] || problems+=("a rustc wrapper ran ($(lines "$(cat "$dir/wrapper.log")") calls)")
    report "$name" ${problems[@]+"${problems[@]}"}
}

# cargo_refusal <case> <pass|fail> [driver args...]: refused before any cargo compile.
cargo_refusal() {
    local name="$1" half="$2"; shift 2
    local dir="$OUT/$name" stdout="$OUT/$name/stdout.txt" problems=()
    cargo_run "$name" "$half" -- --compiler-route trustc --trustc "$TRUSTC" \
        --backend-dylib "$DYLIB" --verbose "$@"
    [[ "$(cat "$dir/exit.txt")" != 0 ]] || problems+=("expected a nonzero exit")
    [[ "$(count 'VERIFICATION:-' "$stdout")" == 0 ]] || problems+=("printed a VERIFICATION line")
    [[ "$(count '^\[AY:COMPILER_ROUTE' "$stdout")" == 0 ]] || problems+=("printed a route marker")
    [[ "$(count 'Running `' "$dir/stderr.txt")" == 0 ]] || problems+=("cargo compiled something")
    [[ ! -e "$dir/wrapper.log" ]] || problems+=("a rustc wrapper ran")
    grep -q 'compiler route trustc refused' "$stdout" || problems+=("no 'compiler route trustc refused'")
    if [[ -n "${REFUSAL_WANT-}" ]]; then
        grep -qF -- "$REFUSAL_WANT" "$stdout" || problems+=("the refusal does not say '$REFUSAL_WANT'")
    fi
    report "$name" ${problems[@]+"${problems[@]}"}
}

CARGO_SUCCESS='assertion failed: a + b < SUM_LIMIT' \
    cargo_lane cargo-bmc-pass pass 0 SUCCESSFUL
CARGO_FAILURES='sum reaches the macro limit|unwinding assertion loop 0' \
    cargo_lane cargo-bmc-fail fail 1 FAILED
CARGO_SUCCESS='assertion failed: a + b < SUM_LIMIT' \
    cargo_lane cargo-chc-pass pass 0 SUCCESSFUL --ay-chc
CARGO_FAILURES='sum reaches the macro limit' \
    cargo_lane cargo-chc-fail fail 1 FAILED --ay-chc --harness bounded_add_reaches_the_macro_limit
# Wrappers in the package's cargo configuration that would inject
# --no-unwinding-checks into the target units, and a host triple table (which
# replaces a command-line host.rustflags): the route disables the wrappers and
# keeps its host posture, so the unwind-bound harness still FAILS.
CASE_CARGO_CONFIG="$(printf '[build]\nrustc-wrapper = "%s"\nrustc-workspace-wrapper = "%s"\n\n[host.%s]\nrustflags = ["--cfg=from_host_table"]' "$INJECTOR" "$INJECTOR" "$HOST_TRIPLE")" \
    CASE_EXPECT_HOST_CFG='--cfg=from_host_table' CARGO_FAILURES='unwinding assertion loop 0' \
    cargo_lane cargo-config-wrappers-host-table fail 1 FAILED --harness loop_runs_past_its_unwind_bound
# The same wrapper named in the environment, one variable at a time: refused, not
# silently dropped.
for wrapper_var in RUSTC_WRAPPER RUSTC_WORKSPACE_WRAPPER CARGO_BUILD_RUSTC_WRAPPER \
    CARGO_BUILD_RUSTC_WORKSPACE_WRAPPER; do
    CASE_WRAPPER_ENV="$wrapper_var" REFUSAL_WANT="rustc wrapper variable(s) $wrapper_var=" \
        cargo_refusal "cargo-refuse-env-$wrapper_var" fail --harness loop_runs_past_its_unwind_bound
done
# The single-file RUSTFLAGS refusal holds for cargo units.
CASE_RUSTFLAGS='-Cllvm-args=--no-unwinding-checks' \
    REFUSAL_WANT='RUSTFLAGS token(s) ["-Cllvm-args=--no-unwinding-checks"]' \
    cargo_refusal cargo-refuse-rustflags-engine-flag fail --harness loop_runs_past_its_unwind_bound
# So does the engine-knob refusal.
CASE_ENV='TRUST_MC_NO_LOOP_RULE=1' REFUSAL_WANT='engine environment knob(s) TRUST_MC_NO_LOOP_RULE' \
    cargo_refusal cargo-refuse-engine-knob fail --harness loop_runs_past_its_unwind_bound
# The same knob in the package's cargo [env] table, which cargo would set on every
# rustc after the launcher's environment edits: refused before any compile.
CASE_CARGO_CONFIG=$'[env]\nTRUST_MC_NO_LOOP_RULE = "1"' \
    REFUSAL_WANT='cargo [env] table in effect here sets TRUST_MC_NO_LOOP_RULE=1' \
    cargo_refusal cargo-refuse-config-env-knob fail --harness loop_runs_past_its_unwind_bound
# An engine flag in the [host] tables' environment form (it reaches build scripts
# and proc-macros): refused, naming the variable.
CASE_ENV='CARGO_HOST_RUSTFLAGS=-Cllvm-args=--no-unwinding-checks' \
    REFUSAL_WANT='host rustflags variable(s) CARGO_HOST_RUSTFLAGS=-Cllvm-args=--no-unwinding-checks' \
    cargo_refusal cargo-refuse-env-host-rustflags fail --harness loop_runs_past_its_unwind_bound

# A KEY library replaced in place between two runs on one target dir. Cargo
# fingerprints the --sysroot path, not the rlibs, so without the KEY content
# identity in the namespace the second run reported `Fresh cargo-pair-fail` and a
# verdict from artifacts compiled against the previous library (review finding,
# T1 S7). The second run must compile against the replaced library (and fail to,
# since it is not an rlib) or refuse; never Fresh, never a verdict.
STALE="$OUT/stale-key/$(basename "$KEY")"
rm -rf "$OUT/stale-key"; mkdir -p "$OUT/stale-key"
cp -cR "$KEY" "$STALE" 2>/dev/null || cp -R "$KEY" "$STALE"
CASE_KEY="$STALE" CARGO_FAILURES='sum reaches the macro limit' \
    cargo_lane cargo-stale-key-rlib fail 1 FAILED --harness bounded_add_reaches_the_macro_limit
printf 'not an rlib\n' >"$STALE/lib/libkani.rlib"
CASE_KEY="$STALE" cargo_rerun cargo-stale-key-rlib fail -- --compiler-route trustc --trustc "$TRUSTC" \
    --backend-dylib "$DYLIB" --verbose --keep-temps --harness bounded_add_reaches_the_macro_limit
problems=()
dir="$OUT/cargo-stale-key-rlib"
[[ "$(cat "$dir/exit2.txt")" != 0 ]] || problems+=("rerun: expected a nonzero exit")
[[ "$(count 'VERIFICATION:-' "$dir/stdout2.txt")" == 0 ]] || problems+=("rerun: printed a VERIFICATION line from the previous library's artifacts")
[[ "$(count 'Fresh cargo-pair-fail' "$dir/stderr2.txt")" == 0 ]] || problems+=("rerun: cargo reported the package Fresh")
n="$(cd "$dir/target" && ls -d kani-trustc-* 2>/dev/null | grep -c .)"
[[ "$n" == 2 ]] || problems+=("rerun: expected a second target-dir namespace for the replaced library, found $n")
if [[ ${#problems[@]} -eq 0 ]]; then
    printf 'ok    %-26s exit=%s %s\n' cargo-stale-key-rlib-rerun "$(cat "$dir/exit2.txt")" no-verdict
else
    FAILURES=$((FAILURES + 1))
    printf 'FAIL  %-26s exit=%s: %s\n' cargo-stale-key-rlib-rerun "$(cat "$dir/exit2.txt")" "$(IFS=';'; echo "${problems[*]}")"
fi

# ---------------------------------------------------------------------------

# A trustc from another seal against this KEY and dylib: the route must refuse it
# because the KEY was built by another librustc_driver.
if [[ -n "$REFUSED_SKIP" && "$REQUIRE_OTHER_SEAL" == 1 ]]; then
    FAILURES=$((FAILURES + 1))
    printf 'FAIL  %-26s %s (TRUST_MC_SMOKE_REQUIRE_OTHER_SEAL=1)\n' refuse-other-seal-trustc "$REFUSED_SKIP"
elif [[ -n "$REFUSED_SKIP" ]]; then
    SKIPPED+=(refuse-other-seal-trustc)
    printf 'SKIPPED %-24s %s\n' refuse-other-seal-trustc "$REFUSED_SKIP"
elif [[ -x "$REFUSED_TRUSTC" ]]; then
    REFUSAL_WANT='differs from the trustc sysroot driver sha256' \
        refusal refuse-other-seal-trustc "$KEY" --trustc "$REFUSED_TRUSTC" --backend-dylib "$DYLIB"
else
    FAILURES=$((FAILURES + 1))
    printf 'FAIL  %-26s no trustc at %s (TRUST_MC_SMOKE_REFUSED_TRUSTC)\n' refuse-other-seal-trustc "$REFUSED_TRUSTC"
fi

# A KEY whose KEY.json names another driver sha256 (an APFS clone where possible).
FORGED="$OUT/forged-key/$(basename "$KEY")"
rm -rf "$OUT/forged-key"; mkdir -p "$OUT/forged-key"
cp -cR "$KEY" "$FORGED" 2>/dev/null || cp -R "$KEY" "$FORGED"
OTHER_SHA="$(printf '%s' "$DRIVER_SHA" | tr '0123456789abcdef' '123456789abcdef0')"
sed -i '' "s/\"driver_sha256\": *\"$DRIVER_SHA\"/\"driver_sha256\": \"$OTHER_SHA\"/" "$FORGED/KEY.json"
if grep -q "$OTHER_SHA" "$FORGED/KEY.json"; then
    refusal refuse-key-other-driver "$FORGED" --trustc "$TRUSTC" --backend-dylib "$FORGED/codegen-backends/librustc_codegen_trust_mc.dylib"
else
    FAILURES=$((FAILURES + 1))
    printf 'FAIL  %-26s could not forge driver_sha256 in %s\n' refuse-key-other-driver "$FORGED/KEY.json"
fi

# The backend dylib copied into a world-writable (sticky) directory.
WW="$OUT/world-writable"
rm -rf "$WW"; mkdir -p "$WW"; chmod 1777 "$WW"
cp "$DYLIB" "$WW/librustc_codegen_trust_mc.dylib"
refusal refuse-world-writable-dylib "$KEY" --trustc "$TRUSTC" --backend-dylib "$WW/librustc_codegen_trust_mc.dylib"
chmod 755 "$WW"

# The vacuity rule: a harness with no checks is inconclusive, never a proof.
lane vacuity-empty-harness empty.rs 1 'INCONCLUSIVE (no checks)'

# A loop-contract harness whose single lane fails is eligible for the driver's
# two-lane retry, and this route cannot run it: the lanes set engine environment
# knobs on child drivers and the route refuses a child while one is set. The
# route must say so by NAME and leave the single-lane verdict alone.
#
# Before the S7 repair the driver started the lanes anyway and printed the
# refused child's stdout inside its own `[AY:LOOP_TWO_LANE]` diagnostic, where
# `tools/kani-domination` read it as THIS run refusing: four attested,
# verdict-bearing CHC rows of the acceptance sample were scored `route error`
# for a refusal that happened in a child process.
loop_contract_route_limitation() {
    local name=chc-loop-contract-route-limitation
    local dir="$OUT/$name" stdout="$OUT/$name/stdout.txt" problems=()
    run "$name" "$KEY" -- "$FIXTURES/loop_contract_retry.rs" --compiler-route trustc \
        --trustc "$TRUSTC" --backend-dylib "$DYLIB" --verbose --keep-temps \
        -Z unstable-options -Z loop-contracts --ay-chc
    [[ "$(cat "$dir/exit.txt")" == 1 ]] || problems+=("expected exit 1")
    [[ "$(grep -o 'VERIFICATION:- .*' "$stdout" | sort -u)" == "VERIFICATION:- FAILED" ]] \
        || problems+=("expected only 'VERIFICATION:- FAILED'")
    # Named, once, and naming both knobs.
    [[ "$(count '^\[AY:ROUTE_LIMITATION:two-lane-loop-contract-retry route=trustc\]' "$stdout")" == 1 ]] \
        || problems+=("no [AY:ROUTE_LIMITATION:two-lane-loop-contract-retry route=trustc] marker")
    grep -q 'TRUST_MC_COMPOUND_DECREASES, TRUST_MC_NO_LOOP_RULE' "$stdout" \
        || problems+=("the limitation does not name the knobs the lanes need")
    # No lane was started, so no child refusal is quoted anywhere.
    [[ "$(count 'obligations lane' "$stdout")" == 0 ]] || problems+=("a lane ran on this route")
    if grep -qF 'compiler route trustc refused' "$stdout" "$dir/stderr.txt"; then
        problems+=("a route refusal reached the output of a run that produced a verdict")
    fi
    while IFS= read -r p; do [[ -n "$p" ]] && problems+=("$p"); done < <(route_problems "$dir")
    report "$name" ${problems[@]+"${problems[@]}"}
}
loop_contract_route_limitation

if [[ "$FAILURES" -ne 0 ]]; then
    echo "trust-lane-smoke: $FAILURES case(s) not as expected"
    exit 1
fi
if [[ ${#SKIPPED[@]} -ne 0 ]]; then
    echo "trust-lane-smoke: every case run as expected; SKIPPED: ${SKIPPED[*]}"
else
    echo "trust-lane-smoke: all cases as expected"
fi
