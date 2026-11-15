#!/bin/sh
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Refuse a tree whose trust-mc-compiler sources have drifted off the
# dual-toolchain compat spellings (trust-mc-compiler/src/rustc_compat.rs).
#
# WHY THIS EXISTS. trust-mc-compiler compiles on two rustc APIs: the frozen
# nightly and the Trust seal. Their `rustc_public` differs — Trust's `Rvalue::Use`
# carries a second field and has no `ShallowInitBox`, and Trust adds variants the
# nightly has never heard of. `tools/port/*.py` rewrite the nightly-only spellings
# into ones that mean the same program on BOTH, and they already carry a `--check`
# mode. Nothing ran it before landing.
#
# Measured 2026-09-14: a rebase onto main reintroduced `Rvalue::Use(op)` in two
# files. trust-mc-engine then failed to compile on seal 8595 with three errors, so
# NO BACKEND DYLIB COULD BE BUILT AT ALL and the whole trustc route was dead on
# main — while the frozen-nightly lane stayed green, so nothing announced it. This
# check answers in about a second, needs no toolchain, and names both files.
#
# Run it before landing anything that touches trust-mc-compiler/src. It is not a
# substitute for building on the seal; it is the cheap half that catches the
# common case.
#
# Usage: scripts/check-trust-lane-port.sh
set -eu
cd "$(dirname "$0")/.."

fail=0

if ! python3 tools/port/trust_api_codemod.py --check; then
    fail=1
fi
if ! python3 tools/port/trust_only_arms.py --check; then
    fail=1
fi

if [ "$fail" -ne 0 ]; then
    cat >&2 <<'MSG'

check-trust-lane-port: the tree carries spellings that do not compile on the
Trust seal. This is the failure that silently kills the trustc route: the
frozen-nightly lane keeps building, and no backend dylib can be produced.

Fix with the codemods that just told you what they would change:

    tools/port/apply.sh

then re-run this check. See trust-mc-compiler/src/rustc_compat.rs for what each
rewrite means, and tools/port/trust_only_arms.py for why a Trust-only match arm
is a per-site soundness decision rather than something a script can infer.
MSG
    exit 1
fi

echo "check-trust-lane-port: ok: trust-mc-compiler/src is on the dual-toolchain spellings"
