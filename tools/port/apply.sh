#!/bin/sh
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# STOCK-AS-ORACLE: the frozen nightly half of the dual lane is the
# Kani-comparison baseline only, kept by the owner's ruling of 2026-09-29.
#
# Re-apply the dual-toolchain (frozen nightly + Trust) rewrites to
# trust-mc-compiler, e.g. after rebasing onto a moving main, then prove the
# rewrites are idempotent. Both scripts only rewrite spellings that mean the
# same program on the frozen nightly; see trust-mc-compiler/src/rustc_compat.rs.
#
# The codemods are not layout-aware (an or-pattern they split or an arm they
# add lands on one line), so every file they change is passed through rustfmt
# with the repo rustfmt.toml -- when that file was rustfmt-clean before the
# rewrite. A file that was not clean stays as rewritten rather than being
# reformatted wholesale. The formatter is `trustfmt`, the Trust toolchain's
# rustfmt (owner ruling 2026-09-23: never stock rustfmt on an ALab machine);
# override it with RUSTFMT=/path/to/formatter. It used to be the frozen
# nightly's rustfmt, resolved with `rustup which --toolchain`: on a host without
# that toolchain rustup AUTO-INSTALLED a minimal nightly (no rustfmt, no
# rustc-dev) and then failed anyway (measured 2026-09-24).
#
# After running, check both lanes:
#   RUSTC_WRAPPER= "$(scripts/resolve-trust-tool.sh targo)" --unverified check -p trust-mc-compiler
#   (frozen nightly) see docs/KANI-LANE-REVIVAL.md
set -eu
cd "$(dirname "$0")/../.."
SRC=trust-mc-compiler/src

if [ -z "${RUSTFMT:-}" ]; then
    RUSTFMT="$(command -v trustfmt)" || {
        echo "tools/port/apply.sh: trustfmt is not on PATH; install the Trust toolchain" \
             "or set RUSTFMT=/path/to/formatter" >&2
        exit 2
    }
fi
"$RUSTFMT" --version >/dev/null

work="$(mktemp -d "${TMPDIR:-/tmp}/trust-port-apply.XXXXXX")"
trap 'rm -rf "$work"' EXIT
trap 'exit 1' HUP INT TERM
cp -R "$SRC" "$work/before"

python3 tools/port/trust_api_codemod.py
python3 tools/port/trust_only_arms.py

rustfmt_stdout() {
    "$RUSTFMT" --edition 2024 --config-path rustfmt.toml --emit stdout < "$1" > "$2"
}

formatted=0
skipped=0
(cd "$SRC" && find . -type f -name '*.rs' | LC_ALL=C sort) > "$work/files"
while IFS= read -r rel; do
    rel="${rel#./}"
    before="$work/before/$rel"
    after="$SRC/$rel"
    if [ -f "$before" ]; then
        cmp -s "$before" "$after" && continue
        rustfmt_stdout "$before" "$work/before-formatted.rs"
        if ! cmp -s "$before" "$work/before-formatted.rs"; then
            echo "tools/port/apply.sh: $after was not rustfmt-clean before the rewrite; left as rewritten" >&2
            skipped=$((skipped + 1))
            continue
        fi
    fi
    rustfmt_stdout "$after" "$work/formatted.rs"
    cmp -s "$after" "$work/formatted.rs" || cat "$work/formatted.rs" > "$after"
    formatted=$((formatted + 1))
done < "$work/files"

python3 tools/port/trust_api_codemod.py --check >/dev/null
python3 tools/port/trust_only_arms.py --check >/dev/null
echo "tools/port/apply.sh: rewrites applied and idempotent; $formatted rewritten files formatted, $skipped left unformatted"
