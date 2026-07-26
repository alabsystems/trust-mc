#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

set -eu

echo
echo "Starting dead flag rejection check..."
echo

export RUST_BACKTRACE=1
cd "$(dirname "$0")"

check_legacy_cbmc_policy() {
    description="$1"
    shift
    echo "Checking ${description}..."
    if "$@" >kani.log 2>&1; then
        echo "Error: ${description} unexpectedly accepted CBMC-only artifact flag."
        cat kani.log
        rm -f kani.log
        exit 1
    fi

    for expected in \
        "--cbmc-args is CBMC-only and has been discarded by trust-mc" \
        "--solver kissat is CBMC-only and has been ignored by trust-mc" \
        "--synthesize-loop-contracts is a no-op in trust-mc" \
        "--gen-c is CBMC-only (C-code generation) and not supported in trust-mc"
    do
        if ! grep -Fq -- "$expected" kani.log; then
            echo "Error: ${description} did not report expected policy message: ${expected}"
            cat kani.log
            rm -f kani.log
            exit 1
        fi
    done

    if grep -Fq "unexpected argument" kani.log; then
        echo "Error: ${description} reported a generic unknown-argument error instead of CBMC policy."
        cat kani.log
        rm -f kani.log
        exit 1
    fi
    rm -f kani.log
}

legacy_flags=(--gen-c --solver kissat --synthesize-loop-contracts --cbmc-args --object-bits 4)

check_legacy_cbmc_policy "single-file invocation" kani singlefile.rs "${legacy_flags[@]}"
(cd multifile && check_legacy_cbmc_policy "cargo-trust-mc invocation" cargo kani --target-dir build "${legacy_flags[@]}")

echo "Finished dead flag rejection check successfully."
echo
