#!/usr/bin/env bash
# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

set -euo pipefail

cd "$(dirname "$0")"

out_dir="${PWD}/target"
log_file="${PWD}/kani.log"
marker="__kani_write_any_slice_elem"

rm -rf "${out_dir}" "${log_file}"

if ! kani write_any_slice_stub_verified.rs \
    -Z function-contracts \
    -Z stubbing \
    --only-codegen \
    --keep-temps \
    --target-dir "${out_dir}" \
    --harness reaches_write_any_slice_model \
    > "${log_file}" 2>&1
then
    cat "${log_file}"
    exit 1
fi

smt_file="$(find "${out_dir}" -name '*.smt2' -print 2>/dev/null | sort | head -n 1)"
if [[ -z "${smt_file}" ]]; then
    smt_file="$(find . -path './target' -prune -o -name '*.smt2' -print 2>/dev/null | sort | head -n 1)"
fi

if [[ -z "${smt_file}" ]]; then
    echo "error: expected Kani to generate an .smt2 file"
    exit 1
fi

grep -Fq "${marker}" "${smt_file}"
echo "found ${marker}"
