#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

# Test that we can build the entire standard library with the trust-mc compiler.
# 1. Make a copy of the rust standard library.
# 2. Prepare a minimal copied library build.
# 3. Run trust-mc compiler.

set -e
set -u

TRUST_MC_DIR=$(git rev-parse --show-toplevel)
TMP_DIR="tmp_dir"

rm -rf ${TMP_DIR}
mkdir ${TMP_DIR}

cp -r dummy ${TMP_DIR}

# Create a custom standard library.
echo "[TEST] Copy standard library from the current toolchain"
SYSROOT=$(rustc --print sysroot)
STD_PATH="${SYSROOT}/lib/rustlib/src/rust/library"
cp -r "${STD_PATH}" "${TMP_DIR}"

echo "[TEST] Modify library"
# Note: Prepending with sed doesn't work on MacOs the same way it does in linux.
# sed -i '1s/^/#![cfg_attr(kani, feature(kani))]\n/' ${TMP_DIR}/library/std/src/lib.rs
cp ${TMP_DIR}/library/std/src/lib.rs ${TMP_DIR}/std_lib.rs
echo '#![cfg_attr(kani, feature(kani))]' > ${TMP_DIR}/library/std/src/lib.rs
cat ${TMP_DIR}/std_lib.rs >> ${TMP_DIR}/library/std/src/lib.rs

export RUST_BACKTRACE=1
export RUSTC_LOG=error
export __CARGO_TESTS_ONLY_SRC_ROOT=$(readlink -f ${TMP_DIR})/library
RUST_FLAGS=(
    "--kani-compiler"
    "-Cpanic=abort"
    "-Zalways-encode-mir"
    "-Zmir-enable-passes=-RemoveStorageMarkers"
    "-Zinline-mir=no"
    "-Cllvm-args=--ignore-global-asm"
    "-Cllvm-args=--build-std"
    "-Zcrate-attr=feature(register_tool)"
    "-Zcrate-attr=register_tool(kanitool)"
)
export RUSTFLAGS="${RUST_FLAGS[@]}"
export RUSTC="$TRUST_MC_DIR/target/trust-mc/bin/trust-mc-compiler"
export KANI_LOGS=kani_compiler::kani_middle=debug
TARGET=$(rustc -vV | awk '/^host/ { print $2 }')

pushd ${TMP_DIR}/dummy > /dev/null
# Compile the standard library with the AY backend.
cargo build --verbose -Z build-std --lib --target ${TARGET}
popd > /dev/null

echo "------ Build succeeded -------"

# Cleanup
rm -r ${TMP_DIR}
