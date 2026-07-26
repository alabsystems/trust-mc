#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates <andrewyates.name@gmail.com>
# Licensed under the Apache License, Version 2.0

# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

cargo trust-mc autoharness -Z autoharness &
trust-mc_pid=$!

while kill -0 "${trust-mc_pid}" 2>/dev/null; do
    sleep 30
    if kill -0 "${trust-mc_pid}" 2>/dev/null; then
        echo "[TEST] waiting for ay tool timeout..." >&2
    fi
done

wait "${trust-mc_pid}"
