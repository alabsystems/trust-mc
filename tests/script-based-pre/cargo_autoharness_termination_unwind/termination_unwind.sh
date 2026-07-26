#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# Author: Andrew Yates
# Licensed under the Apache License, Version 2.0

# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

# Set the timeout to 5m to ensure that the gcd_recursion test gets killed because of the unwind bound
# and not because the verifier times out.
cargo kani autoharness -Z autoharness --harness-timeout 5m -Z unstable-options
