# Copyright Kani Contributors
# SPDX-License-Identifier: Apache-2.0 OR MIT

This directory contains "overlay" files (e.g. expected files) that should be copied into directories under perf before running compiletest.

Explanation: compiletest's `cargo-trust_mc` mode (which is used for running the perf tests) looks for "<harness-name>.expected" files and runs `targo trust-mc --harness <harness-name>` for each.
Some of the perf tests are external repositories that are integrated as git submodules, so we cannot commit files in their subtrees.
Thus, we instead commit any files needed under the "overlays" directory, which then get copied over by the perf runner before it calls compiletest. NOTE: that runner (upstream Kani's `kani-perf.sh`) is **not checked into this repository**; the copy step has to be done by hand or scripted locally.

To create overlay files for `perf/foo`, place them in a `perf/overlays/foo` directory.
They will get copied over following the same directory structure.
