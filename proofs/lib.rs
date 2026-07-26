// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0 OR MIT
//
//! trust_mc formal proofs library.
//!
//! This crate contains trust_mc compatibility proof harnesses for verifying trust_mc's core invariants.
//!
//! # Running Proofs
//!
//! ```bash
//! cargo trust_mc --manifest-path proofs/Cargo.toml
//! ```

// Include proof modules conditionally when running under Kani-compatible proof mode.
#[cfg(kani)]
mod heap_stride_isolation;
