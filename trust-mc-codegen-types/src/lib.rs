// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Foundation crate for trust_mc AY codegen: type coercion and SMT naming.
//!
//! Extracted from `trust_mc-compiler/src/codegen_ay/` for incremental build speed.
//! Part of #2997: split codegen_ay into subcrates.

#![feature(rustc_private)]

extern crate rustc_public;

// rustc_driver is required for linking private rustc crates in test binaries.
#[cfg(test)]
extern crate rustc_driver;

pub mod names;
pub mod types;
