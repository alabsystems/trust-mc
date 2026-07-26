// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Foundation crate for Kani function classification and type layout.
//!
//! Contains the `KaniFunction` enum hierarchy (hooks, intrinsics, models)
//! and `LayoutOf` — a rustc type layout wrapper used throughout codegen.
//!
//! Extracted from `trust_mc-compiler/src/kani_middle/` (Part of #2997) so that
//! codegen subcrates can depend on these types without circular dependency
//! on `trust_mc-compiler`.

#![feature(rustc_private)]
extern crate rustc_public;
// rustc_driver is required for sysroot crate linking in test binaries.
#[cfg(test)]
extern crate rustc_driver;
#[cfg(test)]
extern crate rustc_public_bridge;

pub mod abi;
pub mod kani_functions;
