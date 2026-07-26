// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Thin re-export shim for `trust_mc-codegen-shared` crate.
//!
//! All logic has been extracted to the standalone `trust_mc-codegen-shared` crate
//! (Part of #2997). This module preserves existing import paths
//! (`crate::codegen_ay::shared::*`) so that consumers don't need changes.

mod inline_limits;
pub(in crate::codegen_ay) mod transmute_layout;

// Re-export all public items from the extracted crate.
pub(in crate::codegen_ay) use self::inline_limits::*;
pub(in crate::codegen_ay) use trust_mc_codegen_shared::*;
