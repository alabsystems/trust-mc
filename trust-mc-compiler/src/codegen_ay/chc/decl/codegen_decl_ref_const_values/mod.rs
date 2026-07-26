// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Constant-reference scalar-value collection and provenance resolution.
//!
//! This directory module hosts the collect/worklist engine and provenance
//! helpers for constant-reference encoding. The central decode match lives
//! in sibling modules (`codegen_decl_ref_const_extract` and friends).
//!
//! Originally a single file; split per #3694 (collect/provenance-first
//! module extraction) and #4147 (large-file decomposition).

// Re-export the parent's ChcCtx so child modules can use `super::ChcCtx`.
use super::ChcCtx;

mod collect;
mod provenance;
