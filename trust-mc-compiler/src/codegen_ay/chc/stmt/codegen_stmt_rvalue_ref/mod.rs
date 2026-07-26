// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Ref/AddressOf and Cast dispatch for CHC rvalue encoding.
//!
//! Split from codegen_stmt_rvalue.rs per #3199.
//! Submodules:
//! - `cast_dispatch`: `translate_rvalue_cast` + fn-pointer reification
//! - `ref_address`: translate_ref_or_addressof (Ref/AddressOf encoding)
//! - `transmute_reinterpret`: fixed-layout transmute helpers
//! - `unsize_dyn`: PointerCoercion::Unsize helpers

mod cast_dispatch;
mod ref_address;
mod transmute_reinterpret;
mod unsize_dyn;
