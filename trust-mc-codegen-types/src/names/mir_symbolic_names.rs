// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR local names and discriminant/undef symbolics.
//!
//! Naming for MIR local variables, symbolic discriminants, and undefined
//! value symbolics. Used across `place*`, `ssa`, `codegen_stmt_aggregate_discr`,
//! and `rvalue_discriminant`.
//!
//! Part of #2304, #2408.

use std::fmt::Write as _;

/// MIR local variable name: `{fn_name}::local_{idx}`.
///
/// The canonical SSA name for a MIR local in the AY encoding.
pub fn local_name(fn_name: &str, local_idx: usize) -> String {
    let mut local_name = String::with_capacity(fn_name.len() + 28);
    local_name.push_str(fn_name);
    local_name.push_str("::local_");
    let _ = write!(&mut local_name, "{local_idx}");
    local_name
}

/// Discriminant variable name: `{base}_discriminant`.
///
/// Used as a fallback symbolic discriminant variable name.
pub fn discriminant_name(base: &str) -> String {
    let mut s = String::with_capacity(base.len() + 14);
    s.push_str(base);
    s.push_str("_discriminant");
    s
}

/// Allocation-related discriminant symbol: `__alloc_discr_{local}_{proj_len}`.
///
/// Used for ControlFlow/Result allocation discriminants (#2618).
pub fn alloc_discr_name(local: usize, proj_len: usize) -> String {
    let mut s = String::with_capacity(32);
    s.push_str("__alloc_discr_");
    let _ = write!(&mut s, "{local}_{proj_len}");
    s
}

/// General enum discriminant symbol: `__discr_{local}_{proj_len}`.
///
/// Used for symbolic discriminant variables on general enums.
pub fn discr_sym_name(local: usize, proj_len: usize) -> String {
    let mut s = String::with_capacity(24);
    s.push_str("__discr_");
    let _ = write!(&mut s, "{local}_{proj_len}");
    s
}

/// Undefined symbolic variable: `__undef_{name}_{id}`.
///
/// Used for Option::None and uninitialized Datatype values.
pub fn undef_sym_name(name: &str, id: u64) -> String {
    let mut s = String::with_capacity(name.len() + 16);
    s.push_str("__undef_");
    s.push_str(name);
    s.push('_');
    let _ = write!(&mut s, "{id}");
    s
}

// Tests live in trust_mc-compiler (standalone test binaries cannot link rustc sysroot dylibs).
