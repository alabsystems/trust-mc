// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC rule-generation subsystem facade.
//!
//! This keeps the transition and fragment rule families behind a real `rules/`
//! module boundary while preserving the historical `super::...` imports used by
//! the already-split leaf modules.

pub(super) use super::{
    CallCoerce, CallTerminator, ChcCtx, KaniHook, KaniModel, chc_call_context, chc_fresh_name,
    codegen_call_coerce, codegen_expr_heap, codegen_types, collect_constructor_guards,
    declare_pending_var, dyn_coercion, heap_store_chains,
};
pub(super) use codegen_rules_pointer_check::CodegenRulesPointerCheck;

pub(super) mod codegen_rules;
pub(super) mod codegen_rules_entry;
pub(super) mod codegen_rules_entry_char;
pub(super) mod codegen_rules_entry_static;
pub(super) mod codegen_rules_helpers;
pub(super) mod codegen_rules_pointer_check;
mod fragment_compose;
mod fragment_fallback;
mod fragment_gen;
mod fragment_switchint;
