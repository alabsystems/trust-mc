// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Drop terminator semantics for CHC encoding.
//!
//! Contains:
//! - `codegen_drop`: main Drop dispatch, concrete drop inlining, sound fallback
//! - `arc_drop`: Arc/Rc drop as simple deallocation
//! - `box_drop`: Box dealloc logic
//! - `dyn_dispatch`: vtable-based dyn Trait drop resolution (D1 unique candidate)
//! - `dyn_dispatch_multi`: D2 multi-impl vtable-guarded dispatch
//! - `no_drop`: type-level no-drop classification
//! - `shared_ptr`: Arc/Rc shared pointer drop helpers
//! - `emit_helpers`: common rule emission helpers
//! - `baseline`: D2 candidate baseline save/restore
//!
//! Split from monolithic `transition_drop.rs` — Part of #3927
//! within the broader #3254 CHC god-module decomposition.

mod arc_drop;
mod baseline;
mod box_drop;
mod codegen_drop;
mod dyn_dispatch;
mod dyn_dispatch_multi;
mod emit_helpers;
mod no_drop;
mod shared_ptr;
#[cfg(test)]
mod tests;

pub(in crate::codegen_ay::chc) use box_drop::collect_box_dyn_dealloc_effects;
pub(super) use codegen_drop::codegen_drop;
pub(in crate::codegen_ay::chc) use codegen_drop::{
    coroutine_drop_fields_trivially_no_drop, pin_box_coroutine_inner_ty,
};
pub(in crate::codegen_ay::chc) use no_drop::ty_trivially_no_drop;
pub(in crate::codegen_ay::chc) use shared_ptr::{
    SharedPointerDeallocEffects, collect_shared_pointer_dealloc_effects,
    shared_pointer_drop_local_from_drop_arg, shared_pointer_inner_ty,
    shared_pointer_value_ptr_for_drop, shared_pointer_value_ptr_from_obj_id,
    try_translate_shared_pointer_inner_drop,
};

/// Reason why `codegen_drop()` took the sound-fallback path instead of inlining
/// the concrete `Drop::drop()` body. Part of #3791: provenance-coded diagnostics.
#[derive(Debug, Clone, Copy)]
enum DropFallbackReason {
    /// `drop_ty.kind()` is `RigidTy::Dynamic(..)` — needs vtable dispatch.
    DynDropUnsupported,
    /// `Instance::resolve_drop_in_place` returned a shim with no MIR body.
    DropShimNoBody,
    /// `translate_inline_body` returned `None` — inline walk bailed out.
    DropInlineWalkFailed,
}

impl DropFallbackReason {
    fn as_str(self) -> &'static str {
        match self {
            Self::DynDropUnsupported => "dyn_drop_unsupported",
            Self::DropShimNoBody => "drop_shim_no_body",
            Self::DropInlineWalkFailed => "drop_inline_walk_failed",
        }
    }
}
