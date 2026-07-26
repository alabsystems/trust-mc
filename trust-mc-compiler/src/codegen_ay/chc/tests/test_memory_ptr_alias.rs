// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for `memory_impl_ptr_alias.rs` — pointer-wrapper alias mirroring.
//!
//! `pointer_wrapper_alias_keys()` resolves transparent pointer wrapper alias
//! keys (NonNull<T>, Unique<T>) for type-indexed memory stores, so casted
//! pointer reinterpretation reads the same symbolic memory cell.
//!
//! Part of #2933 (zero-coverage remediation), #2912 (pointer wrapper aliasing).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use std::sync::Arc;

use super::common::*;

// =============================================================================
// pointer_wrapper_alias_keys — basic type key patterns
// =============================================================================

/// Source with raw pointer operations to create a ChcCtx at Mem level.
const PTR_SOURCE: &str = r#"
    #![allow(dead_code)]

    pub fn ptr_id(ptr: *const u32) -> *const u32 {
        ptr
    }
"#;

#[test]
fn test_ptr_key_produces_nonnull_and_unique_aliases() {
    with_test_ay_ctx_for_source(PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ptr_id");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ptr_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let aliases = chc_ctx.pointer_wrapper_alias_keys("ptr_u32");
        // ptr_u32 should produce NonNull_u32 and Unique_u32 variants
        assert!(
            aliases.iter().any(|k| k.contains("NonNull_u32")),
            "ptr_u32 should produce NonNull_u32 alias, got {:?}",
            aliases
        );
        assert!(
            aliases.iter().any(|k| k.contains("Unique_u32")),
            "ptr_u32 should produce Unique_u32 alias, got {:?}",
            aliases
        );
    });
}

#[test]
fn test_nonnull_key_produces_ptr_alias() {
    with_test_ay_ctx_for_source(PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ptr_id");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ptr_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let aliases = chc_ctx.pointer_wrapper_alias_keys("std_ptr_NonNull_u32");
        assert_eq!(aliases, vec![Arc::from("ptr_u32")], "NonNull_u32 should alias back to ptr_u32");
    });
}

#[test]
fn test_unique_key_produces_ptr_alias() {
    with_test_ay_ctx_for_source(PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ptr_id");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ptr_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let aliases = chc_ctx.pointer_wrapper_alias_keys("std_ptr_Unique_u32");
        assert_eq!(aliases, vec![Arc::from("ptr_u32")], "Unique_u32 should alias back to ptr_u32");
    });
}

#[test]
fn test_non_pointer_key_produces_no_aliases() {
    with_test_ay_ctx_for_source(PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ptr_id");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ptr_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        let aliases = chc_ctx.pointer_wrapper_alias_keys("u32");
        assert!(aliases.is_empty(), "non-pointer key should produce no aliases, got {:?}", aliases);
    });
}

#[test]
fn test_nested_ptr_key_produces_no_aliases() {
    with_test_ay_ctx_for_source(PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ptr_id");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ptr_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // ptr_ptr_u32 should NOT recurse — nested pointers are excluded
        let aliases = chc_ctx.pointer_wrapper_alias_keys("ptr_ptr_u32");
        assert!(
            aliases.is_empty(),
            "nested pointer key (ptr_ptr_T) should produce no aliases, got {:?}",
            aliases
        );
    });
}

#[test]
fn test_ref_key_produces_no_aliases() {
    with_test_ay_ctx_for_source(PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "ptr_id");
        let body = instance.body().expect("body");
        let chc_ctx = ChcCtx::new(
            ctx.tcx,
            &body,
            "ptr_id",
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() },
        );

        // ptr_ref_u32 should be excluded (ref_ prefix in inner)
        let aliases = chc_ctx.pointer_wrapper_alias_keys("ptr_ref_u32");
        assert!(aliases.is_empty(), "ptr_ref_ key should produce no aliases, got {:?}", aliases);
    });
}
