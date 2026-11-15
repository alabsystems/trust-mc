// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Tests for static array-of-fat-pointer CHC encoding (#4196).
//!
//! Verifies that `static STATIC: [&str; N] = [...]` resolves provenance
//! for each element's data pointer and initializes target memory with
//! string byte data.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

fn static_state_idx_for_local(chc_ctx: &ChcCtx<'_, '_>, local: usize, name: &str) -> usize {
    chc_ctx
        .ref_resolution
        .static_ref_to_state_idx
        .get(&local)
        .copied()
        .unwrap_or_else(|| panic!("{name} local should map to a static state var"))
}

// Part of #4196: static array of &str — fat pointer provenance resolution.
const STATIC_STR_ARRAY_SOURCE: &str = r#"
    static STATIC: [&str; 1] = ["FOO"];

    pub fn check_static() -> usize {
        let x = STATIC[0];
        x.len()
    }
"#;

/// Array-valued statics with `&str` elements must resolve provenance for each
/// element's data pointer. Without #4196, the init expression reads raw bytes
/// for the pointer half (which are zero), producing an all-zero fat pointer.
#[test]
fn test_static_str_array_resolves_fat_ptr_provenance() {
    with_test_ay_ctx_for_source(STATIC_STR_ARRAY_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "check_static");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "check_static", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let referenced_locals = referenced_static_locals(&body);
        let static_local = referenced_locals.get("STATIC").copied().expect("expected STATIC local");

        let state_idx = static_state_idx_for_local(&chc_ctx, static_local, "STATIC");

        // The init value should exist and be an array.
        let init_val = chc_ctx
            .ref_resolution
            .static_initial_values
            .get(&state_idx)
            .expect("STATIC should have an initial value");
        assert!(
            init_val.sort().is_array(),
            "STATIC init should be an array sort, got {:?}",
            init_val.sort()
        );

        // The init expression should NOT be all-zero (the pre-#4196 raw-byte fallback
        // produces `store(const_array(#x0...0), 0, #x0...0)` — a zero fat pointer).
        // After the fix, the data pointer half is a non-zero concrete address.
        let init_str = init_val.to_string();
        let is_all_zero_element = init_str.contains("store") && !init_str.contains("concat");
        assert!(
            !is_all_zero_element || init_str.contains("concat"),
            "STATIC init should have resolved fat-ptr elements via concat, not raw zero bytes"
        );

        // The "FOO" string's bytes are seeded in its OWN object, whole (D2,
        // `decl::global_objects`): the string is constant memory reached
        // through STATIC's initializer, read at `str`, so each byte is a `u8`
        // seed at that object's offset. (Before the constant-pointer rule the
        // static collector mirrored them into `static_memory_inits` at the
        // address it minted for the target; the target's ONE object now
        // carries them.)
        let byte_at = |obj: u32, off: u64| {
            chc_ctx.ref_resolution.const_ref_memory_inits.iter().find_map(
                |(tk, _, value, o, at)| {
                    (&**tk == "u8" && *o == obj && *at == off).then(|| value.to_string())
                },
            )
        };
        let string_objects: HashSet<u32> = chc_ctx
            .ref_resolution
            .const_ref_memory_inits
            .iter()
            .filter(|(tk, _, _, _, _)| &**tk == "u8")
            .map(|(_, _, _, obj, _)| *obj)
            .collect();
        assert!(
            string_objects.iter().any(|&obj| {
                byte_at(obj, 0).as_deref() == Some("#x46")
                    && byte_at(obj, 1).as_deref() == Some("#x4f")
                    && byte_at(obj, 2).as_deref() == Some("#x4f")
            }),
            "the 'FOO' bytes should be seeded at offsets 0..3 of one object, got objects {string_objects:?}"
        );
    });
}
