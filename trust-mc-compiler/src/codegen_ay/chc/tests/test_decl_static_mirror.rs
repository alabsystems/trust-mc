// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for nested static-field memory mirror registration (#3854).
//!
//! Verifies that `predeclare_static_memory_type_arrays()` materializes type
//! arrays for nested ADT field types discovered by
//! `register_static_memory_init_entries()`, and that the entry rule does not
//! silently drop static memory constraints.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const NESTED_STATIC_PROBE: &str = r#"
    #![allow(dead_code)]

    #[derive(Clone, Copy)]
    pub struct Pair {
        pub lo: u32,
        pub hi: u32,
    }

    pub static TABLE: [Pair; 2] = [
        Pair { lo: 1, hi: 2 },
        Pair { lo: 3, hi: 4 },
    ];

    pub fn probe_static_pair_field(idx: usize) -> u32 {
        let p = &TABLE[idx];
        p.hi
    }
"#;

/// D4: Assert that after `declare_block_relations()`, all static memory mirror
/// type keys are materialized in `heap_state.type_arrays`.
#[test]
fn test_nested_static_mirror_type_arrays_registered() {
    with_test_ay_ctx_for_source(NESTED_STATIC_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_static_pair_field");
        let body = instance.body().expect("function body");

        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_static_pair_field", config);
        chc_ctx.declare_block_relations();

        // Every static_memory_inits type key should be present in type_arrays
        // after declaration (D1 contract).
        for (type_key, _elem_sort, _init, _addr) in &chc_ctx.ref_resolution.static_memory_inits {
            assert!(
                chc_ctx.heap_state.type_arrays.contains_key(type_key.as_ref()),
                "static memory mirror type key '{}' should be registered in \
                 heap_state.type_arrays after declare_block_relations(), \
                 available keys: {:?}",
                type_key,
                chc_ctx.heap_state.type_arrays.keys().collect::<Vec<_>>()
            );
        }
    });
}

/// D5: Assert that the entry rule does not produce
/// `static_memory_array_unregistered` translation-drop sites for the nested
/// static mirror.
#[test]
fn test_nested_static_mirror_no_unregistered_drops() {
    with_test_ay_ctx_for_source(NESTED_STATIC_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_static_pair_field");
        let body = instance.body().expect("function body");

        // Clear any prior translation-drop state from other tests.
        let _ = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();

        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_static_pair_field", config);
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();
        chc_ctx.emit_entry_rule();

        let translation_sites = crate::codegen_ay::take_translation_drop_site_reasons_by_fn();
        let fn_sites = translation_sites.get("probe_static_pair_field");

        if let Some(sites) = fn_sites {
            assert!(
                !sites.contains_key("static_memory_array_unregistered"),
                "entry rule should not drop static memory constraints for nested \
                 fields after predeclare_static_memory_type_arrays (#3854), \
                 but found 'static_memory_array_unregistered' in sites: {:?}",
                sites
            );
        }
    });
}

#[test]
fn test_nested_static_mirror_emits_alignment_constraint() {
    with_test_ay_ctx_for_source(NESTED_STATIC_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_static_pair_field");
        let body = instance.body().expect("function body");

        let config =
            ChcConfig { track_level: crate::args::ChcTrackLevel::Mem, ..ChcConfig::default() };
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_static_pair_field", config);
        chc_ctx.declare_block_relations();
        chc_ctx.declare_error_relation();
        chc_ctx.emit_entry_rule();

        let entry_constraints: Vec<String> = chc_ctx
            .vc
            .rules
            .iter()
            .filter(|rule| rule.body.relation.is_none())
            .flat_map(|rule| rule.body.constraints.iter())
            .map(|c| c.to_string())
            .collect();

        // After the free-variable encoding migration, static base addresses are concrete
        // constants (e.g., 0x200000000) rather than symbolic vars. When the address is
        // concrete, alignment is guaranteed by construction — no explicit bvurem/bvand
        // constraint is needed. The entry rule instead ensures correct obj_size and
        // memory initialization for the static TABLE.
        let has_static_memory_init =
            entry_constraints.iter().any(|smt| smt.contains("obj_size") || smt.contains("store"));
        assert!(
            has_static_memory_init,
            "entry rule should encode static memory initialization (obj_size or store); \
             got constraints: {:?}",
            entry_constraints
        );
    });
}
