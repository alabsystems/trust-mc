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

use std::collections::HashMap;

use super::common::*;

fn referenced_static_locals(body: &rustc_public::mir::Body) -> HashMap<String, usize> {
    use rustc_public::mir::alloc::GlobalAlloc;
    use rustc_public::mir::{Operand, Rvalue, StatementKind};
    use rustc_public::ty::{ConstantKind, TyConstKind};

    let mut locals = HashMap::new();

    for bb in &body.blocks {
        for stmt in &bb.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                continue;
            };
            let Operand::Constant(const_op) = (match rhs {
                Rvalue::Use(op) => op,
                _ => continue,
            }) else {
                continue;
            };

            let provenance = match const_op.const_.kind() {
                ConstantKind::Allocated(alloc) if !alloc.provenance.ptrs.is_empty() => {
                    alloc.provenance.clone()
                }
                ConstantKind::Ty(ty_const) => match ty_const.kind() {
                    TyConstKind::Value(_, alloc) if !alloc.provenance.ptrs.is_empty() => {
                        alloc.provenance.clone()
                    }
                    _ => continue,
                },
                _ => continue,
            };

            let alloc_id = provenance.ptrs[0].1.0;
            let GlobalAlloc::Static(static_def) = GlobalAlloc::from(alloc_id) else {
                continue;
            };
            let static_name = {
                use rustc_public::CrateDef;
                static_def.name().clone()
            };
            locals.insert(static_name, lhs.local);
        }
    }

    locals
}

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

        // There should be u8 memory inits for the "FOO" string bytes.
        let u8_inits: Vec<_> = chc_ctx
            .ref_resolution
            .static_memory_inits
            .iter()
            .filter(|(tk, _, _, _)| &**tk == "u8")
            .collect();
        assert!(
            u8_inits.len() >= 3,
            "should have at least 3 u8 memory inits for 'FOO' bytes, got {}",
            u8_inits.len()
        );
    });
}
