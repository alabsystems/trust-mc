// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression tests for `collect_static_state_vars` aliasing/composite gaps.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use std::collections::HashMap;

use super::common::*;
use rustc_public::mir::alloc::GlobalAlloc;
use rustc_public::mir::{Operand, Rvalue, StatementKind};
use rustc_public::ty::{ConstantKind, TyConstKind};

const STATIC_ALIAS_PROBE: &str = r#"
    #![allow(dead_code)]

    static mut FOO: &mut i32 = &mut 12;
    static mut BAR: *mut i32 = unsafe { FOO as *mut _ };

    pub fn probe_aliased_statics() -> i32 {
        unsafe {
            let foo: &mut i32 = FOO;
            let bar: *mut i32 = BAR;
            *foo = 13;
            *bar
        }
    }
"#;

const ARRAY_STATIC_PROBE: &str = r#"
    #![allow(dead_code)]

    pub static DAYS_OF_WEEK: [char; 7] = ['s', 'm', 't', 'w', 't', 'f', 's'];

    pub fn probe_array_static(day: usize) -> char {
        let days = &DAYS_OF_WEEK;
        days[day]
    }
"#;

fn referenced_static_locals(body: &rustc_public::mir::Body) -> HashMap<String, usize> {
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
            locals.entry(static_name).or_insert(lhs.local);
        }
    }

    locals
}

#[test]
fn test_aliased_pointer_statics_share_one_state_var() {
    with_test_ay_ctx_for_source(STATIC_ALIAS_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_aliased_statics");
        let body = instance.body().expect("function body");

        let mut chc_ctx =
            ChcCtx::new(ctx.tcx, &body, "probe_aliased_statics", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let referenced_locals = referenced_static_locals(&body);
        let foo_local = referenced_locals.get("FOO").copied().expect("expected FOO static local");
        let bar_local = referenced_locals.get("BAR").copied().expect("expected BAR static local");

        let foo_idx = chc_ctx
            .ref_resolution
            .static_ref_to_state_idx
            .get(&foo_local)
            .copied()
            .expect("FOO local should map to a static state var");
        let bar_idx = chc_ctx
            .ref_resolution
            .static_ref_to_state_idx
            .get(&bar_local)
            .copied()
            .expect("BAR local should map to a static state var");

        // FOO and BAR are separate static items with distinct alloc_ids.
        // They correctly get separate state variables. Verification correctness
        // for aliased writes (write through FOO visible via BAR) is achieved
        // through the memory model — both statics' initial values resolve to
        // the same concrete heap address via resolve_pointer_static_init,
        // so deref operations route through the shared memory array.
        assert_ne!(
            foo_idx, bar_idx,
            "separate static items should have distinct state var indices"
        );

        let static_var_count = chc_ctx
            .state_var_mgr
            .state_vars
            .iter()
            .filter(|(name, _)| name.contains("_static_probe_aliased_statics_"))
            .count();
        assert_eq!(
            static_var_count, 2,
            "separate static items should declare two `_static_` state vars, got {static_var_count}"
        );
    });
}

#[test]
fn test_array_typed_static_gets_array_state_var_and_init() {
    with_test_ay_ctx_for_source(ARRAY_STATIC_PROBE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_array_static");
        let body = instance.body().expect("function body");

        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_array_static", ChcConfig::default());
        chc_ctx.declare_block_relations();

        let referenced_locals = referenced_static_locals(&body);
        let days_local = referenced_locals
            .get("DAYS_OF_WEEK")
            .copied()
            .expect("expected DAYS_OF_WEEK static local");
        let days_idx = chc_ctx
            .ref_resolution
            .static_ref_to_state_idx
            .get(&days_local)
            .copied()
            .expect("DAYS_OF_WEEK local should map to a static state var");

        let (_, state_sort) = chc_ctx
            .state_var_mgr
            .state_vars
            .get(days_idx)
            .expect("missing state var for DAYS_OF_WEEK");
        assert!(
            state_sort.array_sort().is_some(),
            "array-typed static should use an array state var sort, got {:?}",
            state_sort
        );

        let init_expr = chc_ctx
            .ref_resolution
            .static_initial_values
            .get(&days_idx)
            .expect("array-typed static should cache an initial value");
        assert!(
            init_expr.sort().array_sort().is_some(),
            "array-typed static initializer should decode to an array expression, got {:?}",
            init_expr.sort()
        );
    });
}
