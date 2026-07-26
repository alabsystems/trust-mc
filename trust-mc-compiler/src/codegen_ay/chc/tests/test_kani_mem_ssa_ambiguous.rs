// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Regression test for #3958: `try_resolve_mir_ptr_to_local()` must reject
//! ambiguous pointer locals that have multiple different source assignments.
//!
//! The bug: the resolver returned the **first** `AddressOf`/`Ref` assignment
//! without checking if the same pointer local was reassigned to a different
//! source local later. This could feed the wrong SSA field value into the
//! validity predicate hint path.
//!
//! The fix: collect all candidate source locals, deduplicate, and return
//! `Some(local)` only when the candidate set is uniquely one local.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used)]

use super::common::*;

// =============================================================================
// Probe sources
// =============================================================================

/// Source with a function that reassigns a pointer local to two different
/// source locals before calling kani::mem::can_dereference.
/// MIR should produce: `_p = &raw const _a; ... _p = &raw const _b;`
const AMBIGUOUS_PTR_SOURCE: &str = r#"
    #![allow(dead_code)]

    mod kani {
        pub mod mem {
            #[inline(never)]
            pub fn can_dereference<T>(_ptr: *const T) -> bool {
                true
            }
        }
    }

    /// Pointer local _p is assigned to two different source locals.
    /// try_resolve_mir_ptr_to_local should return None (ambiguous).
    pub fn probe_ambiguous_ptr(cond: bool) -> bool {
        let a: bool = true;
        let b: bool = false;
        let p: *const bool;
        if cond {
            p = &raw const a;
        } else {
            p = &raw const b;
        }
        kani::mem::can_dereference(p)
    }

    /// Pointer local is assigned to the same source local twice.
    /// try_resolve_mir_ptr_to_local should return Some (unique).
    pub fn probe_unique_ptr() -> bool {
        let a: bool = true;
        let p: *const bool = &raw const a;
        // Even if MIR has two refs to `a`, they're the same source local.
        kani::mem::can_dereference(p)
    }
"#;

// =============================================================================
// Tests
// =============================================================================

/// #3958 regression: When a pointer local has assignments from two different
/// source locals, `try_resolve_mir_ptr_to_local` must return `None`.
#[test]
fn test_kani_mem_ssa_ambiguous_ptr_returns_none() {
    with_test_ay_ctx_for_source(AMBIGUOUS_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_ambiguous_ptr");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_ambiguous_ptr", ChcConfig::default());

        // Find the kani::mem::can_dereference call in MIR to get the args
        let mut found_call = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
            {
                // Check if this is a kani::mem call
                if let Some(def) = func_def_path(ctx.tcx, func) {
                    if def.contains("can_dereference") {
                        let result = chc_ctx.try_resolve_mir_ptr_to_local(args);
                        assert!(
                            result.is_none(),
                            "try_resolve_mir_ptr_to_local should return None for \
                             ambiguous pointer (two different source locals), got {:?}",
                            result
                        );
                        found_call = true;
                    }
                }
            }
        }
        assert!(found_call, "Should find kani::mem::can_dereference call in MIR");
    });
}

/// Sanity check: When a pointer local has a unique source local,
/// `try_resolve_mir_ptr_to_local` should return `Some`.
#[test]
fn test_kani_mem_ssa_unique_ptr_returns_some() {
    with_test_ay_ctx_for_source(AMBIGUOUS_PTR_SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_unique_ptr");
        let body = instance.body().expect("function body");

        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_unique_ptr", ChcConfig::default());

        let mut found_call = false;
        for block in &body.blocks {
            if let rustc_public::mir::TerminatorKind::Call { func, args, .. } =
                &block.terminator.kind
            {
                if let Some(def) = func_def_path(ctx.tcx, func) {
                    if def.contains("can_dereference") {
                        let result = chc_ctx.try_resolve_mir_ptr_to_local(args);
                        assert!(
                            result.is_some(),
                            "try_resolve_mir_ptr_to_local should return Some for \
                             unique pointer source local, got None"
                        );
                        found_call = true;
                    }
                }
            }
        }
        assert!(found_call, "Should find kani::mem::can_dereference call in MIR");
    });
}

/// Helper: Extract the def path of a function operand.
fn func_def_path(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    func: &rustc_public::mir::Operand,
) -> Option<String> {
    match func {
        rustc_public::mir::Operand::Constant(c) => match c.const_.ty().kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => {
                let internal_def = rustc_public::rustc_internal::internal(tcx, def.def_id());
                Some(tcx.def_path_str(internal_def))
            }
            _ => None,
        },
        _ => None,
    }
}
