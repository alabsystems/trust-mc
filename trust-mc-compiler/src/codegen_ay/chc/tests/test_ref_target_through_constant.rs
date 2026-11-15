// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The use-after-scope checks (`emit_ref_into_dead_storage_check`,
//! `try_resolve_deref_via_ref_targets`) read a ref target's local's
//! `StorageDead` as the death of the pointee. A target THROUGH a constant
//! pointer (`(*_2)` with `_2 = const &S`) names a static or constant memory,
//! which never dies (`ref_target_through_constant`).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;

const DEAD_STORAGE_PROBE: &str = r#"
    #![allow(dead_code)]
    static S: u32 = 5;

    pub fn probe_const_pointer() -> u32 {
        let p: *const u32 = &S;
        unsafe { *p }
    }

    pub fn probe_stack_reference(x: u32) -> u32 {
        let q = &x;
        let p: *const u32 = &*q;
        unsafe { *p }
    }
"#;

/// `let p: *const u32 = &S` is `p = &raw const (*_2)` with `_2 = const &S`.
/// The use-after-scope checks read `_2`'s `StorageDead` as the death of the
/// pointee and staged a constant-false obligation on every `*p` / `&*p`; a
/// target THROUGH a constant pointer names a static or constant memory, which
/// never dies (`ref_target_through_constant`). A reference to a stack local
/// is not such a target.
#[test]
fn test_target_through_a_constant_pointer_is_never_dead() {
    use rustc_public::mir::{Operand, ProjectionElem, Rvalue, StatementKind};
    with_test_ay_ctx_for_source(DEAD_STORAGE_PROBE, |ctx| {
        // The local each probe assigns its pointer's referent from.
        let source_local = |name: &str, want_constant: bool| {
            let body = find_instance_by_suffix(ctx.tcx, name).body().expect("body");
            let local = body
                .blocks
                .iter()
                .flat_map(|bb| &bb.statements)
                .find_map(|stmt| match &stmt.kind {
                    StatementKind::Assign(lhs, Rvalue::Use(Operand::Constant(_), ..))
                        if want_constant && lhs.projection.is_empty() =>
                    {
                        Some(lhs.local)
                    }
                    StatementKind::Assign(lhs, Rvalue::Ref(_, _, place))
                        if !want_constant && place.projection.is_empty() =>
                    {
                        Some(lhs.local)
                    }
                    _ => None,
                })
                .expect("the pointer's source local");
            (body, local)
        };
        let (body, constant) = source_local("probe_const_pointer", true);
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_const_pointer", ChcConfig::default());
        assert!(chc_ctx.ref_target_through_constant(constant, &[ProjectionElem::Deref]));
        assert!(!chc_ctx.ref_target_through_constant(constant, &[]), "the local's own storage");
        let (body, reference) = source_local("probe_stack_reference", false);
        let chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_stack_reference", ChcConfig::default());
        assert!(!chc_ctx.ref_target_through_constant(reference, &[ProjectionElem::Deref]));
    });
}
