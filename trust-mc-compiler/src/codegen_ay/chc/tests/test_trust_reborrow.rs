// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Trust toolchain: `Rvalue::Reborrow` fails closed (see `trust_reborrow.rs`).

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use rustc_public::mir::{Mutability, Rvalue, StatementKind};

use super::common::*;
use crate::codegen_ay::chc::codegen_ctx::{FallbackSoundness, fallback_soundness};
use crate::codegen_ay::chc::trust_reborrow::{REBORROW_UNSUPPORTED, body_has_reborrow};
use crate::rustc_compat::mir_statement;

const SOURCE: &str = r#"
    #![allow(dead_code)]
    pub fn probe_reborrow(x: u32) -> u32 { x }
"#;

#[test]
fn test_reborrow_reason_is_fail_close() {
    assert_eq!(fallback_soundness(REBORROW_UNSUPPORTED), FallbackSoundness::FailClose);
}

#[test]
fn test_translate_rvalue_reborrow_fails_closed() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_reborrow");
        let body = instance.body().expect("function body");
        let mut chc_ctx = ChcCtx::new(ctx.tcx, &body, "probe_reborrow", ChcConfig::default());
        assert!(!chc_ctx.recorded_reborrow_unsupported(), "a fresh context has recorded nothing");

        for mutability in [Mutability::Mut, Mutability::Not] {
            let ty = body.locals()[1].ty;
            let rvalue = Rvalue::Reborrow(ty, mutability, Place { local: 1, projection: vec![] });
            let before = chc_ctx.sound_fallback_count();
            let result =
                chc_ctx.translate_rvalue_with_modified(&rvalue, &HashSet::<usize>::new(), Some(0));
            assert!(result.is_none(), "Reborrow must not be encoded ({mutability:?})");
            assert_eq!(
                chc_ctx.sound_fallback_count(),
                before + 1,
                "Reborrow must record a fail-close sound fallback ({mutability:?})"
            );
            assert!(
                chc_ctx.recorded_reborrow_unsupported(),
                "helper contexts decline on the recorded flag ({mutability:?})"
            );
        }
    });
}

#[test]
fn test_body_has_reborrow_detects_assign() {
    with_test_ay_ctx_for_source(SOURCE, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, "probe_reborrow");
        let body = instance.body().expect("function body");
        assert!(!body_has_reborrow(&body));

        let mut with_reborrow = body.clone();
        let span = mir_span!(with_reborrow.blocks[0].terminator);
        let ty = with_reborrow.locals()[1].ty;
        let statement = mir_statement(
            StatementKind::Assign(
                Place { local: 0, projection: vec![] },
                Rvalue::Reborrow(ty, Mutability::Mut, Place { local: 1, projection: vec![] }),
            ),
            span,
        );
        with_reborrow.blocks[0].statements.push(statement);
        assert!(body_has_reborrow(&with_reborrow));
    });
}
