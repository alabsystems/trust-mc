// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Shared helpers for pointer-wrapper misc-dispatch regression tests.
//!
//! Split from `test_call_dispatch_misc_pointer_wrappers.rs` (D4 of #4010).

#![allow(clippy::unwrap_used)]

use super::common::*;
use trust_mc_core::decl::Decl;

pub(super) fn mir_to_chc_default(
    tcx: TyCtxt<'_>,
    body: &rustc_public::mir::Body,
    fn_name: &str,
) -> trust_mc_core::chc::ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig::default(),
    )
}

pub(super) fn assert_source_has_no_inferable_summaries(
    source: &str,
    probe_suffix: &str,
    summary_predicate: impl Fn(&str) -> bool + Send + Sync,
    context: &str,
) {
    with_test_ay_ctx_for_source(source, |ctx| {
        let instance = find_instance_by_suffix(ctx.tcx, probe_suffix);
        let body = instance.body().expect("function body");
        let vc = mir_to_chc_default(ctx.tcx, &body, probe_suffix);

        let inferable_decls: Vec<_> = vc
            .decls
            .iter()
            .filter_map(|decl| match decl {
                Decl::Fun { name, .. } if name.starts_with("P_inf_") && summary_predicate(name) => {
                    Some(name.as_str())
                }
                _ => None,
            })
            .collect();

        assert!(inferable_decls.is_empty(), "{context}, found: {inferable_decls:?}");
    });
}
