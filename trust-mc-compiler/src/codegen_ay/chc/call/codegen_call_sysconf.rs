// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Direct `libc::sysconf` call handling for CHC.
//!
//! `sysconf` is an environment query with no Rust-visible memory side effects.
//! Model the return as nondeterministic rather than sending the call through the
//! generic undefined-foreign path, which introduces an `error` rule.

use super::super::ChcCtx;
use super::super::chc_call_context::DispatchCallContext;
use super::super::codegen_call_coerce::CallCoerce;
use super::super::codegen_rules::CodegenRules;

/// The path this module models. Shared with the obligation-free walk so the
/// two cannot drift: the walk may only clear a body-less callee that the
/// ENCODER actually models as obligation-free.
pub(in crate::codegen_ay) fn is_modeled_sysconf_path(path: &str) -> bool {
    path == "libc::sysconf"
}

pub(in crate::codegen_ay::chc) trait CallDispatchSysconf {
    fn try_dispatch_call_sysconf(&mut self, dcx: &DispatchCallContext<'_>) -> bool;
}

impl<'tcx, 'body> CallDispatchSysconf for ChcCtx<'tcx, 'body> {
    fn try_dispatch_call_sysconf(&mut self, dcx: &DispatchCallContext<'_>) -> bool {
        let Some(target) = dcx.target else {
            return false;
        };
        let callee_path = dcx.callee_path.clone().or_else(|| self.resolve_callee_path(dcx.func));
        if !callee_path.as_deref().is_some_and(is_modeled_sysconf_path) || dcx.args.len() != 1 {
            return false;
        }

        let dest_local = dcx.destination.local;
        let new_output_args = self.build_output_args(dcx.modified_locals, &[dest_local]);
        self.emit_goto_rule_extra(
            dcx.from_app,
            *target,
            &new_output_args,
            dcx.stmt_constraints,
            None,
        );
        true
    }
}
