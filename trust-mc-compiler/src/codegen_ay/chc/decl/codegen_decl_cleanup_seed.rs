// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Cleanup chain analysis for CHC block relation declaration.
//!
//! Extracted from codegen_decl.rs per #4119. Determines which cleanup successor
//! blocks should be retained (relationized) during declaration. Part of #3945:
//! declaration runs before transition generation, so it sees raw MIR cleanup
//! edges for calls whose unwind edges are later suppressed or made redundant
//! by `transition_gen.rs`.

use std::collections::HashSet;

use rustc_public::mir::{Operand, TerminatorKind, UnwindAction};
use tracing::debug;

use crate::codegen_ay::shared::IntoOption;

use super::ChcCtx;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Returns whether a cleanup successor should stay relationized.
    ///
    /// Part of #3945: declaration runs before transition generation, so it sees
    /// raw MIR cleanup edges for calls whose unwind edges are later suppressed
    /// or made redundant by `transition_gen.rs`. Retaining those cleanup-only
    /// blocks relationizes orphan `Resume` tails and records spurious
    /// `resume_abort` translation drops. Keep cleanup chains only when the CHC
    /// encoding can actually reach them or when the cleanup path itself carries
    /// semantic effects that the direct call rule does not already model.
    pub(in crate::codegen_ay::chc) fn should_retain_cleanup_seed(
        &self,
        bb_idx: usize,
        term: &TerminatorKind,
    ) -> bool {
        match term {
            TerminatorKind::Assert { unwind: UnwindAction::Cleanup(cleanup_bb), .. } => {
                let retain = self.cleanup_chain_has_semantic_effects(*cleanup_bb);
                if !retain {
                    debug!(
                        bb_idx,
                        cleanup_bb = *cleanup_bb,
                        "CHC: dropping assert cleanup-only relation seed for inert cleanup chain (#3945)"
                    );
                }
                retain
            }
            TerminatorKind::Drop { unwind: UnwindAction::Cleanup(_), .. } => false,
            TerminatorKind::Call {
                func,
                args,
                target,
                unwind: UnwindAction::Cleanup(cleanup_bb),
                ..
            } => {
                let cleanup_has_semantic_effects =
                    self.cleanup_chain_has_semantic_effects(*cleanup_bb);
                if !cleanup_has_semantic_effects
                    && target.is_none()
                    && self.call_emits_direct_error(func)
                {
                    debug!(
                        bb_idx,
                        cleanup_bb = *cleanup_bb,
                        "CHC: dropping diverging panic cleanup-only relation seed for inert cleanup chain (#3945)"
                    );
                    return false;
                }
                if target.is_none() {
                    return true;
                }
                let retain = !self.definitely_suppresses_call_cleanup(func, args);
                if !retain {
                    debug!(
                        bb_idx,
                        cleanup_bb = *cleanup_bb,
                        "CHC: dropping cleanup-only relation seed for definitely dispatched normal-return call (#3945)"
                    );
                }
                retain
            }
            _ => false,
        }
    }

    /// Returns true when a cleanup chain contains semantically relevant work.
    ///
    /// Part of #3945: `Assert` terminators already emit a direct failure rule in
    /// `transition_gen.rs`. Their unwind cleanup chain only needs relationized
    /// blocks when it performs more than trivial drops before terminating in
    /// `Resume`/`Abort`; otherwise it only duplicates the direct assert-failure
    /// edge and creates spurious `resume_abort` translation drops.
    fn cleanup_chain_has_semantic_effects(&self, entry_bb: usize) -> bool {
        let mut seen = HashSet::new();
        let mut work = vec![entry_bb];

        while let Some(bb_idx) = work.pop() {
            if !seen.insert(bb_idx) {
                continue;
            }

            match &self.body.blocks[bb_idx].terminator.kind {
                TerminatorKind::Goto { target } => work.push(*target),
                TerminatorKind::Drop { place, target, unwind, .. } => {
                    let Some(drop_ty) = place.ty(self.body.locals()).into_option() else {
                        return true;
                    };
                    if !crate::codegen_ay::chc::rules::codegen_rules::transition_drop::ty_trivially_no_drop(drop_ty)
                    {
                        return true;
                    }
                    work.push(*target);
                    if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                        work.push(*cleanup_bb);
                    }
                }
                TerminatorKind::Call { func, target, unwind, .. } => {
                    if self
                        .resolve_callee_path(func)
                        .as_deref()
                        .is_some_and(|path| path.contains("Drop>::drop"))
                    {
                        if let Some(target) = target {
                            work.push(*target);
                        } else {
                            return true;
                        }
                        if let UnwindAction::Cleanup(cleanup_bb) = unwind {
                            work.push(*cleanup_bb);
                        }
                    } else {
                        return true;
                    }
                }
                TerminatorKind::Resume
                | TerminatorKind::Abort
                | TerminatorKind::Return
                | TerminatorKind::Unreachable => {}
                TerminatorKind::Assert { .. }
                | TerminatorKind::SwitchInt { .. }
                | TerminatorKind::InlineAsm { .. } => return true,
            }
        }

        false
    }

    fn definitely_suppresses_call_cleanup(&self, func: &Operand, args: &[Operand]) -> bool {
        self.detect_hashmap_stub(func, args).is_some()
            || self.detect_alloc_stub(func).is_some()
            || self.detect_stub(func).is_some()
            || self.detect_kani_hook(func).is_some()
            || self.detect_kani_intrinsic(func).is_some()
            || self.detect_kani_model(func).is_some()
            || self.is_unmarked_kani_cleanup_dispatch(func)
    }

    fn call_emits_direct_error(&self, func: &Operand) -> bool {
        self.detect_stub(func).is_some_and(crate::codegen_ay::stubs::StubKind::is_panic_error)
            || matches!(
                self.detect_kani_hook(func),
                Some(crate::kani_middle::kani_functions::KaniHook::Panic)
                    | Some(crate::kani_middle::kani_functions::KaniHook::UnsupportedCheck)
            )
    }

    fn is_unmarked_kani_cleanup_dispatch(&self, func: &Operand) -> bool {
        let Some(callee) =
            self.resolve_callee_path(func).or_else(|| self.resolve_fn_def_name(func))
        else {
            return false;
        };
        if !callee.contains("kani::") {
            return false;
        }
        matches!(callee.rsplit("::").next(), Some("safety_check") | Some("safety_check_no_assume"))
            || callee.contains("any_raw_internal")
            || callee.contains("any_raw_array")
            || (callee.contains("kani::Arbitrary") && callee.rsplit("::").next() == Some("any"))
    }
}
