// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Kani parity: reject mutual recursion under `#[kani::recursion]` contracts.
//!
//! The per-function REENTRY tracker that `#[kani::recursion]` installs handles
//! DIRECT recursion only. When the checked function `f` calls `g`, and `g` also
//! carries a contract with `#[kani::recursion]` and calls back into `f`, the
//! contract instrumentation is unsound, and Kani refuses the crate at compile
//! time (`kani-compiler/src/kani_middle/transform/contracts.rs`,
//! `check_mutual_recursion`). trust-mc had no such check, so the CHC walker
//! nested the contract closures of the cycle until the driver watchdog fired
//! (`expected/function-contract/mutual_recursion_unsound.rs`: 80 s, no verdict,
//! where Kani prints the error in 0.1 s).
//!
//! The detection mirrors Kani exactly, including its limit: one level of
//! indirection (`f -> g -> f`). A callee with a contract but WITHOUT
//! `#[kani::recursion]` is replaced by its contract abstraction, so it closes no
//! cycle and is not reported.

use crate::kani_middle::attributes::KaniAttributes;
use rustc_middle::ty::TyCtxt;
use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{Body, TerminatorKind};
use rustc_public::rustc_internal;
use rustc_public::ty::{FnDef, RigidTy, Span, TyKind};

/// A detected `checked -> callee -> checked` cycle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct MutualRecursion {
    /// The callee that closes the cycle.
    pub callee: FnDef,
    /// Span of the call in the checked function.
    pub span: Span,
}

/// The callees of `fn_def` (whose MIR is `body`) that close a one-level mutual
/// recursion cycle. `is_recursive_contract` decides whether a callee carries a
/// contract with `#[kani::recursion]`; it is a parameter so the call-graph
/// logic can be tested on its own.
pub(crate) fn find_mutual_recursion(
    fn_def: FnDef,
    body: &Body,
    is_recursive_contract: impl Fn(FnDef) -> bool,
) -> Vec<MutualRecursion> {
    let mut found: Vec<MutualRecursion> = Vec::new();
    for bb in body.blocks.iter() {
        let TerminatorKind::Call { func, .. } = &bb.terminator.kind else { continue };
        let Ok(func_ty) = func.ty(body.locals()) else { continue };
        let TyKind::RigidTy(RigidTy::FnDef(callee_def, callee_args)) = func_ty.kind() else {
            continue;
        };
        // Direct recursion is what REENTRY handles; not a cycle through a callee.
        if callee_def.def_id() == fn_def.def_id() || !is_recursive_contract(callee_def) {
            continue;
        }
        // One error per callee, as Kani reports it.
        if found.iter().any(|m| m.callee.def_id() == callee_def.def_id()) {
            continue;
        }
        let Ok(callee_instance) = Instance::resolve(callee_def, &callee_args) else { continue };
        let Some(callee_body) = callee_instance.body() else { continue };
        let calls_back = callee_body.blocks.iter().any(|callee_bb| {
            let TerminatorKind::Call { func: callee_func, .. } = &callee_bb.terminator.kind else {
                return false;
            };
            let Ok(ty) = callee_func.ty(callee_body.locals()) else { return false };
            matches!(ty.kind(), TyKind::RigidTy(RigidTy::FnDef(def, _)) if def.def_id() == fn_def.def_id())
        });
        if calls_back {
            found.push(MutualRecursion { callee: callee_def, span: mir_span!(bb.terminator) });
        }
    }
    found
}

/// Kani's diagnostic, word for word (the corpus `.expected` file matches it).
pub(crate) fn mutual_recursion_message(fn_name: &str, callee_name: &str) -> String {
    format!(
        "`#[kani::recursion]` is used on `{fn_name}`, which calls `{callee_name}` that calls \
         back to `{fn_name}`. Mutual recursion is not supported by contract verification and \
         produces unsound results. Only direct recursion (a function calling itself) is handled \
         correctly."
    )
}

/// Emit Kani's compile error for every mutual-recursion cycle through the
/// checked function `fn_def`, then stop compilation if any was found.
///
/// Stopping is deliberate: codegen of this shape does not terminate in useful
/// time, and Kani's verdict for it IS the compile error.
pub(crate) fn check_mutual_recursion(tcx: TyCtxt, fn_def: FnDef, body: &Body) {
    let cycles = find_mutual_recursion(fn_def, body, |callee| {
        let attrs = KaniAttributes::for_def_id(tcx, callee.def_id());
        attrs.has_contract() && attrs.has_recursion()
    });
    if cycles.is_empty() {
        return;
    }
    let fn_name = tcx.def_path_str(rustc_internal::internal(tcx, fn_def.def_id()));
    for cycle in &cycles {
        let callee_name = tcx.def_path_str(rustc_internal::internal(tcx, cycle.callee.def_id()));
        let span = rustc_internal::internal(tcx, cycle.span);
        tcx.dcx().span_err(span, mutual_recursion_message(&fn_name, &callee_name));
    }
    tcx.dcx().abort_if_errors();
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used, clippy::panic)]
    use super::*;
    use rustc_public::{CompilerError, run_with_tcx};
    use std::sync::atomic::{AtomicU64, Ordering};
    use tempfile::TempDir;

    /// The corpus expectation for `expected/function-contract/mutual_recursion_unsound.rs`.
    const KANI_EXPECTED: &str = "error: `#[kani::recursion]` is used on `mutual_a`, which calls \
        `mutual_b` that calls back to `mutual_a`. Mutual recursion is not supported by contract \
        verification and produces unsound results.";

    #[test]
    fn message_matches_kani_expected_output() {
        let line = format!("error: {}", mutual_recursion_message("mutual_a", "mutual_b"));
        assert!(line.starts_with(KANI_EXPECTED), "{line}");
    }

    const SOURCE: &str = r#"#![allow(dead_code, unconditional_recursion)]
#![feature(register_tool)]
#![register_tool(kanitool)]

#[kanitool::checked_with = "c"]
#[kanitool::recursion]
pub fn mutual_a(x: u32) -> u32 { if x == 0 { 0 } else { mutual_b(x - 1) } }

#[kanitool::checked_with = "c"]
#[kanitool::recursion]
pub fn mutual_b(x: u32) -> u32 { if x == 0 { 0 } else { mutual_a(x - 1) } }

// A contract without #[kani::recursion] is replaced by its abstraction: no cycle.
#[kanitool::checked_with = "c"]
pub fn replaced(x: u32) -> u32 { if x == 0 { 0 } else { calls_replaced(x - 1) } }
#[kanitool::checked_with = "c"]
#[kanitool::recursion]
pub fn calls_replaced(x: u32) -> u32 { if x == 0 { 0 } else { replaced(x - 1) } }

// Direct recursion is what REENTRY handles.
#[kanitool::checked_with = "c"]
#[kanitool::recursion]
pub fn direct(x: u32) -> u32 { if x == 0 { 0 } else { direct(x - 1) } }

// Two levels of indirection: Kani detects one level only, and so do we.
#[kanitool::checked_with = "c"]
#[kanitool::recursion]
pub fn ring_a(x: u32) -> u32 { if x == 0 { 0 } else { ring_b(x - 1) } }
#[kanitool::checked_with = "c"]
#[kanitool::recursion]
pub fn ring_b(x: u32) -> u32 { if x == 0 { 0 } else { ring_c(x - 1) } }
#[kanitool::checked_with = "c"]
#[kanitool::recursion]
pub fn ring_c(x: u32) -> u32 { if x == 0 { 0 } else { ring_a(x - 1) } }
"#;

    fn with_tcx<F>(callback: F)
    where
        F: for<'tcx> FnOnce(TyCtxt<'tcx>) + Send,
    {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let dir = TempDir::new().unwrap();
        let src = dir.path().join("lib.rs");
        std::fs::write(&src, SOURCE).unwrap();
        let id = COUNTER.fetch_add(1, Ordering::SeqCst);
        let out = dir.path().join("out");
        std::fs::create_dir_all(&out).unwrap();
        let args = vec![
            "rustc".to_string(),
            src.to_string_lossy().into_owned(),
            "--crate-type=lib".to_string(),
            format!("--crate-name=mutual_recursion_test_{id}"),
            "--out-dir".to_string(),
            out.to_string_lossy().into_owned(),
            "--edition=2021".to_string(),
            "-C".to_string(),
            "opt-level=0".to_string(),
            "-Z".to_string(),
            "inline-mir=no".to_string(),
        ];
        let result = run_with_tcx!(&args, |tcx| {
            callback(tcx);
            std::ops::ControlFlow::<(), ()>::Continue(())
        });
        assert!(
            result.is_ok() || matches!(result, Err(CompilerError::Skipped)),
            "rustc_public run failed: {result:?}"
        );
    }

    /// The local function `name`, with the crate item it was found as (the
    /// frozen nightly has no `FnDef -> CrateItem` conversion).
    fn fn_def(name: &str) -> (FnDef, rustc_public::CrateItem) {
        rustc_public::all_local_items()
            .into_iter()
            .find_map(|item| {
                let TyKind::RigidTy(RigidTy::FnDef(def, _)) = item.ty().kind() else { return None };
                (item.name() == name || item.name().ends_with(&format!("::{name}")))
                    .then_some((def, item))
            })
            .unwrap_or_else(|| panic!("missing fn {name}"))
    }

    fn cycles_through(tcx: TyCtxt<'_>, name: &str) -> Vec<String> {
        let (def, item) = fn_def(name);
        let body = Instance::try_from(item).unwrap().body().unwrap();
        find_mutual_recursion(def, &body, |callee| {
            let attrs = KaniAttributes::for_def_id(tcx, callee.def_id());
            attrs.has_contract() && attrs.has_recursion()
        })
        .into_iter()
        .map(|m| m.callee.name())
        .collect()
    }

    #[test]
    fn detects_one_level_mutual_recursion_both_ways() {
        with_tcx(|tcx| {
            let a = cycles_through(tcx, "mutual_a");
            assert_eq!(a.len(), 1, "{a:?}");
            assert!(a[0].ends_with("mutual_b"), "{a:?}");
            let b = cycles_through(tcx, "mutual_b");
            assert!(b.len() == 1 && b[0].ends_with("mutual_a"), "{b:?}");
        });
    }

    #[test]
    fn ignores_direct_recursion_replaced_callees_and_deeper_rings() {
        with_tcx(|tcx| {
            assert!(cycles_through(tcx, "direct").is_empty());
            // `replaced` has no #[kani::recursion], so checking `calls_replaced`
            // sees no recursive-contract callee.
            assert!(cycles_through(tcx, "calls_replaced").is_empty());
            // f -> g -> h -> f is past Kani's one-level detection.
            assert!(cycles_through(tcx, "ring_a").is_empty());
        });
    }
}
