// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The same dropped-write regression as `interior_pointer_store_modeling`, but on
//! a module the PRODUCTION path built.
//!
//! `interior_pointer_store_modeling` constructs its IR with `ModuleBuilder`, which
//! proves the translator's logic but not that the compiler ever hands it this
//! shape. The fixture here is a verbatim `-Ztrust-dump=native-bundle` artifact
//! emitted by `trustc` from
//!
//! ```ignore
//! pub struct S { pub a: u32, pub b: u32 }
//! #[inline(never)]
//! pub fn stale_struct(seed: u32) -> u32 {
//!     let mut s = S { a: 1, b: seed };
//!     let r = &mut s.a;
//!     *r = 0;
//!     100 / s.a
//! }
//! ```
//!
//! At run time `s.a` is 0, so `100 / s.a` divides by zero and the divide-by-zero
//! obligation MUST be refutable. Before the interior-pointer provenance fix the
//! `Store` through `BorrowMut(GEP(alloca, 0))` was dropped, the readback folded to
//! the pre-store `1`, and the CHC discharged the obligation — a false PROVE of a
//! function that always panics.

use trust_ir::Module;
use trust_ir::value::FuncId;
use trust_mc_core::chc::ChcVc;
use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;
use trust_mc_trust_bmc::{TranslateOptions, trust_ir_function_to_chc_translation_output};

const BUNDLE: &str = include_str!("fixtures/stale_struct_native_bundle.json");

fn lowered_module() -> Module {
    let bundle: serde_json::Value =
        serde_json::from_str(BUNDLE).expect("the dumped native bundle is valid JSON");
    serde_json::from_value(bundle["module"].clone())
        .expect("the dumped module deserializes into trust_ir::Module")
}

/// How many `error`-head rules are UNCONDITIONALLY reachable — every constraint
/// folds to the constant `true`.
///
/// `stale_struct`'s divide-by-zero check is entirely literal (`100 / s.a` with
/// `s.a` written from a constant), so with the write modeled its error rule folds
/// to `!((0 == 0) == false)` = true and this is at least 1. With the write dropped
/// the divisor folds to the PRE-store `1`, the rule becomes `!((1 == 0) == false)`
/// = false, and the count is 0 — the obligation is discharged. Rules that stay
/// symbolic (the second, `seed`-dependent check) are counted neither way.
fn unconditionally_reachable_error_rules(vc: &ChcVc) -> usize {
    let mut saw_error_rule = false;
    let mut reachable = 0;
    for rule in &vc.rules {
        if rule.head.name.as_str() != "error" {
            continue;
        }
        saw_error_rule = true;
        if rule.body.constraints.iter().all(|c| try_eval_to_bool(c) == Some(true)) {
            reachable += 1;
        }
    }
    assert!(saw_error_rule, "the division must emit an error rule");
    reachable
}

/// The lowering really does produce the shape the fix targets: an `Alloca` seeded
/// by a direct `Store`, a `GEP` at a constant lane, a `BorrowMut` of that address,
/// a `ValidBorrow`-annotated `Store` through the borrow, and a `Load` back off the
/// SAME alloca. If the bridge ever stops emitting this, the regression test below
/// silently stops testing anything — so assert the shape.
#[test]
fn the_lowered_module_still_stores_through_an_interior_pointer() {
    use trust_ir::inst::Inst;

    let module = lowered_module();
    let func = module
        .functions
        .iter()
        .find(|f| f.name.contains("stale_struct"))
        .expect("the dumped module defines stale_struct");

    let mut alloca = None;
    let mut lane_gep = None;
    let mut borrow = None;
    let mut stored_through_borrow = false;
    let mut reloaded_the_alloca = false;

    for block in &func.blocks {
        for node in &block.body {
            match &node.inst {
                Inst::Alloca { .. } => alloca = node.results.first().copied(),
                Inst::GEP { base, .. } if Some(*base) == alloca => {
                    lane_gep = node.results.first().copied();
                }
                Inst::BorrowMut { ptr } if Some(*ptr) == lane_gep => {
                    borrow = node.results.first().copied();
                }
                Inst::Store { ptr, .. } if Some(*ptr) == borrow => stored_through_borrow = true,
                Inst::Load { ptr, .. } if Some(*ptr) == alloca => reloaded_the_alloca = true,
                _ => {}
            }
        }
    }

    assert!(alloca.is_some(), "the struct local must be spilled to an alloca");
    assert!(lane_gep.is_some(), "`&mut s.a` must lower to a GEP off that alloca");
    assert!(borrow.is_some(), "`&mut s.a` must lower to a BorrowMut of that GEP");
    assert!(stored_through_borrow, "`*r = 0` must be a Store through the borrow");
    assert!(reloaded_the_alloca, "`s.a` must be read back off the SAME alloca");
}

/// THE PRODUCTION-PATH REGRESSION. `stale_struct` always divides by zero, so the
/// obligation must NOT be discharged.
#[test]
fn the_divide_by_zero_in_the_lowered_module_is_not_falsely_proved() {
    let module = lowered_module();
    let func = module
        .functions
        .iter()
        .position(|f| f.name.contains("stale_struct"))
        .expect("the dumped module defines stale_struct");

    let out = trust_ir_function_to_chc_translation_output(
        &module,
        FuncId::new(func as u32),
        &TranslateOptions::default(),
    )
    .expect("stale_struct translates");

    assert!(
        unconditionally_reachable_error_rules(&out.vc) >= 1,
        "FALSE PROVE: `100 / s.a` was discharged even though `*(&mut s.a) = 0` makes the \
         divisor zero — the through-borrow store was dropped and the readback folded to the \
         pre-store `1`"
    );
    assert!(
        out.diagnostics.is_empty(),
        "the through-borrow store is modeled exactly, so nothing should fail closed: {:?}",
        out.diagnostics
    );
}
