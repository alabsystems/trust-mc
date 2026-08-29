// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! `format!` builds its argument list with `InsertElement`, and that used to fail
//! closed.
//!
//! The unit tests in `src/tests.rs` prove the translator's `InsertElement` logic
//! on hand-built IR. They do NOT prove the compiler ever hands it this shape. The
//! fixture here is a verbatim `-Ztrust-dump=native-bundle` artifact emitted by
//! `trustc` (profile `unix_hardened`, `-Ztrust-verify-level=2`) from
//!
//! ```ignore
//! pub struct Lit(pub bool, pub String);
//!
//! pub fn lit_str(l: &Lit) -> String {
//!     if l.0 { l.1.clone() } else { format!("(not {})", l.1) }
//! }
//! ```
//!
//! which is a line-for-line replica of `ny_cert::alethe_emit::lit_str`. The single
//! format argument lowers to ONE `InsertElement` at the CONSTANT index `0` into a
//! `[core::fmt::rt::Argument; 1]`, and before the `InsertElement` arm existed that
//! one instruction emitted an UNCONDITIONALLY REACHABLE error rule — the whole
//! function's panic-freedom obligation was unprovable by construction.
//!
//! This is not a synthetic worry: on the `ny-cert` strict gate this exact
//! construct was the largest named fail-closed family, blocking 18 obligations
//! across 41 sites (5 `thiserror` `Display::fmt` impls plus `lit_str`,
//! `StepWriter::assume`, `certz::qpair_lean`, `Rat::to_clean_string`, …), with the
//! per-function site count equal to the number of format arguments.

use trust_ir::Module;
use trust_ir::inst::Inst;
use trust_ir::ty::Ty;
use trust_ir::value::FuncId;
use trust_mc_trust_bmc::{
    TranslateOptions, TrustIrChcUnsupportedReason, trust_ir_function_to_chc_translation_output,
};

const BUNDLE: &str = include_str!("fixtures/format_args_insert_element_native_bundle.json");

fn lowered_module() -> Module {
    let bundle: serde_json::Value =
        serde_json::from_str(BUNDLE).expect("the dumped native bundle is valid JSON");
    serde_json::from_value(bundle["module"].clone())
        .expect("the dumped module deserializes into trust_ir::Module")
}

fn lit_str_id(module: &Module) -> FuncId {
    let index = module
        .functions
        .iter()
        .position(|f| f.name == "lit_str")
        .expect("the dumped module defines lit_str");
    FuncId::new(index as u32)
}

/// The lowering really does produce the shape the fix targets: an `InsertElement`
/// into a fixed-size array whose index operand is defined by a `Const`. If the
/// bridge ever stops emitting this, the regression test below silently stops
/// testing anything — so assert the shape.
#[test]
fn format_args_still_lower_to_a_constant_index_insert_element() {
    let module = lowered_module();
    let func = module.function_by_id(lit_str_id(&module)).expect("lit_str resolves");

    let mut constant_ids = Vec::new();
    let mut found = false;
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::Const { .. } = &node.inst {
                constant_ids.extend(node.results.iter().map(|r| r.index()));
            }
            if let Inst::InsertElement { ty, index, .. } = &node.inst {
                assert!(
                    matches!(ty, Ty::Array(_, len) if *len <= 256),
                    "the format-argument list is a small fixed-size array, got {ty:?}"
                );
                assert!(
                    constant_ids.contains(&index.index()),
                    "the format-argument index must be a compile-time constant defined \
                     before the write"
                );
                found = true;
            }
        }
    }

    assert!(
        found,
        "`format!` must still build its argument array with `InsertElement` — the fixture \
         no longer exercises the construct this file guards"
    );
}

/// THE PRODUCTION-PATH REGRESSION. `lit_str`'s single `InsertElement` must be
/// modeled, not lowered to an unconditionally reachable error rule.
///
/// Pre-fix this counted exactly 1 `AggregateUpdate` — the value the strict
/// `ny-cert` gate reported for `ny_cert__alethe_emit__lit_str`
/// (`1 unsupported trust_ir construct(s) … (constructs: AggregateUpdate)`).
#[test]
fn the_format_argument_write_no_longer_fails_closed() {
    let module = lowered_module();
    let output = trust_ir_function_to_chc_translation_output(
        &module,
        lit_str_id(&module),
        &TranslateOptions::default(),
    )
    .expect("lit_str translates");

    let aggregate_updates = output
        .diagnostics
        .iter()
        .filter(|d| d.reason == TrustIrChcUnsupportedReason::AggregateUpdate)
        .count();

    assert_eq!(
        aggregate_updates, 0,
        "the constant-index format-argument write is exactly expressible; it must not emit an \
         unconditionally reachable error rule. Remaining diagnostics: {:?}",
        output.diagnostics
    );
}
