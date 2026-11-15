// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! A bundled `core::mem::drop` whose body opens with a `Unit` constant is
//! SUMMARIZED. Checked on REAL bridge output, not hand-built IR.
//!
//! The fixture is `-Ztrust-dump=native-bundle` output from a trust stage-1
//! compiler (superproject `32b1cc59311e`, upstream baseline `2a01bd6f8ba2`)
//! for `pub fn p(v: std::sync::Arc<u32>) -> u8 { drop(v); 1 }`. Since upstream
//! 9f6141e78128 ("Initialize ZST results in MIR construction and lowering"),
//! drop shims assign `_0 = const ()`; the bridge lowers that to
//! `Const { Unit, PhantomData }` + `Copy` at the head of the bundled
//! `core::mem::drop::<alloc::sync::Arc<u32>>` body, whose remainder is
//! `Assert(true); Return`.
//!
//! `try_direct_call_summary`'s `Inst::Const` arm admitted only scalar types,
//! so the unit constant fell to the anonymous catch-all
//! (`unmodeled_instruction`/`Const`) and every caller through `mem::drop`
//! took the unconditional `UnsupportedDirectCallSummary` error rule —
//! panic-freedom of a plain `drop(arc)` demoted to unknown (the 13-test
//! sysroot-drop-reach family in the superproject's `tests/ui/trust`). A unit
//! constant has exactly one inhabitant, the zero-field aggregate the rest of
//! the interpreter already uses for `Ty::Unit`; modeling it is exact.

use trust_ir::Module;
use trust_ir::constant::Constant;
use trust_ir::inst::Inst;
use trust_ir::ty::Ty;
use trust_mc_trust_bmc::{
    CallSummaryOutcome, TranslateOptions, TrustIrChcUnsupportedReason,
    trust_ir_function_to_chc_translation_output,
};

const BUNDLE: &str = include_str!("fixtures/unit_const_drop_native_bundle.json");

const CALLER: &str = "p";
const CALLEE: &str = "core::mem::drop::<alloc::sync::Arc<u32>>";

fn module() -> Module {
    let bundle: serde_json::Value =
        serde_json::from_str(BUNDLE).expect("the dumped native bundle is valid JSON");
    serde_json::from_value(bundle["module"].clone())
        .expect("the dumped native bundle module deserializes")
}

#[test]
fn a_unit_const_drop_callee_is_summarized() {
    let module = module();
    let callee_fn = module
        .functions
        .iter()
        .find(|f| f.name == CALLEE)
        .expect("mem::drop is BUNDLED");
    // The lowering shape this regression pins: the callee's entry block opens
    // with the ZST return-place initialization as a unit constant + copy. If
    // the bridge stops emitting it, this test must be re-derived, not pass
    // vacuously.
    let entry = &callee_fn.blocks[callee_fn.entry.as_usize()];
    assert!(
        matches!(
            entry.body.first().map(|n| &n.inst),
            Some(Inst::Const { ty: Ty::Unit, value: Constant::PhantomData })
        ),
        "the callee must open with the unit constant: {:?}",
        entry.body.first().map(|n| &n.inst)
    );

    let caller_fn =
        module.functions.iter().find(|f| f.name == CALLER).expect("the caller is in the bundle");
    let options =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let output = trust_ir_function_to_chc_translation_output(&module, caller_fn.id, &options)
        .expect("the caller translates");

    let outcome = output
        .call_summary_census
        .iter()
        .find(|attempt| attempt.callee == CALLEE)
        .unwrap_or_else(|| {
            panic!("the census records the call to `{CALLEE}`: {:?}", output.call_summary_census)
        })
        .outcome
        .clone();
    assert_eq!(outcome, CallSummaryOutcome::Summarized, "diagnostics: {:?}", output.diagnostics);
    assert!(
        !output
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary),
        "no fail-closed call-summary error rule may remain: {:?}",
        output.diagnostics
    );
}
