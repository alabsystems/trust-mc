//! A bundled `-> !` callee is SUMMARIZED, and a call to it does not continue.
//! Checked on REAL bridge output, not hand-built IR.
//!
//! Both fixtures are `-Ztrust-dump=native-bundle` output from a trust stage-1
//! compiler (trust 98725f8d7d plus the change that adds this file). That compiler's
//! bridge ends every never-typed call site with `%c = const false; assume %c;
//! unreachable`.
//!
//! * `never_call_wrapper_native_bundle.json` holds
//!   `fn stop() -> ! { unsafe { c_exit(1) } }` and
//!   `pub fn inc(x: u32) -> u32 { if x == u32::MAX { stop(); } x + 1 }`. `c_exit`
//!   is a bodyless, non-unwinding `extern "C"` import that returns `!`. It is
//!   ABI-total, so the bridge emits no instruction for it and `stop` lowers to the
//!   tail alone.
//! * `never_call_panicking_native_bundle.json` holds the negative control,
//!   `fn stop_if(c: bool) -> ! { if c { panic!() } unsafe { c_exit(1) } }`, called
//!   from `g` the same way.
//!
//! Before 2026-09-27 `try_direct_call_summary` declined every callee with NO
//! return path (`returns_not_combinable`). The caller's call site then took the
//! unconditional `UnsupportedDirectCallSummary` error rule, so `inc` could never
//! be proved panic-free, although nothing in it can panic.
//!
//! The error-rule checks read the PER-BLOCK encoding
//! (`trust_ir_function_to_chc_translation_output_per_block`): since design step
//! 8e an acyclic caller like `inc` or `g` is translated by default into one
//! large-block query with no per-block relations, and the two encodings are
//! equisatisfiable (`translate_chc_large_block.rs`). The census and diagnostic
//! checks read the default translation, the one the verifier solves.

use trust_ir::Module;
use trust_ir::inst::Inst;
use trust_ir::value::BlockId;
use trust_mc_core::chc::ChcVc;
use trust_mc_core::chc_const_prop::eval::try_eval_to_bool;
use trust_mc_trust_bmc::{
    CallSummaryOutcome, ChcTranslationOutput, TranslateOptions, TrustIrChcUnsupportedReason,
    trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_per_block,
};

const WRAPPER_BUNDLE: &str = include_str!("fixtures/never_call_wrapper_native_bundle.json");
const PANICKING_BUNDLE: &str = include_str!("fixtures/never_call_panicking_native_bundle.json");

fn module(bundle_json: &str) -> Module {
    let bundle: serde_json::Value =
        serde_json::from_str(bundle_json).expect("the dumped native bundle is valid JSON");
    serde_json::from_value(bundle["module"].clone())
        .expect("the dumped native bundle module deserializes")
}

/// A caller's translations: the default one (what the verifier solves) and the
/// per-block one (which names each block's relation), plus the block that calls
/// the callee.
struct CallerTranslation {
    default: ChcTranslationOutput,
    per_block: ChcTranslationOutput,
    call_block: BlockId,
}

/// Translate `caller` in both encodings and find the block that calls `callee`.
/// It also asserts the lowering shape the fix relies on: the callee declares NO
/// result, and the call is followed by the never-continues tail.
fn translate_caller(module: &Module, caller: &str, callee: &str) -> CallerTranslation {
    let caller_fn =
        module.functions.iter().find(|f| f.name == caller).expect("the caller is in the bundle");
    let callee_fn =
        module.functions.iter().find(|f| f.name == callee).expect("the callee is BUNDLED");
    assert!(
        module.func_types[callee_fn.ty.as_usize()].returns.is_empty(),
        "a `-> !` callee lowers with no declared result"
    );
    let call_block = caller_fn
        .blocks
        .iter()
        .find(|block| {
            let insts: Vec<&Inst> = block.body.iter().map(|node| &node.inst).collect();
            matches!(
                insts.as_slice(),
                [.., Inst::Call { callee: c, .. }, Inst::Const { .. }, Inst::Assume { .. }, Inst::Unreachable]
                    if *c == callee_fn.id
            )
        })
        .unwrap_or_else(|| panic!("`{caller}` must call `{callee}` in a block that ends `assume false; unreachable`"))
        .id;
    let options =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let default = trust_ir_function_to_chc_translation_output(module, caller_fn.id, &options)
        .expect("the caller translates");
    let per_block =
        trust_ir_function_to_chc_translation_output_per_block(module, caller_fn.id, &options)
            .expect("the caller translates per block");
    CallerTranslation { default, per_block, call_block }
}

/// The constraint lists of the `error` rules whose body relation is `block`'s.
fn error_rules_from_block(vc: &ChcVc, block: BlockId) -> Vec<Vec<Option<bool>>> {
    let name = format!("bb{}", block.index());
    let rules: Vec<Vec<Option<bool>>> = vc
        .rules
        .iter()
        .filter(|rule| rule.head.name.as_str() == "error")
        .filter(|rule| rule.body.relation.as_ref().is_some_and(|r| r.name.as_str() == name))
        .map(|rule| rule.body.constraints.iter().map(try_eval_to_bool).collect())
        .collect();
    assert!(
        !rules.is_empty(),
        "the call block {name} must carry error rules, or this test checks nothing"
    );
    rules
}

fn census_outcome(output: &ChcTranslationOutput, callee: &str) -> CallSummaryOutcome {
    output
        .call_summary_census
        .iter()
        .find(|attempt| attempt.callee == callee)
        .unwrap_or_else(|| {
            panic!("the census records the call to `{callee}`: {:?}", output.call_summary_census)
        })
        .outcome
        .clone()
}

/// THE REGRESSION. `stop` has no return path and cannot panic. Its summary must
/// succeed. Every error rule in the call block, the summary's own and the one for
/// the trailing `Unreachable`, must be vacuous: some constraint folds to the
/// constant `false`, the `Assume(false)`. No unconditional error rule may remain.
#[test]
fn a_panic_free_never_returning_callee_is_summarized_and_its_call_does_not_continue() {
    let module = module(WRAPPER_BUNDLE);
    let CallerTranslation { default: output, per_block, call_block } =
        translate_caller(&module, "inc", "stop");
    assert_eq!(
        census_outcome(&output, "stop"),
        CallSummaryOutcome::Summarized,
        "diagnostics: {:?}",
        output.diagnostics
    );
    assert!(
        !output
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::UnsupportedDirectCallSummary),
        "no fail-closed call-summary error rule may remain: {:?}",
        output.diagnostics
    );
    assert_eq!(
        census_outcome(&per_block, "stop"),
        CallSummaryOutcome::Summarized,
        "per-block diagnostics: {:?}",
        per_block.diagnostics
    );
    for constraints in error_rules_from_block(&per_block.vc, call_block) {
        assert!(
            constraints.contains(&Some(false)),
            "every error rule after a call that never returns must be vacuous, got constraints folding to \
             {constraints:?}"
        );
    }
}

/// THE NEGATIVE CONTROL. `stop_if` also has no return path, so its summary now
/// succeeds too. But its `panic!()` path is a real error condition, and it must
/// reach the caller as a LIVE error rule. It must not fold to `false`. The
/// never-continues tail may not swallow what happens BEFORE the call returns.
#[test]
fn a_never_returning_callee_that_can_panic_still_charges_its_caller() {
    let module = module(PANICKING_BUNDLE);
    let CallerTranslation { default: output, per_block, call_block } =
        translate_caller(&module, "g", "stop_if");
    for (encoding, translation) in [("default", &output), ("per-block", &per_block)] {
        assert_eq!(
            census_outcome(translation, "stop_if"),
            CallSummaryOutcome::Summarized,
            "{encoding} diagnostics: {:?}",
            translation.diagnostics
        );
    }
    let rules = error_rules_from_block(&per_block.vc, call_block);
    assert!(
        rules.iter().any(|constraints| !constraints.contains(&Some(false))),
        "the callee's reachable panic must stay a live error rule in the caller, got {rules:?}"
    );
}
