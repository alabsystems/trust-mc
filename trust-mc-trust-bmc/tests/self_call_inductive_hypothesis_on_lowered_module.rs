//! The self-call inductive hypothesis on REAL bridge output — not hand-built IR.
//!
//! `fixtures/recursive_requires_native_bundle.json` is the `-Ztrust-dump=
//! native-bundle` of `tests/ui/trust/native_recursive_requires_fresh_context.rs`
//! (`#valid`, trustc stage1 on 2026-09-14): `fn recursive_requires(n: u32)
//! requires n > 0 { if n > 1 { recursive_requires(n - 1) } }`. The bridge puts
//! the `requires` assume and the parameter-range assume in the ENTRY block,
//! spelled over entry-block constants, and the self-call in a NON-ENTRY block
//! behind the recursion guard with the actual from a checked subtraction.
//!
//! The hand-built unit tests in `src/tests.rs` all placed the self-call in the
//! entry block and passed while this body still fell through to the historical
//! `RecursiveDirectCall` error rule: the evaluator looked entry constants up in
//! a per-block value map that `translate_block` had already cleared. This test
//! is the lowered-module pin for that miss, and it reads the census reason so a
//! future miss is named rather than reconstructed.

use trust_ir::Module;
use trust_mc_trust_bmc::{
    CallSummaryOutcome, TranslateOptions, TrustIrChcUnsupportedReason,
    trust_ir_to_chc_translation_outputs, trust_ir_to_chc_translation_outputs_per_block,
};

const RECURSIVE_REQUIRES_BUNDLE: &str =
    include_str!("fixtures/recursive_requires_native_bundle.json");

#[path = "support/initialized_construction.rs"]
mod initialized_construction;

fn module(bundle_json: &str) -> Module {
    let bundle: serde_json::Value =
        serde_json::from_str(bundle_json).expect("the dumped native bundle is valid JSON");
    serde_json::from_value(bundle["module"].clone())
        .expect("the dumped native bundle module deserializes")
}

#[test]
fn bridge_lowered_recursive_requires_takes_the_inductive_hypothesis() {
    // Retain the complete original recursion/contract oracle on an explicit
    // initialized construction twin; the old captured Undef is UB, not havoc.
    let module =
        initialized_construction::complete_construction_twin(&module(RECURSIVE_REQUIRES_BUNDLE));
    let function = module
        .functions
        .iter()
        .find(|f| f.name == "recursive_requires")
        .expect("the fixture carries the recursive body");
    assert!(
        function.blocks.len() > 1,
        "the fixture must keep its multi-block shape: {}",
        function.blocks.len()
    );
    let options =
        TranslateOptions { collect_call_summary_census: true, ..TranslateOptions::default() };
    let outputs = trust_ir_to_chc_translation_outputs(&module, &options);
    let output = outputs
        .iter()
        .find(|o| o.call_summary_census.iter().any(|a| a.caller == "recursive_requires"))
        .expect("the recursive body's translation records its self-call in the census");
    let reasons: Vec<String> =
        output.call_summary_census.iter().map(|a| format!("{:?}", a.outcome)).collect();
    assert!(
        !output
            .diagnostics
            .iter()
            .any(|d| d.reason == TrustIrChcUnsupportedReason::RecursiveDirectCall),
        "the real self-call must take the inductive hypothesis; census: {reasons:?}; diagnostics: {:?}",
        output.diagnostics
    );
    assert_eq!(output.inductive_hypothesis_sites.len(), 1, "census: {reasons:?}");
    assert!(
        output
            .call_summary_census
            .iter()
            .any(|a| a.outcome == CallSummaryOutcome::InductiveHypothesis),
        "census: {reasons:?}"
    );
    // Exactly three error rules: the translator's own underflow obligation on
    // `n - 1` (in the subtraction's block), and the two re-asserted entry
    // assumes over the actual in the CALL block — `requires n > 0` and the
    // parameter-range assume. The actual reaches the call block as a block
    // argument (the checked subtraction's tuple field), so the re-asserted
    // `requires` reads `not(actual > 0)` over that variable, not over a
    // syntactic subtraction. (The `Debug` rendering wraps operands, so these
    // are operator-presence checks within one rule.)
    //
    // Read per block, where each error obligation is its own rule over its
    // block's relation; production makes this acyclic body one large-block
    // query whose error sites must sit in the same blocks (checked below).
    let per_block = trust_ir_to_chc_translation_outputs_per_block(&module, &options);
    let per_block = per_block
        .iter()
        .find(|o| o.call_summary_census.iter().any(|a| a.caller == "recursive_requires"))
        .expect("the per-block translation records the self-call too");
    assert_eq!(per_block.diagnostics, output.diagnostics);
    assert_eq!(per_block.inductive_hypothesis_sites, output.inductive_hypothesis_sites);
    let error_rules: Vec<String> = per_block
        .vc
        .rules
        .iter()
        .filter(|rule| rule.head.name == "error")
        .map(|rule| format!("{rule:?}"))
        .collect();
    assert_eq!(error_rules.len(), 3, "got {error_rules:#?}");
    let map = output.large_block.as_ref().expect("the acyclic body is one large-block query");
    let mut site_blocks: Vec<u32> = map.sites.iter().map(|site| site.block.index()).collect();
    site_blocks.sort_unstable();
    assert_eq!(site_blocks, [1, 3, 3], "the same error sites, block by block");
    let call_block_rules: Vec<&String> =
        error_rules.iter().filter(|r| r.contains("RelName(\"bb3\")")).collect();
    assert_eq!(
        call_block_rules.len(),
        2,
        "two re-assertions in the call block, got {error_rules:#?}"
    );
    assert!(
        call_block_rules.iter().any(|r| {
            r.contains("Not(")
                && r.contains("BvUGt(")
                && r.contains("BitVecConst { value: 0, width: 32 }")
        }),
        "the re-asserted `actual > 0` must be an error rule in the call block, got {error_rules:#?}"
    );
    assert!(
        call_block_rules
            .iter()
            .any(|r| r.contains("Ite {") && r.contains("BvUGe(") && r.contains("BvULe(")),
        "the re-asserted parameter-range assume must be an error rule in the call block, got {error_rules:#?}"
    );
    assert!(
        error_rules
            .iter()
            .any(|r| r.contains("RelName(\"bb1\")") && r.contains("BvSubNoUnderflowUnsigned(")),
        "the translator's own underflow obligation on `n - 1` stays, got {error_rules:#?}"
    );
}

#[test]
fn original_recursive_capture_undef_remains_ub_and_cannot_supply_an_inductive_actual() {
    use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
    let module = module(RECURSIVE_REQUIRES_BUNDLE);
    let function =
        module.functions.iter().find(|function| function.name == "recursive_requires").unwrap();
    let error = Interpreter::with_module(&module)
        .execute_func(function.id, [InterpretValue::int(trust_ir::Ty::U32, 2).unwrap()])
        .expect_err("the old checked-tuple Undef executes before the self-call");
    assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
    let output = trust_ir_to_chc_translation_outputs(&module, &TranslateOptions::default());
    assert!(output.iter().any(|output| {
        output
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.reason == TrustIrChcUnsupportedReason::OperandConsumption)
    }));
    assert!(output.iter().all(|output| output.inductive_hypothesis_sites.is_empty()));

    let initialized = initialized_construction::complete_construction_twin(&module);
    Interpreter::with_module(&initialized)
        .execute_func(function.id, [InterpretValue::int(trust_ir::Ty::U32, 2).unwrap()])
        .expect("the exact evaluated checked-subtraction fields are initialized");
}
