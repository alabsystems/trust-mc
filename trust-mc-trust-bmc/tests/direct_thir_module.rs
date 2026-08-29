//! STEP 0 of the direct-lane proof-authority plan: evidence that a module the
//! DIRECT lane produced (THIR -> trust_ir, no MIR anywhere upstream) turns into
//! the same CHC shape trust-mc already solves.
//!
//! Nobody had measured this. The plan for taking `trust-thir-lower` to proof
//! authority rests on the assumption that its Module is translator-compatible,
//! and green was *expected* rather than established — the direct lane merges
//! through BLOCK PARAMETERS where the MIR lane uses stack slots, so the
//! assumption is not free.
//!
//! The fixture is a real `-Ztrust-dump=ir:` artifact, checked in beside the
//! source that produced it and the text rendering, so a drift shows up as a diff
//! rather than as a mystery:
//!
//! ```text
//! trustc --edition 2021 --crate-type lib --crate-name step0 \
//!        -Ztrust-verify=off -Ztrust-ir-lower=on -Ztrust-dump=ir:<dir> \
//!        tests/fixtures/direct_thir_arith.rs
//! ```

use trust_mc_trust_bmc::{TranslateOptions, trust_ir_to_chc_vc};

const DIRECT_MODULE: &[u8] = include_bytes!("fixtures/direct_thir_arith.trust-ir.bin");
const DIRECT_TEXT: &str = include_str!("fixtures/direct_thir_arith.trust-ir.txt");

/// The direct lane's asserts survive into CHC error rules, one for one.
///
/// `a + b`, `a / b`, `s * d` lower to FOUR asserts: `no_overflow` for the add,
/// `div_nonzero` and the signed `MIN / -1` `no_overflow` for the divide, and
/// `no_overflow` for the multiply. That count is read off the checked-in text
/// rendering rather than hardcoded, so if the lowering changes shape the test
/// re-derives instead of lying.
#[test]
fn direct_thir_module_translates_every_assert() {
    let module = trust_ir::binary::deserialize_module(DIRECT_MODULE)
        .expect("the checked-in -Ztrust-dump=ir: fixture must decode");

    let asserts_in_ir = DIRECT_TEXT.lines().filter(|l| l.trim_start().starts_with("assert ")).count();
    assert_eq!(
        asserts_in_ir, 4,
        "fixture drift: the arithmetic body should lower to 4 asserts \
         (add overflow, div-by-zero, signed MIN/-1, mul overflow)"
    );

    let vcs = trust_ir_to_chc_vc(&module, &TranslateOptions::default());
    assert!(
        !vcs.is_empty(),
        "a direct-lane module must produce at least one CHC VC; got none — the \
         translator did not consume the THIR-lowered shape"
    );

    // Every assert must be represented. The translator emits one error rule per
    // assert (translate_chc.rs), so the counts must agree: a shortfall means an
    // obligation was silently dropped on the direct lane, which is exactly the
    // failure this step exists to rule out.
    // An error rule is one whose head is the `error` relation -- the same
    // predicate the in-crate tests use (src/tests.rs:3669).
    let error_rules: usize = vcs
        .iter()
        .map(|vc| vc.rules.iter().filter(|r| r.head.name == "error").count())
        .sum();

    // MEASURED, and NOT the 1:1 the plan assumed: 4 asserts -> 6 error rules.
    // The translator models `sdiv` division safety ITSELF, on top of consuming
    // the direct lane's explicit asserts. Enumerated (see the companion test):
    //
    //   [0] Not(Ite ..)              <- the add overflow assert
    //   [1] Not(Not(Eq ..))          <- the div_nonzero assert
    //   [2] Not(Ite ..)              <- the signed MIN/-1 assert
    //   [3] Not(BvSdivNoOverflow ..) <- TRANSLATOR-INTRINSIC sdiv overflow
    //   [4] Eq(bb0_v1, ..)           <- TRANSLATOR-INTRINSIC divisor-zero
    //   [5] Not(Ite ..)              <- the mul overflow assert
    //
    // The direction is the safe one -- the CHC over-approximates, so no assert
    // goes unchecked -- but it means an obligation table minted from the direct
    // lane's asserts will NOT stand in 1:1 correspondence with the solver's
    // error rules. Any future obligation-identity scheme has to survive that.
    const TRANSLATOR_INTRINSIC_DIV_RULES: usize = 2;
    assert!(
        error_rules >= asserts_in_ir,
        "every direct-lane assert must be represented as a CHC error rule: \
         {asserts_in_ir} asserts but only {error_rules} error rules -- an \
         obligation was DROPPED, which is the failure this test exists to catch"
    );
    assert_eq!(
        error_rules,
        asserts_in_ir + TRANSLATOR_INTRINSIC_DIV_RULES,
        "the assert-to-error-rule relationship changed. It is not 1:1: the \
         translator adds its own sdiv overflow and divisor-zero rules. If this \
         count moved, re-run the companion test and update the enumeration \
         above rather than relaxing the assertion"
    );
}

/// Diagnostic companion: name every error rule the direct module produces, so a
/// count mismatch is actionable rather than a bare number.
#[test]
fn zz_enumerate_direct_error_rules() {
    let module = trust_ir::binary::deserialize_module(DIRECT_MODULE).expect("decode");
    let vcs = trust_ir_to_chc_vc(&module, &TranslateOptions::default());
    for (i, vc) in vcs.iter().enumerate() {
        let errs: Vec<_> = vc.rules.iter().filter(|r| r.head.name == "error").collect();
        println!("VC {i}: {} error rules of {} total", errs.len(), vc.rules.len());
        for (j, r) in errs.iter().enumerate() {
            let from = r.body.relation.as_ref().map(|x| format!("{:?}", x.name)).unwrap_or_else(|| "-".into());
            let cs: Vec<String> = r.body.constraints.iter().map(|c| format!("{c:?}")).collect();
            println!("  [{j}] from={from} constraints={}", cs.join(" && "));
        }
    }
}
