// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! First-class UF call summaries: the gate, the congruence, and the duals.
//!
//! These are the tests ay's 2026-08-29 capability response (adoption step 8)
//! requires BEFORE anything about Trust-MC's demotion classification may move:
//! a NEGATIVE DUAL (two equal-argument calls that read hidden state and may
//! legitimately differ — must NOT be proved), POSITIVE CONGRUENCE, and
//! SAT/Unsafe witnesses. Nothing here changes a classification; the lane still
//! records the unblessed `call_uf_congruent_summary` reason it always did.
//!
//! Two independent layers per behaviour, because either alone is weak:
//!
//! * a STRUCTURAL check on the `ChcVc` — which symbols were minted, with which
//!   signature, and that none of them is a Horn relation. Deterministic; it
//!   cannot be masked by a solver timeout, and it is what actually catches a
//!   widened purity gate or a merged callee.
//! * a SOLVE check through `ay-chc` on the emitted SMT-LIB. `unsat` = the error
//!   relation is unreachable (PROVED); `sat` = a counterexample exists.

// Test code: unwrap/panic are acceptable for assertions
#![allow(clippy::unwrap_used, clippy::panic)]

use super::common::*;
use ay_bindings::Sort;
use trust_mc_core::chc::ChcVc;
use trust_mc_core::decl::Decl;

fn mir_to_chc_default(tcx: TyCtxt<'_>, body: &rustc_public::mir::Body, fn_name: &str) -> ChcVc {
    crate::codegen_ay::chc::mir_to_chc(
        tcx,
        body,
        fn_name,
        crate::codegen_ay::chc::ChcConfig::default(),
    )
}

/// AY needs more than the 5 s corpus default for a 20-arm callee summarised
/// twice; these harnesses are tiny but the BV domain is 32/64/128 bits wide.
const UF_TEST_TIMEOUT_SECS: u64 = 60;

/// Every first-class call-summary UF declared in this VC, as
/// `(name, arg_sorts, ret_sort)`.
fn uf_decls(vc: &ChcVc) -> Vec<(String, Vec<Sort>, Sort)> {
    vc.decls
        .iter()
        .filter_map(|decl| match decl {
            Decl::Fun { name, arg_sorts, ret_sort } if name.starts_with("uf_call_") => {
                Some((name.clone(), arg_sorts.clone(), ret_sort.clone()))
            }
            _ => None,
        })
        .collect()
}

/// The invariant that separates an ORDINARY UF from a HORN RELATION.
///
/// A Bool-returning `declare-fun` is a predicate to ay-chc, and a predicate is
/// something the solver may synthesise an interpretation for. Assert, on the IR
/// rather than on the text, that every minted summary symbol is (a) never
/// Bool-returning, (b) never a declared relation, and (c) never the head of a
/// Horn rule.
fn assert_uf_symbols_are_not_horn_relations(vc: &ChcVc) {
    for (name, _, ret_sort) in uf_decls(vc) {
        assert!(
            !ret_sort.is_bool(),
            "{name}: a Bool-returning declare-fun is a HORN RELATION to ay-chc, never an \
             ordinary UF — bool results must be declared BV1 and compared against #b1"
        );
        assert!(
            !vc.relations.iter().any(|rel| *rel.name == *name),
            "{name} was declared both as a UF and as a CHC relation"
        );
        assert!(
            !vc.rules.iter().any(|rule| *rule.head.name == *name),
            "{name} appears as the HEAD of a Horn rule — it is being solved for, not \
             uninterpreted"
        );
    }
}

/// Solve and REPORT. The refutability duals assert only `!= "unsat"` (an
/// `unknown` must not be read as a proof either), so the actual verdict is
/// printed: `cargo test -- --nocapture` shows whether each dual is a real
/// `sat` witness or merely undecided.
fn solved_verdict(smt: &str, label: &str) -> String {
    let verdict = run_z3_on_smt2_with_timeout(smt, UF_TEST_TIMEOUT_SECS)
        .unwrap_or_else(|err| panic!("AY execution failed: {err}. SMT:\n{smt}"));
    eprintln!("[uf-congruence] {label}: AY verdict = {verdict}");
    verdict
}

fn encode(ctx_tcx: TyCtxt<'_>, fn_name: &str) -> (ChcVc, String) {
    let instance = find_instance_by_suffix(ctx_tcx, fn_name);
    let body = instance.body().expect("function body");
    let vc = mir_to_chc_default(ctx_tcx, &body, fn_name);
    let smt = crate::codegen_ay::emit_chc(&vc).to_string();
    (vc, smt)
}

// ---------------------------------------------------------------------------
// Sources
// ---------------------------------------------------------------------------

/// PURE, too big for `chc_inline_effective_block_limit`, no panicking path.
///
/// `wrapping_add` is one of `PURE_TOTAL_INTRINSICS`, so no `Assert` terminator
/// is generated and clause 4 of the purity gate is satisfied. Two callees with
/// the SAME signature (`alpha`, `beta`) so a symbol-merging bug is observable.
const PURE_SCALAR_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    fn alpha(x: u32, y: u32) -> u32 {
        match y {
            0 => x.wrapping_add(1),
            1 => x.wrapping_add(2),
            2 => x.wrapping_add(3),
            3 => x.wrapping_add(4),
            4 => x.wrapping_add(5),
            5 => x.wrapping_add(6),
            6 => x.wrapping_add(7),
            7 => x.wrapping_add(8),
            8 => x.wrapping_add(9),
            9 => x.wrapping_add(10),
            10 => x.wrapping_add(11),
            11 => x.wrapping_add(12),
            12 => x.wrapping_add(13),
            13 => x.wrapping_add(14),
            14 => x.wrapping_add(15),
            15 => x.wrapping_add(16),
            16 => x.wrapping_add(17),
            17 => x.wrapping_add(18),
            _ => x.wrapping_add(19),
        }
    }

    fn beta(x: u32, y: u32) -> u32 {
        match y {
            0 => x.wrapping_sub(1),
            1 => x.wrapping_sub(2),
            2 => x.wrapping_sub(3),
            3 => x.wrapping_sub(4),
            4 => x.wrapping_sub(5),
            5 => x.wrapping_sub(6),
            6 => x.wrapping_sub(7),
            7 => x.wrapping_sub(8),
            8 => x.wrapping_sub(9),
            9 => x.wrapping_sub(10),
            10 => x.wrapping_sub(11),
            11 => x.wrapping_sub(12),
            12 => x.wrapping_sub(13),
            13 => x.wrapping_sub(14),
            14 => x.wrapping_sub(15),
            15 => x.wrapping_sub(16),
            16 => x.wrapping_sub(17),
            17 => x.wrapping_sub(18),
            _ => x.wrapping_sub(19),
        }
    }

    /// POSITIVE CONGRUENCE: same symbol, equal arguments => equal results.
    pub fn probe_uf_same_args_congruent() {
        let x: u32 = kani::any();
        let y: u32 = kani::any();
        let a = alpha(x, y);
        let b = alpha(x, y);
        assert!(a == b);
    }

    /// POSITIVE CONGRUENCE, the hard direction: the two applications are
    /// SYNTACTICALLY DIFFERENT (`x` vs `z`) and equal only because `x == z` is
    /// assumed. Proving this needs real congruence reasoning over the symbol,
    /// not the syntactic identity of two identical terms.
    pub fn probe_uf_congruent_under_assumption() {
        let x: u32 = kani::any();
        let z: u32 = kani::any();
        let y: u32 = kani::any();
        kani::assume(x == z);
        let a = alpha(x, y);
        let b = alpha(z, y);
        assert!(a == b);
    }

    /// SAT WITNESS: congruence must NOT extend to different arguments.
    pub fn probe_uf_diff_args_not_congruent() {
        let x: u32 = kani::any();
        let y: u32 = kani::any();
        let z: u32 = kani::any();
        let a = alpha(x, y);
        let b = alpha(z, y);
        assert!(a == b);
    }

    /// SAT WITNESS: two DISTINCT callees with identical signatures must get
    /// distinct symbols. Both are applied twice so both reach the lane.
    pub fn probe_uf_distinct_callees_not_equal() {
        let x: u32 = kani::any();
        let y: u32 = kani::any();
        let a1 = alpha(x, y);
        let a2 = alpha(x, y);
        let b1 = beta(x, y);
        let b2 = beta(x, y);
        assert!(a1 == a2);
        assert!(b1 == b2);
        assert!(a1 == b1);
    }
"#;

/// The NEGATIVE DUAL. Byte-for-byte the same by-value scalar PROTOTYPE as
/// `alpha` above, and yet `hidden_state(x, y) != hidden_state(x, y)`: the body
/// reads and writes a `static mut`. This is `codegen_call_foreign.rs`'s
/// `uint32_t takes_int(uint32_t i) { return i + c++; }` written in Rust.
///
/// A gate that looked at the signature would summarise it and PROVE the two
/// calls equal — a fabricated proof. `established_pure_scalar_callee` reads the
/// MIR body instead, sees the `Deref` through the static's pointer, and refuses.
const HIDDEN_STATE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(static_mut_refs)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    static mut COUNTER: u32 = 0;

    fn hidden_state(x: u32, y: u32) -> u32 {
        let c: u32 = unsafe {
            COUNTER = COUNTER.wrapping_add(1);
            COUNTER
        };
        match y {
            0 => x.wrapping_add(c),
            1 => x.wrapping_add(c).wrapping_add(1),
            2 => x.wrapping_add(c).wrapping_add(2),
            3 => x.wrapping_add(c).wrapping_add(3),
            4 => x.wrapping_add(c).wrapping_add(4),
            5 => x.wrapping_add(c).wrapping_add(5),
            6 => x.wrapping_add(c).wrapping_add(6),
            7 => x.wrapping_add(c).wrapping_add(7),
            8 => x.wrapping_add(c).wrapping_add(8),
            9 => x.wrapping_add(c).wrapping_add(9),
            10 => x.wrapping_add(c).wrapping_add(10),
            11 => x.wrapping_add(c).wrapping_add(11),
            12 => x.wrapping_add(c).wrapping_add(12),
            13 => x.wrapping_add(c).wrapping_add(13),
            14 => x.wrapping_add(c).wrapping_add(14),
            15 => x.wrapping_add(c).wrapping_add(15),
            16 => x.wrapping_add(c).wrapping_add(16),
            17 => x.wrapping_add(c).wrapping_add(17),
            _ => x.wrapping_add(c).wrapping_add(19),
        }
    }

    /// MUST NOT BE PROVED.
    pub fn probe_hidden_state_not_congruent() {
        let x: u32 = kani::any();
        let y: u32 = kani::any();
        let a = hidden_state(x, y);
        let b = hidden_state(x, y);
        assert!(a == b);
    }
"#;

/// A PANICKING pure-looking callee: `x + 1` is overflow-checked, which lowers to
/// `CheckedBinaryOp` + `Assert`. Clause 4 of the gate refuses it, because a
/// summary would silently swallow the overflow panic (a MISSED BUG, not merely
/// a lost proof).
const PANICKING_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![allow(arithmetic_overflow)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    fn checked_add_chain(x: u32, y: u32) -> u32 {
        match y {
            0 => x + 1,
            1 => x + 2,
            2 => x + 3,
            3 => x + 4,
            4 => x + 5,
            5 => x + 6,
            6 => x + 7,
            7 => x + 8,
            8 => x + 9,
            9 => x + 10,
            10 => x + 11,
            11 => x + 12,
            12 => x + 13,
            13 => x + 14,
            14 => x + 15,
            15 => x + 16,
            16 => x + 17,
            17 => x + 18,
            _ => x + 19,
        }
    }

    pub fn probe_panicking_callee_refused() {
        let x: u32 = kani::any();
        let y: u32 = kani::any();
        let a = checked_add_chain(x, y);
        let b = checked_add_chain(x, y);
        assert!(a == b);
    }
"#;

/// Both width ceilings the frozen table imposed, in one callee:
/// 64 + 64 = 128 bits of ARGUMENTS (the table concatenated into 96 bits and
/// refused anything wider) and a 128-bit RETURN (the table's value was 64 bits
/// and narrower returns took the low bits).
const WIDE_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    fn wide_pure(x: u64, y: u64) -> u128 {
        let a = x as u128;
        let b = y as u128;
        match (y & 31) as u32 {
            0 => a.wrapping_add(b),
            1 => a.wrapping_add(b).wrapping_add(1),
            2 => a.wrapping_add(b).wrapping_add(2),
            3 => a.wrapping_add(b).wrapping_add(3),
            4 => a.wrapping_add(b).wrapping_add(4),
            5 => a.wrapping_add(b).wrapping_add(5),
            6 => a.wrapping_add(b).wrapping_add(6),
            7 => a.wrapping_add(b).wrapping_add(7),
            8 => a.wrapping_add(b).wrapping_add(8),
            9 => a.wrapping_add(b).wrapping_add(9),
            10 => a.wrapping_add(b).wrapping_add(10),
            11 => a.wrapping_add(b).wrapping_add(11),
            12 => a.wrapping_add(b).wrapping_add(12),
            13 => a.wrapping_add(b).wrapping_add(13),
            14 => a.wrapping_add(b).wrapping_add(14),
            15 => a.wrapping_add(b).wrapping_add(15),
            16 => a.wrapping_add(b).wrapping_add(16),
            17 => a.wrapping_add(b).wrapping_add(17),
            _ => a.wrapping_mul(b),
        }
    }

    pub fn probe_wide_uf_congruent() {
        let x: u64 = kani::any();
        let y: u64 = kani::any();
        let a = wide_pure(x, y);
        let b = wide_pure(x, y);
        assert!(a == b);
    }
"#;

/// A `bool`-returning pure callee. The Rust return is `Bool`, so the emitted
/// declaration MUST be `(_ BitVec 1)` — a Bool-returning `declare-fun` is a
/// Horn relation to ay-chc, not an ordinary UF.
const BOOL_RESULT_SOURCE: &str = r#"
    #![allow(dead_code)]
    #![feature(register_tool)]
    #![register_tool(kanitool)]

    mod kani {
        #[kanitool::fn_marker = "AnyModel"]
        pub fn any<T>() -> T {
            unsafe { std::mem::zeroed() }
        }

        #[kanitool::fn_marker = "AssumeHook"]
        pub fn assume(cond: bool) {
            let _ = cond;
        }
    }

    fn pure_pred(x: u32, y: u32) -> bool {
        match y {
            0 => x.wrapping_add(1) > 5,
            1 => x.wrapping_add(2) > 5,
            2 => x.wrapping_add(3) > 5,
            3 => x.wrapping_add(4) > 5,
            4 => x.wrapping_add(5) > 5,
            5 => x.wrapping_add(6) > 5,
            6 => x.wrapping_add(7) > 5,
            7 => x.wrapping_add(8) > 5,
            8 => x.wrapping_add(9) > 5,
            9 => x.wrapping_add(10) > 5,
            10 => x.wrapping_add(11) > 5,
            11 => x.wrapping_add(12) > 5,
            12 => x.wrapping_add(13) > 5,
            13 => x.wrapping_add(14) > 5,
            14 => x.wrapping_add(15) > 5,
            15 => x.wrapping_add(16) > 5,
            16 => x.wrapping_add(17) > 5,
            17 => x.wrapping_add(18) > 5,
            _ => x.wrapping_add(19) > 5,
        }
    }

    pub fn probe_bool_uf_congruent() {
        let x: u32 = kani::any();
        let y: u32 = kani::any();
        let a = pure_pred(x, y);
        let b = pure_pred(x, y);
        assert!(a == b);
    }
"#;

// ---------------------------------------------------------------------------
// Structural tests — deterministic, no solver
// ---------------------------------------------------------------------------

/// The migration receipt: a first-class `(declare-fun ...)` is emitted, the
/// frozen `call_uf_tbl` Array column is GONE, and the symbol is a UF rather
/// than a Horn relation.
#[test]
fn test_pure_callee_gets_first_class_uf_not_a_frozen_table() {
    with_test_ay_ctx_for_source(PURE_SCALAR_SOURCE, |ctx| {
        let (vc, smt) = encode(ctx.tcx, "probe_uf_same_args_congruent");

        let ufs = uf_decls(&vc);
        assert_eq!(
            ufs.len(),
            1,
            "exactly one summary symbol for one monomorphised callee, got: {ufs:?}"
        );
        let (name, arg_sorts, ret_sort) = &ufs[0];
        assert_eq!(
            arg_sorts,
            &vec![Sort::bitvec(32), Sort::bitvec(32)],
            "{name}: every semantic input must be an argument of the application"
        );
        assert_eq!(ret_sort, &Sort::bitvec(32), "{name}: return sort must be the callee's");
        assert_uf_symbols_are_not_horn_relations(&vc);

        assert!(
            !smt.contains("call_uf_tbl"),
            "the frozen congruent-table emulation must be gone from the emitted problem"
        );
        assert!(
            smt.contains(&format!("(declare-fun {name} ((_ BitVec 32) (_ BitVec 32)) (_ BitVec 32))")),
            "expected a first-class scalar declare-fun for {name}; SMT:\n{smt}"
        );
    });
}

/// NEGATIVE DUAL, structural half. The gate must refuse a hidden-state callee,
/// so NO summary symbol may exist for this harness. This is the assertion that
/// fires deterministically if the purity oracle is ever widened.
#[test]
fn test_hidden_state_callee_mints_no_uf_symbol() {
    with_test_ay_ctx_for_source(HIDDEN_STATE_SOURCE, |ctx| {
        let (vc, smt) = encode(ctx.tcx, "probe_hidden_state_not_congruent");
        let ufs = uf_decls(&vc);
        assert!(
            ufs.is_empty(),
            "a callee that reads and writes a `static mut` has the same by-value scalar \
             PROTOTYPE as a pure one but is NOT a function of its arguments; summarising it \
             fabricates a proof that two equal-argument calls are equal. Minted: {ufs:?}"
        );
        assert!(!smt.contains("uf_call_"), "no summary application may reach the problem");
    });
}

/// The clause that makes this lane blessable rather than merely more precise:
/// a callee with a panicking path is refused, because a UF summary would
/// swallow its overflow panic — a MISSED BUG.
#[test]
fn test_panicking_callee_mints_no_uf_symbol() {
    with_test_ay_ctx_for_source(PANICKING_SOURCE, |ctx| {
        let (vc, _smt) = encode(ctx.tcx, "probe_panicking_callee_refused");
        let ufs = uf_decls(&vc);
        assert!(
            ufs.is_empty(),
            "an overflow-checked `x + 1` lowers to CheckedBinaryOp + Assert; a summary would \
             drop the panic the caller should have seen. Minted: {ufs:?}"
        );
    });
}

/// Two distinct callees with IDENTICAL signatures must never share a symbol.
/// A merged symbol would assert `alpha(x,y) == beta(x,y)`, which is false.
#[test]
fn test_distinct_callees_get_distinct_uf_symbols() {
    with_test_ay_ctx_for_source(PURE_SCALAR_SOURCE, |ctx| {
        let (vc, _smt) = encode(ctx.tcx, "probe_uf_distinct_callees_not_equal");
        let ufs = uf_decls(&vc);
        assert_eq!(
            ufs.len(),
            2,
            "alpha and beta are different monomorphised callees and need different symbols, \
             got: {ufs:?}"
        );
        assert_ne!(ufs[0].0, ufs[1].0, "two callees collapsed onto one symbol: {ufs:?}");
        assert_uf_symbols_are_not_horn_relations(&vc);
    });
}

/// The precision ceilings the frozen table imposed and the first-class symbol
/// does not: a 128-bit argument concatenation (table limit: 96) and a 128-bit
/// return (table limit: 64, with narrower returns taking the low bits).
#[test]
fn test_wide_signature_is_no_longer_refused() {
    with_test_ay_ctx_for_source(WIDE_SOURCE, |ctx| {
        let (vc, _smt) = encode(ctx.tcx, "probe_wide_uf_congruent");
        let ufs = uf_decls(&vc);
        assert_eq!(ufs.len(), 1, "expected one summary symbol, got: {ufs:?}");
        let (name, arg_sorts, ret_sort) = &ufs[0];
        assert_eq!(
            arg_sorts,
            &vec![Sort::bitvec(64), Sort::bitvec(64)],
            "{name}: 128 bits of arguments exceeded the frozen table's 96-bit key payload"
        );
        assert_eq!(
            ret_sort,
            &Sort::bitvec(128),
            "{name}: a 128-bit return exceeded the frozen table's 64-bit value"
        );
        assert_uf_symbols_are_not_horn_relations(&vc);
    });
}

/// A `bool`-returning UF is declared BV1, never Bool. A Bool-returning
/// `declare-fun` means a HORN RELATION to ay-chc — a different construct that
/// the solver may synthesise an interpretation for.
#[test]
fn test_bool_returning_uf_is_declared_bv1_not_a_predicate() {
    with_test_ay_ctx_for_source(BOOL_RESULT_SOURCE, |ctx| {
        let (vc, smt) = encode(ctx.tcx, "probe_bool_uf_congruent");
        let ufs = uf_decls(&vc);
        assert_eq!(ufs.len(), 1, "expected one summary symbol, got: {ufs:?}");
        let (name, arg_sorts, ret_sort) = &ufs[0];
        assert_eq!(arg_sorts, &vec![Sort::bitvec(32), Sort::bitvec(32)]);
        assert_eq!(
            ret_sort,
            &Sort::bitvec(1),
            "{name}: a bool result must be declared BV1 and read back with `= #b1`"
        );
        assert_uf_symbols_are_not_horn_relations(&vc);
        assert!(
            !smt.contains(&format!("(declare-fun {name} ((_ BitVec 32) (_ BitVec 32)) Bool)")),
            "a Bool-returning declare-fun would be parsed as a Horn relation; SMT:\n{smt}"
        );
    });
}

/// The symbol carries no axiom anywhere: it is DECLARED once, APPLIED in rule
/// bodies, and never mentioned by an assertion, a relation declaration, or a
/// rule head. That is what keeps a MISSING finite UF model value a non-proof
/// outcome rather than a proof — the encoder says nothing about the function
/// beyond the applications themselves, so an interpretation the solver could
/// not build leaves an undecided problem, not a discharged one.
///
/// Uses the refutable harness on purpose. `probe_uf_same_args_congruent` is
/// discharged by the bounded straight-line prover (its VC comes out as
/// `(rule (=> false error))`), which leaves the declaration with no application
/// to inspect; this harness reaches the solver with its rules intact.
#[test]
fn test_uf_symbol_is_declared_once_applied_and_never_constrained() {
    with_test_ay_ctx_for_source(PURE_SCALAR_SOURCE, |ctx| {
        let (vc, smt) = encode(ctx.tcx, "probe_uf_diff_args_not_congruent");
        let ufs = uf_decls(&vc);
        assert_eq!(ufs.len(), 1, "expected one summary symbol, got: {ufs:?}");
        let name = ufs[0].0.as_str();
        assert_uf_symbols_are_not_horn_relations(&vc);

        let declaration = format!("(declare-fun {name} ");
        assert_eq!(
            smt.matches(&declaration).count(),
            1,
            "{name} must be declared exactly once; SMT:\n{smt}"
        );
        assert!(
            smt.matches(name).count() >= 3,
            "{name} should be declared once and APPLIED at both call sites; SMT:\n{smt}"
        );
        // The CHC lane emits `(assert ...)` only for cover properties, after the
        // query. None may mention the summary symbol.
        for line in smt.lines() {
            let trimmed = line.trim_start();
            assert!(
                !(trimmed.starts_with("(assert ") && trimmed.contains(name)),
                "{name} must never be constrained by an assertion: {line}"
            );
        }
    });
}

/// POSITIVE CONGRUENCE, the hard direction. `alpha(x, y) == alpha(z, y)` under
/// an assumed `x == z` cannot be settled by syntactic term identity — it needs
/// the solver to treat the summary symbol as a FUNCTION. With the pre-#4270
/// encoding (two independent havocs) this is unprovable.
#[test]
fn test_congruence_under_assumed_equality_is_proved() {
    with_test_ay_ctx_for_source(PURE_SCALAR_SOURCE, |ctx| {
        let (vc, smt) = encode(ctx.tcx, "probe_uf_congruent_under_assumption");
        assert_eq!(uf_decls(&vc).len(), 1, "expected one summary symbol");
        assert_z3_result_with_timeout(&smt, "unsat", UF_TEST_TIMEOUT_SECS);
    });
}

// ---------------------------------------------------------------------------
// Solve tests — the behaviour the structure is supposed to buy
// ---------------------------------------------------------------------------

/// POSITIVE CONGRUENCE: `alpha(x, y) == alpha(x, y)` is PROVED.
///
/// Without a congruent summary the two sites drew independent havocs and this
/// was unprovable.
#[test]
fn test_same_args_congruence_is_proved() {
    with_test_ay_ctx_for_source(PURE_SCALAR_SOURCE, |ctx| {
        let (_vc, smt) = encode(ctx.tcx, "probe_uf_same_args_congruent");
        assert_z3_result_with_timeout(&smt, "unsat", UF_TEST_TIMEOUT_SECS);
    });
}

/// NEGATIVE DUAL, solver half: two equal-argument calls into hidden state may
/// legitimately differ, so the equality must NOT be proved. A `unsat` here is a
/// FABRICATED PROOF, which is exactly what an ungated UF summary produces.
///
/// Asserts `!= "unsat"` rather than `== "sat"` deliberately: `unknown` is also
/// "not proved", and a solver hiccup must not be able to turn this soundness
/// dual red. MEASURED 2026-09-01: the verdict is `sat` — the error really is
/// reachable, so this is a live witness and not a vacuous pass.
#[test]
fn test_hidden_state_congruence_is_not_proved() {
    with_test_ay_ctx_for_source(HIDDEN_STATE_SOURCE, |ctx| {
        let (_vc, smt) = encode(ctx.tcx, "probe_hidden_state_not_congruent");
        let verdict = solved_verdict(&smt, "probe_hidden_state_not_congruent");
        assert_ne!(
            verdict, "unsat",
            "`hidden_state(x, y) == hidden_state(x, y)` was PROVED. The callee mutates and \
             reads a `static mut`, so the two calls may legitimately differ — this is a \
             fabricated proof, not a verification. SMT:\n{smt}"
        );
    });
}

/// SAT WITNESS: congruence at EQUAL arguments must not leak into equality at
/// DIFFERENT arguments. If this came back `unsat` the symbol would be behaving
/// like a constant, not a function.
#[test]
fn test_different_args_stay_refutable() {
    with_test_ay_ctx_for_source(PURE_SCALAR_SOURCE, |ctx| {
        let (_vc, smt) = encode(ctx.tcx, "probe_uf_diff_args_not_congruent");
        let verdict = solved_verdict(&smt, "probe_uf_diff_args_not_congruent");
        assert_eq!(
            verdict, "sat",
            "`alpha(x, y) == alpha(z, y)` must stay REFUTABLE for unconstrained x, z. \
             `unsat` means the summary symbol is over-constrained (a fabricated proof); \
             anything else means the witness was lost. SMT:\n{smt}"
        );
    });
}

/// SAT WITNESS: two distinct callees must stay distinct to the solver.
#[test]
fn test_distinct_callees_stay_refutable() {
    with_test_ay_ctx_for_source(PURE_SCALAR_SOURCE, |ctx| {
        let (_vc, smt) = encode(ctx.tcx, "probe_uf_distinct_callees_not_equal");
        let verdict = solved_verdict(&smt, "probe_uf_distinct_callees_not_equal");
        assert_eq!(
            verdict, "sat",
            "`alpha(x, y) == beta(x, y)` must stay REFUTABLE. `unsat` means two distinct \
             callees were merged onto one summary symbol. SMT:\n{smt}"
        );
    });
}

/// The bool lane end to end: BV1 declaration, `= #b1` read-back, and the
/// resulting congruence is provable — and, critically, ay-chc PARSES it (a
/// Bool-returning declaration would have become a Horn relation instead).
#[test]
fn test_bool_result_congruence_is_proved() {
    with_test_ay_ctx_for_source(BOOL_RESULT_SOURCE, |ctx| {
        let (_vc, smt) = encode(ctx.tcx, "probe_bool_uf_congruent");
        assert_z3_result_with_timeout(&smt, "unsat", UF_TEST_TIMEOUT_SECS);
    });
}
