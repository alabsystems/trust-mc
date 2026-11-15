// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verdict parity of the precise CHC relation liveness against the analysis it
//! replaced.
//!
//! The pre-fix liveness carried (almost) every threaded value and promoted cell
//! through every block relation; the precise one carries only what each
//! block's translation, or a block it can reach, reads. Dropping a column no
//! read needs changes neither the reachable states nor the error rules, so
//! every function of the corpus must get the same verdict from the native
//! typed CHC/PDR solver under both — and the precise relations must never be
//! wider. The legacy analysis is reachable only through the test-only
//! `legacy-liveness-oracle` feature of trust-mc-trust-bmc.
//!
//! Corpus: every function of the lowered modules checked into
//! trust-mc-trust-bmc's fixtures (real `-Ztrust-dump` output of the compiler)
//! and generated families that exercise loop-carried cells, cross-block SSA
//! values and the ever-init cleanup-chain shape.
//!
//! The production translation makes an ACYCLIC function one large-block query
//! (design step 8e) while the legacy oracle keeps one relation per block, so on
//! those functions this also compares the two encodings (the large-block
//! encoding's own parity test is `chc_large_block_verdict_parity.rs`).

#![cfg(all(feature = "native-typed-chc-pdr", feature = "native-trust-ir-bundle"))]

use std::time::Duration;

use trust_ir::Module;
use trust_ir::inst::{ICmpOp, OverflowOp};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::{
    ChcPdrSolveOptions, ChcPdrSolveRequest, FullVerificationVerdict, MirChcPdrObligation,
    MirObligationKind,
};
use trust_mc_trust_bmc::{
    TranslateOptions, trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_with_legacy_liveness,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Refuted,
    Unknown,
}

fn solve(module: &Module, function: FuncId, legacy: bool) -> (Verdict, usize) {
    let options = TranslateOptions::default();
    let output = if legacy {
        trust_ir_function_to_chc_translation_output_with_legacy_liveness(module, function, &options)
    } else {
        trust_ir_function_to_chc_translation_output(module, function, &options)
    }
    .expect("corpus function translates");
    let arity: usize = output.vc.relations.iter().map(|relation| relation.arity()).sum();
    let name = module.function_by_id(function).map_or("?", |f| f.name.as_str()).to_owned();
    let obligation = MirChcPdrObligation::new(
        format!("liveness-parity-{}", function.index()),
        name,
        MirObligationKind::Assertion,
        output.vc,
    );
    if obligation.validate().is_err() {
        // No rule or no relation: not a solver question, and the same for both.
        return (Verdict::Unknown, arity);
    }
    let request = ChcPdrSolveRequest::new(obligation)
        .with_options(ChcPdrSolveOptions::default().with_timeout(Duration::from_secs(20)));
    // The engine's own verdict, before proof-grade admission (which needs the
    // private consumer replay this lane does not run): the parity question is
    // whether the CHC means the same thing, not whether a seal can be minted.
    let verdict = match trust_mc_driver::solve_typed_chc_pdr_full_verification(request) {
        Ok(solved) => match solved.verdict {
            FullVerificationVerdict::Proved { .. } => Verdict::Proved,
            FullVerificationVerdict::Failed { .. } => Verdict::Refuted,
            _ => Verdict::Unknown,
        },
        Err(_) => Verdict::Unknown,
    };
    (verdict, arity)
}

fn assert_parity(module: &Module, what: &str) -> Vec<Verdict> {
    let mut verdicts = Vec::new();
    for func in &module.functions {
        if func.blocks.is_empty() {
            continue;
        }
        let (precise, precise_arity) = solve(module, func.id, false);
        let (legacy, legacy_arity) = solve(module, func.id, true);
        assert!(
            precise_arity <= legacy_arity,
            "{what}::{}: precise relations ({precise_arity}) wider than legacy ({legacy_arity})",
            func.name
        );
        assert_eq!(precise, legacy, "{what}::{}: verdict changed with liveness", func.name);
        verdicts.push(precise);
    }
    verdicts
}

fn bundle_module(json: &str) -> Module {
    let bundle: trust_ir::NativeVerificationBundle =
        serde_json::from_str(json).expect("the dumped native bundle is valid JSON");
    bundle.module
}

#[test]
fn lowered_fixture_modules_keep_their_verdicts() {
    let fixtures = [
        (
            "recursive_requires",
            bundle_module(include_str!(
                "../../trust-mc-trust-bmc/tests/fixtures/recursive_requires_native_bundle.json"
            )),
        ),
        (
            "stale_struct",
            bundle_module(include_str!(
                "../../trust-mc-trust-bmc/tests/fixtures/stale_struct_native_bundle.json"
            )),
        ),
        (
            "format_args_insert_element",
            bundle_module(include_str!(
                "../../trust-mc-trust-bmc/tests/fixtures/format_args_insert_element_native_bundle.json"
            )),
        ),
        (
            "option_str_unwrap_or",
            serde_json::from_str(include_str!(
                "../../trust-mc-trust-bmc/tests/fixtures/option_str_unwrap_or_seal9178.module.json"
            ))
            .expect("the dumped module is valid JSON"),
        ),
    ];
    let mut functions = 0;
    for (name, module) in &fixtures {
        let verdicts = assert_parity(module, name);
        if std::env::var_os("PARITY_DEBUG").is_some() {
            eprintln!("{name}: {verdicts:?}");
        }
        functions += verdicts.len();
    }
    assert!(functions >= 8, "the fixture corpus shrank to {functions} functions");
}

/// `i = 0; while i < bound { assert(i + 1 does not overflow); i += 1 }`, the
/// counter a promoted cell carried around the back edge, with `bound` an entry
/// param threaded to the header. Proved only if both survive in the relations.
fn counting_loop(bound_is_param: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("counting_loop");
    let ft = mb.add_func_type(vec![Ty::U32], vec![Ty::U32]);
    let mut fb = mb.function("count", ft);
    let (entry, header, body, exit) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    let param = fb.add_block_param(entry, Ty::U32);
    fb.switch_to_block(entry);
    let counter = fb.alloca(Ty::U32);
    let zero = fb.iconst(Ty::U32, 0);
    fb.store(Ty::U32, counter, zero);
    fb.br(header, vec![]);
    fb.switch_to_block(header);
    let current = fb.load(Ty::U32, counter);
    let bound = if bound_is_param { param } else { fb.iconst(Ty::U32, 10) };
    let more = fb.icmp(ICmpOp::Ult, Ty::U32, current, bound);
    fb.condbr(more, body, vec![], exit, vec![]);
    fb.switch_to_block(body);
    let current = fb.load(Ty::U32, counter);
    let one = fb.iconst(Ty::U32, 1);
    let (next, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U32, current, one);
    let no = fb.bool_const(false);
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
    fb.assert(ok);
    fb.store(Ty::U32, counter, next);
    fb.br(header, vec![]);
    fb.switch_to_block(exit);
    let done = fb.load(Ty::U32, counter);
    fb.ret(vec![done]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// A value made in one block, carried untouched across a diamond, and checked
/// after the join — refuted when `refutable`, proved otherwise.
fn carried_across_a_diamond(refutable: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("diamond");
    let ft = mb.add_func_type(vec![Ty::U8, Ty::Bool], vec![]);
    let mut fb = mb.function("diamond", ft);
    let (entry, left, right, join) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    let x = fb.add_block_param(entry, Ty::U8);
    let c = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let limit = fb.iconst(Ty::U8, 100);
    let small = fb.icmp(ICmpOp::Ult, Ty::U8, x, limit);
    fb.assume(small);
    fb.condbr(c, left, vec![], right, vec![]);
    fb.switch_to_block(left);
    fb.br(join, vec![]);
    fb.switch_to_block(right);
    fb.br(join, vec![]);
    fb.switch_to_block(join);
    let addend = fb.iconst(Ty::U8, if refutable { 200 } else { 100 });
    let (_, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U8, x, addend);
    let no = fb.bool_const(false);
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
    fb.assert(ok);
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// The ever-init cleanup-chain shape (see trust-mc-trust-bmc's liveness tests):
/// per local a drop flag set, cleared and re-tested by a cleanup chain that
/// every unwind choice can enter, and an overflow-checked running sum.
fn ever_init(n: usize) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("ever_init");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("many_locals", ft);
    let entry = fb.create_block();
    let make: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let add: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let exit = fb.create_block();
    let cleanup: Vec<BlockId> = (0..=n).map(|_| fb.create_block()).collect();
    let drop: Vec<BlockId> = (0..=n).map(|_| fb.create_block()).collect();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let sum = fb.alloca(Ty::U64);
    let zero = fb.iconst(Ty::U64, 0);
    fb.store(Ty::U64, sum, zero);
    let mut flags = Vec::with_capacity(n);
    for _ in 0..n {
        let flag = fb.alloca(Ty::Bool);
        let no = fb.bool_const(false);
        fb.store(Ty::Bool, flag, no);
        flags.push(flag);
    }
    fb.br(make[0], vec![]);
    for i in 0..n {
        fb.switch_to_block(make[i]);
        let yes = fb.bool_const(true);
        fb.store(Ty::Bool, flags[i], yes);
        let unwinds = fb.undef(Ty::Bool);
        fb.condbr(unwinds, cleanup[i], vec![], add[i], vec![]);
        fb.switch_to_block(add[i]);
        let before = fb.load(Ty::U64, sum);
        let one = fb.iconst(Ty::U64, 1);
        let (total, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, before, one);
        let no = fb.bool_const(false);
        let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
        fb.assert(ok);
        fb.store(Ty::U64, sum, total);
        let no = fb.bool_const(false);
        fb.store(Ty::Bool, flags[i], no);
        let drop_unwinds = fb.undef(Ty::Bool);
        let next = if i + 1 < n { make[i + 1] } else { exit };
        fb.condbr(drop_unwinds, cleanup[i + 1], vec![], next, vec![]);
    }
    fb.switch_to_block(exit);
    let result = fb.load(Ty::U64, sum);
    fb.ret(vec![result]);
    fb.switch_to_block(cleanup[0]);
    let unwound = fb.undef(Ty::U64);
    fb.ret(vec![unwound]);
    for i in 1..=n {
        fb.switch_to_block(cleanup[i]);
        let live = fb.load(Ty::Bool, flags[i - 1]);
        let no = fb.bool_const(false);
        let dead = fb.icmp(ICmpOp::Eq, Ty::Bool, live, no);
        fb.condbr(dead, cleanup[i - 1], vec![], drop[i], vec![]);
        fb.switch_to_block(drop[i]);
        let dropped = fb.bool_const(true);
        fb.assert(dropped);
        fb.br(cleanup[i - 1], vec![]);
    }
    fb.switch_to_block(drop[0]);
    fb.unreachable();
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

#[test]
fn generated_families_keep_their_verdicts() {
    let mut decided = Vec::new();
    for (name, (module, _)) in [
        ("counting_loop(param bound)", counting_loop(true)),
        ("counting_loop(constant bound)", counting_loop(false)),
        ("diamond(proved)", carried_across_a_diamond(false)),
        ("diamond(refuted)", carried_across_a_diamond(true)),
        ("ever_init(1)", ever_init(1)),
        ("ever_init(2)", ever_init(2)),
        ("ever_init(3)", ever_init(3)),
    ] {
        decided.push((name, assert_parity(&module, name)));
    }
    if std::env::var_os("PARITY_DEBUG").is_some() {
        eprintln!("{decided:?}");
    }
    // The corpus must actually decide things in both directions, or parity would
    // be vacuous.
    let all: Vec<Verdict> = decided.iter().flat_map(|(_, v)| v.iter().copied()).collect();
    assert!(all.contains(&Verdict::Proved), "{decided:?}");
    assert!(all.contains(&Verdict::Refuted), "{decided:?}");
}
