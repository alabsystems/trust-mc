// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Design step 8e: a counterexample of the large-block encoding maps back to a
//! per-block derivation.
//!
//! trust-mc-trust-bmc makes an acyclic function one non-recursive query
//! (`translate_chc_large_block.rs`). Its equisatisfiability argument's (L ⇒ S)
//! half walks a model's true selectors back from a true error site
//! (`LargeBlockMap::counterexample_path`) and claims the per-block encoding
//! derives `error` along that block path. These tests check the claim on the
//! engine's own witnesses: the acyclic composer refutes the large-block query,
//! the witness's model is mapped to its block path, and the per-block CHC cut
//! down to EXACTLY the rules that path uses — the entry fact pinned to the
//! witness's inputs, each transition the selected selector names, the error
//! rule of the site — must still derive `error`. They also pin that the
//! consumer's refutation replay (the model-aware havoc gate) admits a
//! large-block witness whenever it admits the per-block one.

use std::collections::BTreeMap;

use ay_bindings::Expr;
use trust_ir::Module;
use trust_ir::inst::{ICmpOp, OverflowOp};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir_build::ModuleBuilder;
use trust_mc_core::chc::{Rule, RuleBody};

use super::*;
use crate::direct_smt_cex::{
    AcyclicDecision, acyclic_direct_smt_decision, alpha_renamed_variable_names,
};

struct Lcg(u64);

impl Lcg {
    fn below(&mut self, bound: usize) -> usize {
        self.0 =
            self.0.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        ((self.0 >> 33) as usize) % bound
    }
}

/// An acyclic SSA function: block `i` branches only forward and reads the entry
/// parameters, its own parameter, its own values and two promoted cells; joins
/// merge differing arguments; havocs sit both on and off the failing paths.
fn random_acyclic(seed: u64, blocks: usize) -> (Module, FuncId) {
    let mut rng = Lcg(seed);
    let mut mb = ModuleBuilder::new("large_block_witness");
    let ft = mb.add_func_type(vec![Ty::U8, Ty::U8, Ty::Bool], vec![]);
    let mut fb = mb.function("random_acyclic", ft);
    let ids: Vec<BlockId> = (0..blocks).map(|_| fb.create_block()).collect();
    fb.set_entry(ids[0]);
    let entry_values = vec![fb.add_block_param(ids[0], Ty::U8), fb.add_block_param(ids[0], Ty::U8)];
    let flag = fb.add_block_param(ids[0], Ty::Bool);
    let params: Vec<Option<ValueId>> = (0..blocks)
        .map(|index| {
            (index > 0 && rng.below(2) == 0).then(|| fb.add_block_param(ids[index], Ty::U8))
        })
        .collect();
    fb.switch_to_block(ids[0]);
    let cells = [fb.alloca(Ty::U8), fb.alloca(Ty::U8)];
    fb.store(Ty::U8, cells[0], entry_values[1]);
    let three = fb.iconst(Ty::U8, 3);
    fb.store(Ty::U8, cells[1], three);
    for index in 0..blocks {
        if index > 0 {
            fb.switch_to_block(ids[index]);
        }
        let mut values = entry_values.clone();
        values.extend(params[index]);
        for _ in 0..=rng.below(3) {
            match rng.below(6) {
                0 => {
                    let cell = cells[rng.below(2)];
                    values.push(fb.load(Ty::U8, cell));
                }
                1 => {
                    let cell = cells[rng.below(2)];
                    let value = values[rng.below(values.len())];
                    fb.store(Ty::U8, cell, value);
                }
                2 => {
                    let (lhs, rhs) =
                        (values[rng.below(values.len())], values[rng.below(values.len())]);
                    let (sum, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U8, lhs, rhs);
                    let no = fb.bool_const(false);
                    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
                    fb.assert(ok);
                    values.push(sum);
                }
                3 => {
                    let value = values[rng.below(values.len())];
                    let forbidden = fb.iconst(Ty::U8, 40 + rng.below(40) as i128);
                    let ok = fb.icmp(ICmpOp::Ne, Ty::U8, value, forbidden);
                    fb.assert(ok);
                }
                4 => values.push(fb.undef(Ty::U8)),
                _ => {
                    let value = values[rng.below(values.len())];
                    let bound = fb.iconst(Ty::U8, 100);
                    let small = fb.icmp(ICmpOp::Ult, Ty::U8, value, bound);
                    fb.assume(small);
                }
            }
        }
        let args_for = |rng: &mut Lcg, target: usize, values: &[ValueId]| -> Vec<ValueId> {
            params[target].map(|_| values[rng.below(values.len())]).into_iter().collect()
        };
        if index + 1 == blocks {
            fb.ret(vec![]);
            continue;
        }
        let later = |rng: &mut Lcg| index + 1 + rng.below(blocks - index - 1);
        if rng.below(3) == 0 {
            let target = later(&mut rng);
            let args = args_for(&mut rng, target, &values);
            fb.br(ids[target], args);
        } else {
            let cond = if rng.below(2) == 0 {
                flag
            } else {
                let (lhs, rhs) = (values[rng.below(values.len())], values[rng.below(values.len())]);
                fb.icmp(ICmpOp::Ult, Ty::U8, lhs, rhs)
            };
            let (then_target, else_target) = (later(&mut rng), later(&mut rng));
            let then_args = args_for(&mut rng, then_target, &values);
            let else_args = args_for(&mut rng, else_target, &values);
            fb.condbr(cond, ids[then_target], then_args, ids[else_target], else_args);
        }
    }
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

fn obligation(vc: trust_mc_core::chc::ChcVc, id: &str) -> trust_mc_core::MirChcPdrObligation {
    trust_mc_core::MirChcPdrObligation::new(
        id.to_owned(),
        "random_acyclic",
        trust_mc_core::MirObligationKind::Assertion,
        vc,
    )
}

/// A witness model's value as a constant term of `sort`, for the scalar sorts
/// the generated functions use.
fn constant(value: &serde_json::Value, sort: &ay_bindings::Sort) -> Option<Expr> {
    match value.get("kind")?.as_str()? {
        "bool" => Some(Expr::bool_const(value.get("value")?.as_bool()?)),
        "bit_vec" => {
            let width = sort.bitvec_width()?;
            let digits: u128 = value.get("value")?.as_str()?.parse().ok()?;
            Some(Expr::bitvec_const(digits, width))
        }
        _ => None,
    }
}

/// What the replay of one witness established.
#[derive(Debug, Default)]
struct Replayed {
    refuted: usize,
    paths_replayed: usize,
    consumer_large_block: usize,
    consumer_per_block: usize,
}

/// Refute `func`'s large-block query with the composer, map the witness to its
/// block path, and check that the per-block CHC restricted to that path's rules
/// derives `error` from the witness's inputs.
fn replay_through_the_per_block_encoding(module: &Module, func: FuncId, replayed: &mut Replayed) {
    let options = trust_mc_trust_bmc::TranslateOptions::default();
    let large =
        trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output(module, func, &options)
            .expect("translates");
    let per_block = trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output_per_block(
        module, func, &options,
    )
    .expect("translates");
    let Some(map) = large.large_block.clone() else {
        return;
    };
    let problem = typed_chc_ay::lower_obligation(&obligation(large.vc.clone(), "large"))
        .expect("the large-block query lowers");
    let AcyclicDecision::Unsafe(witness) = acyclic_direct_smt_decision(&problem) else {
        return;
    };
    replayed.refuted += 1;

    // The error clause of the derivation, and its variables' witness names.
    let error_clause = witness
        .derivation_clause_indices
        .iter()
        .map(|index| usize::try_from(*index).expect("index"))
        .find(|index| {
            matches!(&problem.clauses()[*index].head, ay_chc::ClauseHead::Predicate(id, _)
                if problem.get_predicate(*id).is_some_and(|p| p.name == "error"))
        })
        .expect("the derivation reaches error");
    let names = alpha_renamed_variable_names(&problem).expect("renames")[error_clause].clone();
    let by_name: BTreeMap<String, String> =
        names.iter().map(|(var, renamed)| (var.name.clone(), renamed.clone())).collect();
    let model = witness.model.as_object().expect("a model object").clone();
    let lookup = |var: &str| -> Option<bool> {
        let renamed = by_name.get(var)?;
        model.get(renamed)?.get("value")?.as_bool()
    };
    let path = map.counterexample_path(lookup).expect("a model of the query maps to a block path");
    assert_eq!(path.blocks.first(), Some(&map.root));
    // JUSTIFICATION: the model's true Booleans are that one derivation and no
    // more — every true selector is an edge of the path, every true site sits in
    // its last block, every reached block is on it.
    let on_path = |block: &BlockId| path.blocks.contains(block);
    for (target, edges) in &map.in_edges {
        for edge in edges {
            if lookup(&edge.selector) == Some(true) {
                let edge_on_path =
                    path.blocks.windows(2).any(|pair| pair[0] == edge.source && pair[1] == *target);
                assert!(
                    edge_on_path,
                    "selector {} true off the path {:?}",
                    edge.selector, path.blocks
                );
            }
        }
        if lookup(&format!("bb{}_lbe_r", target.index())) == Some(true) {
            assert!(on_path(target), "bb{} reached off the path {:?}", target.index(), path.blocks);
        }
    }
    for site in &map.sites {
        if lookup(&site.var) == Some(true) {
            assert_eq!(
                Some(&site.block),
                path.blocks.last(),
                "site {} true off the path",
                site.var
            );
        }
    }

    // The per-block rules the path uses: the k-th emission of block B is B's
    // k-th rule (both encodings run B's translation, which emits in order).
    let rules_of = |block: BlockId| -> Vec<usize> {
        let name = format!("bb{}", block.index());
        per_block
            .vc
            .rules
            .iter()
            .enumerate()
            .filter(|(_, rule)| {
                rule.body.relation.as_ref().is_some_and(|app| app.name.as_str() == name)
            })
            .map(|(index, _)| index)
            .collect()
    };
    let emission = |var: &str| -> usize {
        let digits: String = var.chars().rev().take_while(char::is_ascii_digit).collect();
        digits.chars().rev().collect::<String>().parse().expect("an emission index")
    };
    let mut kept = vec![0usize];
    for pair in path.blocks.windows(2) {
        let (source, target) = (pair[0], pair[1]);
        let selector = map.in_edges[&target]
            .iter()
            .find(|edge| edge.source == source && lookup(&edge.selector) == Some(true))
            .expect("the path's edge is a true selector");
        let index = rules_of(source)[emission(&selector.selector)];
        assert_eq!(
            per_block.vc.rules[index].head.name.as_str(),
            format!("bb{}", target.index()),
            "the selector's emission is the per-block transition into its target"
        );
        kept.push(index);
    }
    let site_rule = rules_of(path.site.block)[emission(&path.site.var)];
    assert_eq!(per_block.vc.rules[site_rule].head.name.as_str(), "error");
    kept.push(site_rule);

    // Pin the entry fact to the witness's inputs.
    let mut restricted = per_block.vc.clone();
    let entry_args: Vec<Expr> = restricted.rules[0].head.args.iter().cloned().collect();
    let mut pins = Vec::new();
    for arg in &entry_args {
        let ay_bindings::ExprValue::Var { name } = arg.value() else { continue };
        let Some(value) = by_name.get(name).and_then(|renamed| model.get(renamed)) else {
            continue;
        };
        if let Some(constant) = constant(value, arg.sort()) {
            pins.push(arg.clone().eq(constant));
        }
    }
    let entry = restricted.rules[0].head.clone();
    restricted.rules = kept.iter().map(|index| per_block.vc.rules[*index].clone()).collect();
    restricted.rules[0] = Rule::new(RuleBody::new(None, pins), entry);
    let restricted_problem = typed_chc_ay::lower_obligation(&obligation(restricted, "path"))
        .expect("the path's per-block rules lower");
    assert!(
        matches!(acyclic_direct_smt_decision(&restricted_problem), AcyclicDecision::Unsafe(_)),
        "the per-block rules along {:?} must derive error from the witness's inputs",
        path.blocks
    );
    replayed.paths_replayed += 1;
}

#[test]
fn large_block_counterexamples_replay_along_their_per_block_paths() {
    let mut replayed = Replayed::default();
    for seed in 0..40u64 {
        let (module, func) = random_acyclic(seed, 3 + seed as usize % 6);
        replay_through_the_per_block_encoding(&module, func, &mut replayed);
    }
    assert!(replayed.refuted >= 10, "the corpus must refute: {replayed:?}");
    assert_eq!(replayed.paths_replayed, replayed.refuted, "{replayed:?}");
}

/// The consumer's refutation replay admits a large-block witness whenever it
/// admits the per-block witness of the same function: the havoc gate reads only
/// the witness's path.
#[test]
fn the_consumer_admits_large_block_witnesses_like_per_block_ones() {
    let options = trust_mc_trust_bmc::TranslateOptions::default();
    let mut replayed = Replayed::default();
    for seed in 0..40u64 {
        let (module, func) = random_acyclic(seed, 3 + seed as usize % 6);
        let mut admitted = [false; 2];
        let mut refusals: [Option<String>; 2] = [None, None];
        for (slot, per_block) in [false, true].into_iter().enumerate() {
            let output = if per_block {
                trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output_per_block(
                    &module, func, &options,
                )
            } else {
                trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output(
                    &module, func, &options,
                )
            }
            .expect("translates");
            let obligation = obligation(output.vc, &format!("consumer-{seed}"));
            let options = trust_mc_core::ChcPdrSolveOptions::default()
                .with_timeout(std::time::Duration::from_secs(20));
            let engine = options.engine;
            let request =
                trust_mc_core::ChcPdrSolveRequest::new(obligation.clone()).with_options(options);
            let Ok(solved) = solve_typed_chc_pdr_full_verification(request) else {
                continue;
            };
            let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
                &solved.outcome.status
            else {
                continue;
            };
            match independently_replay_typed_chc_pdr_refutation_witness(
                &obligation,
                engine,
                witness,
            ) {
                Ok(_) => admitted[slot] = true,
                Err(error) => refusals[slot] = Some(error.to_string()),
            }
        }
        replayed.consumer_large_block += usize::from(admitted[0]);
        replayed.consumer_per_block += usize::from(admitted[1]);
        assert!(
            admitted[0] || !admitted[1],
            "seed {seed}: the consumer admits the per-block witness but not the large-block one: {:?}",
            refusals[0]
        );
    }
    assert!(replayed.consumer_large_block > 0, "{replayed:?}");
}

// ---------------------------------------------------------------------------
// Fat pointers across blocks, against the trust-ir reference interpreter (the
// 8e soundness review). A slice built by `PtrFromParts` in one block and read
// in another: the large-block query reads its parts EXACTLY where the building
// block dominates the reader; the per-block encoding reads them as an OPAQUE
// value (an unbounded havoc), never the `isize::MAX`-bounded `slice_len`
// symbol (the false proof the review found) and never an earlier rule's
// variables free (the spurious refutation the review found).
// ---------------------------------------------------------------------------

use trust_ir::inst::{CastOp, SwitchCase};
use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, InterpretValue, Interpreter};
use trust_ir::ty::FatPtrKind;

/// The interpreter domain of `n: u64`, `a: u8` and `flag: bool`: the boundary
/// values the generated constants are drawn from.
const N_PIVOTS: [u128; 11] =
    [0, 1, 2, 9, 10, 255, 1 << 32, (1 << 63) - 1, 1 << 63, u64::MAX as u128 - 1, u64::MAX as u128];
const A_PIVOTS: [u128; 8] = [0, 1, 9, 10, 127, 128, 254, 255];

/// A verdict as the consumer stands behind it: a refutation counts only when
/// the consumer's independent replay (havoc gate included) admits its witness;
/// an engine refutation it refuses is a refutation of the encoding, not of the
/// program.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Standing {
    Proved,
    Refuted,
    AbstractRefuted,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Execution {
    Completed,
    Trap(String),
    OutsideDomain,
    Incapable(String),
}

fn execute(module: &Module, n: u128, a: u128, flag: bool) -> Execution {
    let function = module.function_by_name("f").expect("f is generated");
    let interpreter = Interpreter::with_module(module)
        .with_options(InterpretOptions { fuel: 100_000, ..InterpretOptions::default() });
    let args = vec![
        InterpretValue::int(Ty::U64, n as i128).expect("a u64 input"),
        InterpretValue::int(Ty::U8, a as i128).expect("a u8 input"),
        InterpretValue::bool(flag),
    ];
    match interpreter.execute_function(function, args) {
        Ok(_) => Execution::Completed,
        Err(error) if error.code == InterpretErrorCode::Panic => Execution::Trap(error.message),
        Err(error) if error.code == InterpretErrorCode::AssumeViolated => Execution::OutsideDomain,
        Err(error) => Execution::Incapable(format!("{:?}: {}", error.code, error.message)),
    }
}

/// The standing of `output`'s verdict, and for an admitted refutation the
/// witness's entry inputs (`None` for one the derivation leaves free).
fn standing(
    output: trust_mc_trust_bmc::ChcTranslationOutput,
    id: &str,
) -> (Standing, Option<Vec<Option<serde_json::Value>>>) {
    let obligation = obligation(output.vc, id);
    let options = trust_mc_core::ChcPdrSolveOptions::default()
        .with_timeout(std::time::Duration::from_secs(20));
    let engine = options.engine;
    let request = trust_mc_core::ChcPdrSolveRequest::new(obligation.clone()).with_options(options);
    let Ok(solved) = solve_typed_chc_pdr_full_verification(request) else {
        return (Standing::Unknown, None);
    };
    match &solved.verdict {
        trust_mc_core::FullVerificationVerdict::Proved { .. } => (Standing::Proved, None),
        trust_mc_core::FullVerificationVerdict::Failed { .. } => {
            let trust_mc_core::ChcPdrSolveStatus::Refuted { witness: Some(witness) } =
                &solved.outcome.status
            else {
                return (Standing::AbstractRefuted, None);
            };
            if independently_replay_typed_chc_pdr_refutation_witness(&obligation, engine, witness)
                .is_err()
            {
                return (Standing::AbstractRefuted, None);
            }
            let payload: DirectSmtRefutationReplayPayload =
                serde_json::from_str(&witness.counterexample_json).expect("an admitted payload");
            if payload.unroll_k.is_some() {
                return (Standing::Refuted, None);
            }
            let problem = prepare_validated_typed_chc_pdr_input(&obligation)
                .expect("the obligation prepares")
                .problem
                .expect("the obligation lowers");
            let direct = crate::direct_smt_cex::AcyclicUnsafeWitness {
                model: payload.witness_model,
                derivation_clause_indices: payload.derivation_clause_indices,
            };
            let inputs = crate::direct_smt_cex::witness_entry_fact_assignment(&problem, &direct)
                .expect("an admitted witness names its entry inputs");
            (Standing::Refuted, Some(inputs))
        }
        _ => (Standing::Unknown, None),
    }
}

/// A model value as the bits it denotes.
fn decoded(value: &serde_json::Value) -> Option<u128> {
    match value.get("kind")?.as_str()? {
        "bool" => Some(u128::from(value.get("value")?.as_bool()?)),
        "bit_vec" => value.get("value")?.as_str()?.parse().ok(),
        _ => None,
    }
}

/// What one function's two encodings and the interpreter said.
#[derive(Debug, Default)]
struct Differential {
    functions: usize,
    proved: usize,
    refuted: usize,
    decided_only_as_one_query: usize,
    executions: usize,
}

/// Decide `module`'s `f` under both encodings and hold each decided verdict to
/// the interpreter (when `interpretable`): a proof traps on no input of the
/// domain, an admitted refutation's inputs trap (each input the derivation
/// leaves free, at every pivot tried); the two encodings never contradict, and
/// the large-block query decides everything the per-block encoding decides.
fn hold_to_ground_truth(
    module: &Module,
    what: &str,
    interpretable: bool,
    tally: &mut Differential,
) -> Standing {
    let errors = trust_ir_build::validate_module(module);
    assert!(errors.is_empty(), "{what}: differential input must be canonical: {errors:?}");
    let options = trust_mc_trust_bmc::TranslateOptions::default();
    let func = module.function_by_name("f").expect("f").id;
    let large =
        trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output(module, func, &options)
            .expect("translates");
    assert!(large.large_block.is_some(), "{what}: acyclic, so one query");
    assert_eq!(large.work.large_block_fallbacks, 0, "{what}");
    let per_block = trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output_per_block(
        module, func, &options,
    )
    .expect("translates");
    let (large, inputs) = standing(large, &format!("{what}-large"));
    let (per_block, _) = standing(per_block, &format!("{what}-per-block"));
    tally.functions += 1;
    match per_block {
        Standing::Proved | Standing::Refuted => assert_eq!(
            large, per_block,
            "{what}: the per-block encoding decides {per_block:?}, the large-block query {large:?}"
        ),
        Standing::AbstractRefuted | Standing::Unknown => {
            if matches!(large, Standing::Proved | Standing::Refuted) {
                tally.decided_only_as_one_query += 1;
            }
        }
    }
    match large {
        Standing::Proved if !interpretable => tally.proved += 1,
        Standing::Refuted if !interpretable => tally.refuted += 1,
        Standing::Proved => {
            tally.proved += 1;
            for n in N_PIVOTS {
                for a in A_PIVOTS {
                    for flag in [false, true] {
                        tally.executions += 1;
                        match execute(module, n, a, flag) {
                            Execution::Completed | Execution::OutsideDomain => {}
                            Execution::Trap(message) => panic!(
                                "{what}: FALSE PROOF — proved, but the interpreter traps on \
                                 n={n} a={a} flag={flag}: {message}"
                            ),
                            Execution::Incapable(message) => {
                                panic!("{what}: the interpreter cannot run n={n} a={a}: {message}")
                            }
                        }
                    }
                }
            }
        }
        Standing::Refuted => {
            tally.refuted += 1;
            let inputs = inputs.expect("a direct-SMT witness");
            assert_eq!(inputs.len(), 3, "{what}: the entry fact binds n, a, flag");
            let candidates = |index: usize, pivots: &[u128]| -> Vec<u128> {
                match inputs[index].as_ref() {
                    Some(value) => vec![decoded(value).expect("a scalar model value")],
                    None => vec![pivots[0], pivots[pivots.len() - 1]],
                }
            };
            for n in candidates(0, &N_PIVOTS) {
                for a in candidates(1, &A_PIVOTS) {
                    for flag in candidates(2, &[0, 1]) {
                        tally.executions += 1;
                        let run = execute(module, n, a, flag == 1);
                        assert!(
                            matches!(run, Execution::Trap(_)),
                            "{what}: an admitted refutation's inputs n={n} a={a} flag={flag} do \
                             not trap: {run:?}"
                        );
                    }
                }
            }
        }
        Standing::AbstractRefuted | Standing::Unknown => {}
    }
    large
}

fn slice_of_u8(mb: &mut ModuleBuilder) -> Ty {
    let u8_id = mb.add_type(Ty::U8);
    Ty::FatPtr(FatPtrKind::Slice(u8_id))
}

/// `len = PtrMetadata(fat)` followed by the overflow-checked `len + 1`.
fn assert_len_plus_one(fb: &mut trust_ir_build::FunctionBuilder<'_>, fat_ty: &Ty, fat: ValueId) {
    let len = fb.ptr_metadata(fat_ty.clone(), Ty::U64, fat);
    let one = fb.iconst(Ty::U64, 1);
    let (_, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, len, one);
    let no = fb.bool_const(false);
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
    fb.assert(ok);
}

/// How the reading block reaches the slice.
#[derive(Debug, Clone, Copy)]
enum Reach {
    /// The entry's own value, read in its successor.
    Direct,
    /// A `Copy` made in the successor and read in the next block.
    Copied,
    /// A same-type `PtrToPtr` cast made in the successor, read in the next.
    /// (The interpreter executes no cast of a fat pointer; the variant must
    /// decide exactly as `Copied` does — the cast is the identity.)
    Cast,
    /// Read in the join of a diamond on `flag`.
    Join,
}

/// The review's blocker: `f(n, a, flag)` builds `fat = PtrFromParts(null, n)`
/// in the entry (after `assume(n < 10)` when `bounded`) and checks
/// `PtrMetadata(fat) + 1` for overflow in a later block. Unbounded, it traps at
/// `n = u64::MAX`; bounded, it never traps.
fn slice_across_blocks(reach: Reach, bounded: bool) -> Module {
    let count = match reach {
        Reach::Direct => 2,
        Reach::Copied | Reach::Cast => 3,
        Reach::Join => 4,
    };
    slice_across_allocated_blocks(reach, bounded, count)
}

fn slice_across_allocated_blocks(reach: Reach, bounded: bool, count: usize) -> Module {
    let mut mb = ModuleBuilder::new("slice_across_blocks");
    let fat_ty = slice_of_u8(&mut mb);
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U8, Ty::Bool], vec![]);
    let mut fb = mb.function("f", ft);
    let blocks: Vec<BlockId> = (0..count).map(|_| fb.create_block()).collect();
    fb.set_entry(blocks[0]);
    let n = fb.add_block_param(blocks[0], Ty::U64);
    let _a = fb.add_block_param(blocks[0], Ty::U8);
    let flag = fb.add_block_param(blocks[0], Ty::Bool);
    fb.switch_to_block(blocks[0]);
    if bounded {
        let ten = fb.iconst(Ty::U64, 10);
        let small = fb.icmp(ICmpOp::Ult, Ty::U64, n, ten);
        fb.assume(small);
    }
    let null = fb.null_ptr();
    let fat = fb.ptr_from_parts(fat_ty.clone(), Ty::U64, null, n);
    match reach {
        Reach::Direct => {
            fb.br(blocks[1], vec![]);
            fb.switch_to_block(blocks[1]);
            assert_len_plus_one(&mut fb, &fat_ty, fat);
            fb.ret(vec![]);
        }
        Reach::Copied | Reach::Cast => {
            fb.br(blocks[1], vec![]);
            fb.switch_to_block(blocks[1]);
            let copy = if matches!(reach, Reach::Copied) {
                fb.copy(fat_ty.clone(), fat)
            } else {
                fb.cast(CastOp::PtrToPtr, fat_ty.clone(), fat_ty.clone(), fat)
            };
            fb.br(blocks[2], vec![]);
            fb.switch_to_block(blocks[2]);
            assert_len_plus_one(&mut fb, &fat_ty, copy);
            fb.ret(vec![]);
        }
        Reach::Join => {
            fb.condbr(flag, blocks[1], vec![], blocks[2], vec![]);
            for arm in [blocks[1], blocks[2]] {
                fb.switch_to_block(arm);
                fb.br(blocks[3], vec![]);
            }
            fb.switch_to_block(blocks[3]);
            assert_len_plus_one(&mut fb, &fat_ty, fat);
            fb.ret(vec![]);
        }
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

/// The review's spurious refutation: `assume(n < 10)`, `fat = PtrFromParts(null,
/// n)` in the entry, `assert(PtrMetadata(fat) < 10)` in its successor — TRUE.
fn bounded_length_asserted_later() -> Module {
    let mut mb = ModuleBuilder::new("bounded_length_asserted_later");
    let fat_ty = slice_of_u8(&mut mb);
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U8, Ty::Bool], vec![]);
    let mut fb = mb.function("f", ft);
    let (entry, next) = (fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    let n = fb.add_block_param(entry, Ty::U64);
    let _a = fb.add_block_param(entry, Ty::U8);
    let _flag = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    let ten = fb.iconst(Ty::U64, 10);
    let small = fb.icmp(ICmpOp::Ult, Ty::U64, n, ten);
    fb.assume(small);
    let null = fb.null_ptr();
    let fat = fb.ptr_from_parts(fat_ty.clone(), Ty::U64, null, n);
    fb.br(next, vec![]);
    fb.switch_to_block(next);
    let len = fb.ptr_metadata(fat_ty, Ty::U64, fat);
    let ten = fb.iconst(Ty::U64, 10);
    let ok = fb.icmp(ICmpOp::Ult, Ty::U64, len, ten);
    fb.assert(ok);
    fb.ret(vec![]);
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn slices_across_blocks_hold_to_the_interpreter() {
    let mut tally = Differential::default();
    for reach in [Reach::Direct, Reach::Copied, Reach::Cast, Reach::Join] {
        let interpretable = !matches!(reach, Reach::Cast);
        // `n = u64::MAX` overflows `len + 1`: refuted in the large-block query
        // with the entry's own `n` (it was PROVED from a bounded `slice_len`
        // symbol before the review), never proved by either encoding.
        let module = slice_across_blocks(reach, false);
        let what = format!("{reach:?} unbounded");
        let large = hold_to_ground_truth(&module, &what, interpretable, &mut tally);
        assert_eq!(large, Standing::Refuted, "{what}");
        // `n < 10`: proved in the large-block query.
        let module = slice_across_blocks(reach, true);
        let what = format!("{reach:?} bounded");
        let large = hold_to_ground_truth(&module, &what, interpretable, &mut tally);
        assert_eq!(large, Standing::Proved, "{what}");
    }
    // The true property the per-block encoding used to "refute" through an
    // earlier rule's free variable (and the consumer admitted): proved as one
    // query, never an admitted refutation per block (`hold_to_ground_truth`
    // fails on a per-block `Refuted` against a large-block `Proved`).
    let large =
        hold_to_ground_truth(&bounded_length_asserted_later(), "bounded length", true, &mut tally);
    assert_eq!(large, Standing::Proved);
    assert!(tally.decided_only_as_one_query > 0, "{tally:?}");
}

fn assert_unreachable_input_refused(module: &Module, what: &str) {
    let errors = trust_ir_build::validate_module(module);
    assert!(
        errors
            .iter()
            .any(|error| matches!(error, trust_ir_build::ValidationError::UnreachableBlock(_))),
        "{what}: original unreachable blocks stay diagnosed: {errors:?}"
    );
    let func = module.function_by_name("f").expect("f").id;
    let options = trust_mc_trust_bmc::TranslateOptions::default();
    for output in [
        trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output(module, func, &options)
            .expect("existing selection"),
        trust_mc_trust_bmc::trust_ir_function_to_chc_translation_output_per_block(
            module, func, &options,
        )
        .expect("existing selection"),
    ] {
        assert!(output.module_input_refusal.is_some(), "{what}");
        assert!(output.diagnostics.is_empty(), "invalidity has no invented instruction site");
        assert!(output.large_block.is_none());
        assert_eq!(output.vc.rules.len(), 1);
        let rule = &output.vc.rules[0];
        assert_eq!(rule.head.name, "error");
        assert!(rule.body.relation.is_none());
        assert!(rule.body.constraints.is_empty());
    }
}

#[test]
fn original_unused_slice_blocks_are_canonical_input_refusals() {
    for reach in [Reach::Direct, Reach::Copied, Reach::Cast] {
        for bounded in [false, true] {
            // The original generator allocated four blocks for every shape,
            // leaving one or two unreachable, unterminated blocks behind.
            let original = slice_across_allocated_blocks(reach, bounded, 4);
            assert_unreachable_input_refused(&original, &format!("{reach:?}/{bounded}"));
        }
    }
}

/// A random acyclic function over fat pointers: the entry builds two slices
/// from a null data pointer — `PtrFromParts(null, n)` and `PtrFromParts(null,
/// zext a)` (a compound length) — and every block reads them (they dominate
/// it), copies them (a cast of a fat pointer is not executable by the
/// interpreter; `slices_across_blocks_hold_to_the_interpreter` pins it to the
/// copy), checks their data's address is 0, checks their lengths with overflow
/// checks, asserts and assumptions, and branches on computed and passed
/// `bool`s. No `undef`: the interpreter runs every input.
fn random_fat(seed: u64, blocks: usize) -> Module {
    random_fat_input(seed, blocks, true)
}

fn random_fat_input(seed: u64, blocks: usize, reach_every_block: bool) -> Module {
    let mut rng = Lcg(seed);
    let mut mb = ModuleBuilder::new("large_block_fat");
    let fat_ty = slice_of_u8(&mut mb);
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U8, Ty::Bool], vec![]);
    let mut fb = mb.function("f", ft);
    let ids: Vec<BlockId> = (0..blocks).map(|_| fb.create_block()).collect();
    fb.set_entry(ids[0]);
    let n = fb.add_block_param(ids[0], Ty::U64);
    let a = fb.add_block_param(ids[0], Ty::U8);
    let flag = fb.add_block_param(ids[0], Ty::Bool);
    let params: Vec<Option<(ValueId, bool)>> = (0..blocks)
        .map(|index| match (index, rng.below(3)) {
            (0, _) | (_, 2) => None,
            (_, 0) => Some((fb.add_block_param(ids[index], Ty::U64), false)),
            _ => Some((fb.add_block_param(ids[index], Ty::Bool), true)),
        })
        .collect();
    fb.switch_to_block(ids[0]);
    let null = fb.null_ptr();
    let wide = fb.zext(Ty::U8, Ty::U64, a);
    let shared_fats = [
        fb.ptr_from_parts(fat_ty.clone(), Ty::U64, null, n),
        fb.ptr_from_parts(fat_ty.clone(), Ty::U64, null, wide),
    ];
    let constant = |rng: &mut Lcg| N_PIVOTS[rng.below(N_PIVOTS.len())] as i128;
    for index in 0..blocks {
        if index > 0 {
            fb.switch_to_block(ids[index]);
        }
        let mut words = vec![n, wide];
        let mut bools = vec![flag];
        match params[index] {
            Some((value, false)) => words.push(value),
            Some((value, true)) => bools.push(value),
            None => {}
        }
        let mut fats = shared_fats.to_vec();
        for _ in 0..=rng.below(4) {
            match rng.below(8) {
                0 | 1 => {
                    let fat = fats[rng.below(fats.len())];
                    words.push(fb.ptr_metadata(fat_ty.clone(), Ty::U64, fat));
                }
                2 => {
                    let value = words[rng.below(words.len())];
                    let step = fb.iconst(Ty::U64, [1, 2, 10, 1 << 63][rng.below(4)]);
                    let (sum, overflowed) =
                        fb.overflow(OverflowOp::AddOverflow, Ty::U64, value, step);
                    let no = fb.bool_const(false);
                    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
                    fb.assert(ok);
                    words.push(sum);
                }
                3 => {
                    let value = words[rng.below(words.len())];
                    let bound = fb.iconst(Ty::U64, [10, 256, 1 << 32, 1 << 63][rng.below(4)]);
                    let small = fb.icmp(ICmpOp::Ult, Ty::U64, value, bound);
                    fb.assume(small);
                }
                4 => {
                    let value = words[rng.below(words.len())];
                    let forbidden = fb.iconst(Ty::U64, constant(&mut rng));
                    let op = if rng.below(2) == 0 { ICmpOp::Ne } else { ICmpOp::Ult };
                    let ok = fb.icmp(op, Ty::U64, value, forbidden);
                    fb.assert(ok);
                }
                5 => {
                    let fat = fats[rng.below(fats.len())];
                    fats.push(fb.copy(fat_ty.clone(), fat));
                }
                6 => {
                    // The data part: the entry's null pointer, address 0.
                    let fat = fats[rng.below(fats.len())];
                    let data = fb.ptr_data(fat_ty.clone(), fat);
                    let address = fb.cast(CastOp::PtrToInt, Ty::Ptr, Ty::U64, data);
                    let zero = fb.iconst(Ty::U64, 0);
                    let ok = fb.icmp(ICmpOp::Eq, Ty::U64, address, zero);
                    fb.assert(ok);
                }
                _ => {
                    let (lhs, rhs) = (words[rng.below(words.len())], words[rng.below(words.len())]);
                    bools.push(fb.icmp(ICmpOp::Ult, Ty::U64, lhs, rhs));
                }
            }
        }
        let args_for = |rng: &mut Lcg, target: usize| -> Vec<ValueId> {
            match params[target] {
                Some((_, false)) => vec![words[rng.below(words.len())]],
                Some((_, true)) => vec![bools[rng.below(bools.len())]],
                None => Vec::new(),
            }
        };
        if index + 1 == blocks {
            fb.ret(vec![]);
            continue;
        }
        let later = |rng: &mut Lcg| index + 1 + rng.below(blocks - index - 1);
        match rng.below(5) {
            0 => {
                let target = later(&mut rng);
                let target = if reach_every_block { index + 1 } else { target };
                let args = args_for(&mut rng, target);
                fb.br(ids[target], args);
            }
            1 => {
                let selector = words[rng.below(words.len())];
                let cases = (0..=rng.below(2))
                    .map(|case| {
                        let target = later(&mut rng);
                        SwitchCase {
                            value: trust_ir::Constant::Int([0, 1, 10][case] as i128),
                            target: ids[target],
                            args: args_for(&mut rng, target),
                        }
                    })
                    .collect();
                let default = later(&mut rng);
                let default = if reach_every_block { index + 1 } else { default };
                let default_args = args_for(&mut rng, default);
                fb.switch(selector, cases, ids[default], default_args);
            }
            _ => {
                let cond = bools[rng.below(bools.len())];
                let (then_target, else_target) = (later(&mut rng), later(&mut rng));
                let then_target = if reach_every_block { index + 1 } else { then_target };
                let then_args = args_for(&mut rng, then_target);
                let else_args = args_for(&mut rng, else_target);
                fb.condbr(cond, ids[then_target], then_args, ids[else_target], else_args);
            }
        }
    }
    fb.build();
    mb.build().expect("ModuleBuilder::build: test fixture")
}

#[test]
fn random_fat_pointer_functions_hold_to_the_interpreter() {
    let mut tally = Differential::default();
    for seed in 0..48u64 {
        let module = random_fat(seed, 2 + seed as usize % 6);
        hold_to_ground_truth(&module, &format!("random_fat(seed {seed})"), true, &mut tally);
    }
    if std::env::var_os("PARITY_DEBUG").is_some() {
        eprintln!("{tally:?}");
    }
    assert!(tally.proved > 0 && tally.refuted > 0, "{tally:?}");
    assert!(tally.decided_only_as_one_query > 0, "{tally:?}");
}

#[test]
fn original_random_fat_inputs_execute_or_are_canonical_input_refusals() {
    let mut tally = Differential::default();
    let mut refused = 0;
    for seed in 0..48u64 {
        // Keep every original fixed-seed input. Its randomly skipped blocks
        // cannot be used as a positive translation/encoding oracle.
        let module = random_fat_input(seed, 2 + seed as usize % 6, false);
        let what = format!("original random_fat(seed {seed})");
        if trust_ir_build::validate_module(&module).is_empty() {
            hold_to_ground_truth(&module, &what, true, &mut tally);
        } else {
            assert_unreachable_input_refused(&module, &what);
            refused += 1;
        }
    }
    assert_eq!(tally.functions + refused, 48);
    assert!(refused > 0, "the original invalid inputs must remain exercised");
}
