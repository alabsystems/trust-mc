// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Verdict parity of the large-block encoding of an acyclic function against
//! the per-block encoding (design step 8e).
//!
//! trust-mc-trust-bmc makes an acyclic function ONE non-recursive query over the
//! entry's relation (`translate_chc_large_block.rs`), where the per-block
//! encoding gives every block a relation. The two are equisatisfiable (the
//! argument is in that module), so the native typed CHC/PDR solver may never
//! return CONTRADICTING verdicts on them (one proved, the other refuted), nor
//! leave undecided on the large-block query what it decides per block. Where
//! the per-block query stays undecided — the acyclic composer enumerates paths
//! per relation, the large-block query is one SMT problem — the large-block
//! verdict may be the decided one; such a function is held to the trust-ir
//! reference interpreter whenever it can run every input (no `undef`, scalar
//! parameters): a proof must trap on no input, a refutation on some. A
//! refutation counts only when the consumer's independent replay admits its
//! witness (its havoc gate included); an engine refutation the consumer refuses
//! refutes the encoding, not the program, and counts as undecided. Fat pointers
//! across blocks, against the interpreter, are trust-mc-driver's
//! `native/tests/large_block_tests.rs`.
//!
//! Corpus: every function of the lowered modules checked into
//! trust-mc-trust-bmc's fixtures (real `-Ztrust-dump` output of the compiler),
//! generated families (the ever-init cleanup chain, path-dependent drop flags,
//! joins whose arguments differ), and random acyclic SSA functions mixing
//! promoted cells, block parameters, havocs, assumptions, overflow checks,
//! assertions, switches with shared targets and blocks no path reaches, and
//! joins of in-degree up to several thousand.
//! Canonically invalid modules remain in the corpus as explicit input refusals;
//! their rows are neither solver verdicts nor evidence of encoding parity.

#![cfg(all(feature = "native-typed-chc-pdr", feature = "native-trust-ir-bundle"))]

use std::time::Duration;

use trust_ir::inst::{BinOp, ICmpOp, Inst, OverflowOp, SwitchCase};
use trust_ir::interpret::{InterpretErrorCode, InterpretValue, Interpreter};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Constant, Module};
use trust_ir_build::{ModuleBuilder, validate_module};
use trust_mc_core::{
    ChcPdrSolveOptions, ChcPdrSolveRequest, ChcPdrSolveStatus, FullVerificationVerdict,
    MirChcPdrObligation, MirObligationKind,
};
use trust_mc_trust_bmc::{
    ChcTranslationOutput, TranslateOptions, trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_per_block,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Proved,
    Refuted,
    Unknown,
}

/// Every corpus row is retained, including input the public translator refuses.
/// A refusal is not a solver refutation, proof or undecided solver attempt.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParityOutcome {
    Solver(Verdict),
    InvalidInput,
}

fn solve(output: ChcTranslationOutput, name: &str, id: usize) -> Verdict {
    assert!(
        output.module_input_refusal.is_none(),
        "{name}: module input refusals must be classified before invoking the solver"
    );
    let obligation = MirChcPdrObligation::new(
        format!("large-block-parity-{id}"),
        name.to_owned(),
        MirObligationKind::Assertion,
        output.vc,
    );
    if let Err(error) = obligation.validate() {
        if std::env::var_os("PARITY_DEBUG").is_some() {
            eprintln!("{name}: obligation validation: {error:?}");
        }
        return Verdict::Unknown;
    }
    let options = ChcPdrSolveOptions::default().with_timeout(Duration::from_secs(20));
    let engine = options.engine;
    let request = ChcPdrSolveRequest::new(obligation.clone()).with_options(options);
    let solved_result = trust_mc_driver::solve_typed_chc_pdr_full_verification(request);
    match solved_result {
        Ok(solved) => match solved.verdict {
            FullVerificationVerdict::Proved { .. } => Verdict::Proved,
            // Only a refutation the consumer stands behind.
            FullVerificationVerdict::Failed { .. } => match &solved.outcome.status {
                ChcPdrSolveStatus::Refuted { witness: Some(witness) } => {
                    match trust_mc_driver::independently_replay_typed_chc_pdr_refutation_witness(
                        &obligation,
                        engine,
                        witness,
                    ) {
                        Ok(_) => Verdict::Refuted,
                        Err(error) => {
                            if std::env::var_os("PARITY_DEBUG").is_some() {
                                eprintln!("{name}: independent witness replay: {error:?}");
                                eprintln!(
                                    "{name}: original obligation {obligation:#?}; witness {witness:#?}"
                                );
                            }
                            Verdict::Unknown
                        }
                    }
                }
                status => {
                    if std::env::var_os("PARITY_DEBUG").is_some() {
                        eprintln!("{name}: failed verdict with {status:?}");
                    }
                    Verdict::Unknown
                }
            },
            verdict => {
                if std::env::var_os("PARITY_DEBUG").is_some() {
                    eprintln!(
                        "{name}: full verdict {verdict:?}; status {:?}",
                        solved.outcome.status
                    );
                }
                Verdict::Unknown
            }
        },
        Err(error) => {
            if std::env::var_os("PARITY_DEBUG").is_some() {
                eprintln!("{name}: solver error: {error:?}");
            }
            Verdict::Unknown
        }
    }
}

/// Every input of `func` when the interpreter can run them all: scalar `u8`,
/// `bool` parameters, at most 2^17 inputs, and no `undef` (poison to the
/// interpreter, a free value to the encoding).
fn interpretable_inputs(module: &Module, func: FuncId) -> Option<Vec<Vec<InterpretValue>>> {
    let function = module.function_by_id(func)?;
    if function
        .blocks
        .iter()
        .any(|block| block.body.iter().any(|node| matches!(node.inst, Inst::Undef { .. })))
    {
        return None;
    }
    let entry = function.block(function.entry)?;
    let mut inputs: Vec<Vec<InterpretValue>> = vec![Vec::new()];
    for (_, ty) in &entry.params {
        let domain: Vec<InterpretValue> = match ty {
            Ty::U8 => (0..=255).map(|v| InterpretValue::int(Ty::U8, v).expect("u8")).collect(),
            Ty::Bool => vec![InterpretValue::bool(false), InterpretValue::bool(true)],
            _ => return None,
        };
        if inputs.len() * domain.len() > 1 << 17 {
            return None;
        }
        inputs = inputs
            .into_iter()
            .flat_map(|prefix| {
                domain.iter().map(move |value| {
                    let mut next = prefix.clone();
                    next.push(value.clone());
                    next
                })
            })
            .collect();
    }
    Some(inputs)
}

/// Hold a verdict only the large-block query decided to the interpreter: a
/// proof traps on no input, a refutation on some. `false` when the interpreter
/// cannot run every input (the verdict is then only counted).
fn holds_to_the_interpreter(module: &Module, func: FuncId, verdict: Verdict, what: &str) -> bool {
    let Some(inputs) = interpretable_inputs(module, func) else {
        return false;
    };
    let function = module.function_by_id(func).expect("function");
    let interpreter = Interpreter::with_module(module);
    let mut traps = 0usize;
    for input in inputs {
        match interpreter.execute_function(function, input.clone()) {
            Ok(_) => {}
            Err(error) if error.code == InterpretErrorCode::Panic => traps += 1,
            Err(error) if error.code == InterpretErrorCode::AssumeViolated => {}
            Err(error) => panic!("{what}: the interpreter cannot run {input:?}: {error:?}"),
        }
    }
    match verdict {
        Verdict::Proved => assert_eq!(traps, 0, "{what}: FALSE PROOF — the interpreter traps"),
        Verdict::Refuted => assert!(traps > 0, "{what}: refuted, but no input traps"),
        Verdict::Unknown => {}
    }
    true
}

/// Every body row of `module`: either matching canonical input refusals, or
/// solver verdicts that agree (or only the per-block one is undecided). Returns
/// the large-block outcomes and how many valid functions only it decided.
fn assert_parity(module: &Module, what: &str) -> (Vec<ParityOutcome>, usize) {
    let options = TranslateOptions::default();
    let errors = validate_module(module);
    let mut outcomes = Vec::new();
    let mut decided_only_as_one_query = 0;
    for func in &module.functions {
        if func.blocks.is_empty() {
            continue;
        }
        let large = trust_ir_function_to_chc_translation_output(module, func.id, &options)
            .expect("corpus function translates");
        let per_block =
            trust_ir_function_to_chc_translation_output_per_block(module, func.id, &options)
                .expect("corpus function translates");
        assert_eq!(
            large.module_input_refusal,
            per_block.module_input_refusal,
            "{what}::{}: encodings must agree on module input refusal",
            func.name
        );
        assert_eq!(
            large.module_input_refusal.is_some(),
            !errors.is_empty(),
            "{what}::{}: input refusal must match canonical module validity: {errors:?}",
            func.name
        );
        if let Some(reason) = large.module_input_refusal.as_deref() {
            eprintln!("{what}::{}: invalid-input refusal: {reason}", func.name);
            outcomes.push(ParityOutcome::InvalidInput);
            continue;
        }
        assert_eq!(large.work.large_block_fallbacks, 0, "{what}::{}", func.name);
        assert_eq!(large.diagnostics, per_block.diagnostics, "{what}::{}", func.name);
        let encoded_as_one_query = large.large_block.is_some();
        let id = func.id.index() as usize;
        let large_verdict = solve(large, &format!("{what}::{} large", func.name), id);
        let per_block_verdict = solve(per_block, &format!("{what}::{} per block", func.name), id);
        if large_verdict != per_block_verdict {
            assert!(
                per_block_verdict == Verdict::Unknown,
                "{what}::{}: the large-block query answers {large_verdict:?}, the per-block \
                 encoding {per_block_verdict:?} (large-block: {encoded_as_one_query})",
                func.name
            );
            holds_to_the_interpreter(
                module,
                func.id,
                large_verdict,
                &format!("{what}::{}", func.name),
            );
            decided_only_as_one_query += 1;
        }
        outcomes.push(ParityOutcome::Solver(large_verdict));
    }
    assert_eq!(
        outcomes.len(),
        module.functions.iter().filter(|func| !func.blocks.is_empty()).count(),
        "{what}: every corpus body must retain an outcome"
    );
    (outcomes, decided_only_as_one_query)
}

/// An unreachable block is rejected before either solver runs. Its body row
/// remains in the result and cannot supply a Refuted or Proved control.
#[test]
fn canonical_input_refusals_are_retained_without_solver_verdicts() {
    let mut mb = ModuleBuilder::new("parity_invalid_input");
    let ty = mb.add_func_type(vec![], vec![]);
    let mut fb = mb.function("subject", ty);
    let entry = fb.create_block();
    let orphan = fb.create_block();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    fb.ret(vec![]);
    fb.switch_to_block(orphan);
    fb.unreachable();
    fb.build();
    let module = mb.build().expect("the malformed control has a complete fixture shape");
    assert_eq!(
        validate_module(&module),
        [trust_ir_build::ValidationError::UnreachableBlock(orphan.index())]
    );
    let (outcomes, decided_only_as_one_query) = assert_parity(&module, "invalid input control");
    assert_eq!(outcomes, [ParityOutcome::InvalidInput]);
    assert_eq!(decided_only_as_one_query, 0);
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
        let (verdicts, decided_only_as_one_query) = assert_parity(module, name);
        if std::env::var_os("PARITY_DEBUG").is_some() {
            eprintln!("{name}: {verdicts:?}");
        }
        assert_eq!(decided_only_as_one_query, 0, "{name}: {verdicts:?}");
        functions += verdicts.len();
    }
    assert!(functions >= 8, "the fixture corpus shrank to {functions} functions");
}

/// `pub fn splat_index_param(i: usize) -> u32 { let a = [7u32; 8]; a[i] }`,
/// the compiler's `-Ztrust-dump` of it (the wave-7 SMT-array corpus): the index
/// check fails for `i >= 8`. The per-block encoding's witness names the entry and
/// the failing check only; the large-block query's model also binds the splat's
/// array (a block the failing path never reaches) and its solver left the entry
/// fact's index variable out, so the consumer refused that witness until the
/// composer completed it (`direct_smt_cex::replayable_model`). Both encodings
/// must refute, and the consumer must admit both witnesses.
#[test]
fn an_index_past_a_splat_is_refuted_as_one_query() {
    let module = bundle_module(include_str!(
        "../../trust-mc-trust-bmc/tests/fixtures/splat_index_param_native_bundle.json"
    ));
    let (verdicts, _) = assert_parity(&module, "splat_index_param");
    assert_eq!(verdicts, [ParityOutcome::Solver(Verdict::Refuted)]);
}

/// The ever-init cleanup chain (trust-mc-trust-bmc's liveness tests): a drop
/// flag per local, set, cleared and re-tested by a cleanup chain every unwind
/// choice can enter, and an overflow-checked running sum of `step` per local —
/// refuted when `step` can overflow within `n` locals.
fn ever_init(n: usize, step: i128) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("ever_init");
    let ft = mb.add_func_type(vec![], vec![Ty::U8]);
    let mut fb = mb.function("many_locals", ft);
    let entry = fb.create_block();
    let make: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let add: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let exit = fb.create_block();
    let cleanup: Vec<BlockId> = (0..=n).map(|_| fb.create_block()).collect();
    // cleanup[0] has no preceding local to drop. Omit its unused sentinel so
    // this semantic-parity fixture satisfies canonical module admission.
    let drop: Vec<BlockId> = (1..=n).map(|_| fb.create_block()).collect();
    fb.set_entry(entry);
    fb.switch_to_block(entry);
    let sum = fb.alloca(Ty::U8);
    let zero = fb.iconst(Ty::U8, 0);
    fb.store(Ty::U8, sum, zero);
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
        let before = fb.load(Ty::U8, sum);
        let step = fb.iconst(Ty::U8, step);
        let (total, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U8, before, step);
        let no = fb.bool_const(false);
        let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
        fb.assert(ok);
        fb.store(Ty::U8, sum, total);
        let no = fb.bool_const(false);
        fb.store(Ty::Bool, flags[i], no);
        let drop_unwinds = fb.undef(Ty::Bool);
        let next = if i + 1 < n { make[i + 1] } else { exit };
        fb.condbr(drop_unwinds, cleanup[i + 1], vec![], next, vec![]);
    }
    fb.switch_to_block(exit);
    let result = fb.load(Ty::U8, sum);
    fb.ret(vec![result]);
    fb.switch_to_block(cleanup[0]);
    let unwound = fb.undef(Ty::U8);
    fb.ret(vec![unwound]);
    for i in 1..=n {
        fb.switch_to_block(cleanup[i]);
        let live = fb.load(Ty::Bool, flags[i - 1]);
        let no = fb.bool_const(false);
        let dead = fb.icmp(ICmpOp::Eq, Ty::Bool, live, no);
        fb.condbr(dead, cleanup[i - 1], vec![], drop[i - 1], vec![]);
        fb.switch_to_block(drop[i - 1]);
        let dropped = fb.bool_const(true);
        fb.assert(dropped);
        fb.br(cleanup[i - 1], vec![]);
    }
    let function = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, function)
}

/// Drop flags that depend on the path: local `i` is moved only when input bit
/// `i` is set, so at the cleanup chain each flag is `true` or `false` by path,
/// and the chain asserts that a dropped local was never moved — refuted iff
/// `moved_twice_possible` lets a moved local's flag stay set.
fn path_dependent_flags(n: usize, moved_twice_possible: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("path_dependent_flags");
    let ft = mb.add_func_type(vec![Ty::U8], vec![]);
    let mut fb = mb.function("conditional_moves", ft);
    let entry = fb.create_block();
    let decide: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let moved: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let chain: Vec<BlockId> = (0..=n).map(|_| fb.create_block()).collect();
    let check: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    fb.set_entry(entry);
    let bits = fb.add_block_param(entry, Ty::U8);
    fb.switch_to_block(entry);
    let mut flags = Vec::with_capacity(n);
    let mut moves = Vec::with_capacity(n);
    for _ in 0..n {
        let flag = fb.alloca(Ty::Bool);
        let yes = fb.bool_const(true);
        fb.store(Ty::Bool, flag, yes);
        flags.push(flag);
        let was_moved = fb.alloca(Ty::Bool);
        let no = fb.bool_const(false);
        fb.store(Ty::Bool, was_moved, no);
        moves.push(was_moved);
    }
    fb.br(decide[0], vec![]);
    for i in 0..n {
        fb.switch_to_block(decide[i]);
        let mask = fb.iconst(Ty::U8, 1 << i);
        let zero = fb.iconst(Ty::U8, 0);
        let masked = fb.binop(BinOp::And, Ty::U8, bits, mask);
        let set = fb.icmp(ICmpOp::Ne, Ty::U8, masked, zero);
        let next = if i + 1 < n { decide[i + 1] } else { chain[n] };
        fb.condbr(set, moved[i], vec![], next, vec![]);
        fb.switch_to_block(moved[i]);
        // A move clears the flag — unless the variant forgets to.
        let cleared = fb.bool_const(moved_twice_possible && i == n - 1);
        fb.store(Ty::Bool, flags[i], cleared);
        let yes = fb.bool_const(true);
        fb.store(Ty::Bool, moves[i], yes);
        fb.br(next, vec![]);
    }
    fb.switch_to_block(chain[0]);
    fb.ret(vec![]);
    for i in (0..n).rev() {
        fb.switch_to_block(chain[i + 1]);
        let live = fb.load(Ty::Bool, flags[i]);
        fb.condbr(live, check[i], vec![], chain[i], vec![]);
        fb.switch_to_block(check[i]);
        let was_moved = fb.load(Ty::Bool, moves[i]);
        let no = fb.bool_const(false);
        let never = fb.icmp(ICmpOp::Eq, Ty::Bool, was_moved, no);
        fb.assert(never);
        fb.br(chain[i], vec![]);
    }
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

#[test]
fn generated_families_keep_their_verdicts() {
    let mut decided = Vec::new();
    let mut only_as_one_query = Vec::new();
    for (name, (module, _)) in [
        ("ever_init(1, 1)", ever_init(1, 1)),
        ("ever_init(3, 1)", ever_init(3, 1)),
        ("ever_init(3, 100)", ever_init(3, 100)),
        ("ever_init(6, 50)", ever_init(6, 50)),
        ("path_dependent_flags(3, ok)", path_dependent_flags(3, false)),
        ("path_dependent_flags(3, bug)", path_dependent_flags(3, true)),
        ("path_dependent_flags(6, ok)", path_dependent_flags(6, false)),
        ("path_dependent_flags(6, bug)", path_dependent_flags(6, true)),
    ] {
        let (verdicts, decided_only_as_one_query) = assert_parity(&module, name);
        if decided_only_as_one_query > 0 {
            only_as_one_query.push(name);
        }
        decided.push((name, verdicts));
    }
    if std::env::var_os("PARITY_DEBUG").is_some() {
        eprintln!("{decided:?}; decided only as one query: {only_as_one_query:?}");
    }
    let all: Vec<ParityOutcome> = decided.iter().flat_map(|(_, v)| v.iter().copied()).collect();
    assert_eq!(all.len(), 8, "every generated family row remains in the corpus");
    assert!(!all.contains(&ParityOutcome::InvalidInput), "{decided:?}");
    assert!(all.contains(&ParityOutcome::Solver(Verdict::Proved)), "{decided:?}");
    assert!(all.contains(&ParityOutcome::Solver(Verdict::Refuted)), "{decided:?}");
}

// ---------------------------------------------------------------------------
// Random acyclic SSA functions
// ---------------------------------------------------------------------------

struct Lcg(u64);

impl Lcg {
    fn below(&mut self, bound: usize) -> usize {
        self.0 =
            self.0.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        ((self.0 >> 33) as usize) % bound
    }
}

/// An acyclic function of `blocks` blocks in SSA form: block `i` branches only
/// to later blocks, and reads the entry's parameters, its own parameters, the
/// values it defines and two promoted cells. Blocks get zero or one `u8`
/// parameter, so joins merge differing arguments; havocs, assumptions, overflow
/// checks, assertions, switches (cases may share a target) and `unreachable`
/// are mixed in, and some blocks are reached by no path.
fn random_acyclic(seed: u64, blocks: usize) -> (Module, FuncId) {
    let mut rng = Lcg(seed);
    let mut mb = ModuleBuilder::new("large_block_random");
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
    fb.store(Ty::U8, cells[0], entry_values[0]);
    let seven = fb.iconst(Ty::U8, 7);
    fb.store(Ty::U8, cells[1], seven);
    for index in 0..blocks {
        if index > 0 {
            fb.switch_to_block(ids[index]);
        }
        let mut values = entry_values.clone();
        values.extend(params[index]);
        for _ in 0..=rng.below(4) {
            match rng.below(7) {
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
                    let bound = fb.iconst(Ty::U8, 16 + rng.below(100) as i128);
                    let small = fb.icmp(ICmpOp::Ult, Ty::U8, value, bound);
                    fb.assume(small);
                }
                4 => {
                    let value = values[rng.below(values.len())];
                    let forbidden = fb.iconst(Ty::U8, 200 + rng.below(50) as i128);
                    let ok = fb.icmp(ICmpOp::Ne, Ty::U8, value, forbidden);
                    fb.assert(ok);
                }
                5 => values.push(fb.undef(Ty::U8)),
                _ => {
                    let cell = cells[rng.below(2)];
                    let loaded = fb.load(Ty::U8, cell);
                    let one = fb.iconst(Ty::U8, 1);
                    values.push(fb.add(Ty::U8, loaded, one));
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
        match rng.below(6) {
            0 | 1 => {
                let target = later(&mut rng);
                let args = args_for(&mut rng, target, &values);
                fb.br(ids[target], args);
            }
            2 | 3 => {
                let cond = if rng.below(2) == 0 {
                    flag
                } else {
                    let (lhs, rhs) =
                        (values[rng.below(values.len())], values[rng.below(values.len())]);
                    fb.icmp(ICmpOp::Ult, Ty::U8, lhs, rhs)
                };
                let (then_target, else_target) = (later(&mut rng), later(&mut rng));
                let then_args = args_for(&mut rng, then_target, &values);
                let else_args = args_for(&mut rng, else_target, &values);
                fb.condbr(cond, ids[then_target], then_args, ids[else_target], else_args);
            }
            4 => {
                let selector = values[rng.below(values.len())];
                let cases = (0..=rng.below(3))
                    .map(|case| {
                        let target = later(&mut rng);
                        SwitchCase {
                            value: Constant::Int(case as i128),
                            target: ids[target],
                            args: args_for(&mut rng, target, &values),
                        }
                    })
                    .collect();
                let default = later(&mut rng);
                let default_args = args_for(&mut rng, default, &values);
                fb.switch(selector, cases, ids[default], default_args);
            }
            _ if rng.below(2) == 0 => fb.unreachable(),
            _ => fb.ret(vec![]),
        }
    }
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

#[test]
fn random_acyclic_functions_keep_their_verdicts() {
    let mut verdicts = Vec::new();
    let mut decided_only_as_one_query = 0;
    for seed in 0..48u64 {
        let blocks = 2 + (seed as usize % 7);
        let (module, _) = random_acyclic(seed, blocks);
        let (found, only) = assert_parity(&module, &format!("random_acyclic(seed {seed})"));
        verdicts.extend(found);
        decided_only_as_one_query += only;
    }
    assert_eq!(verdicts.len(), 48, "every original seed retains its body outcome");
    let count =
        |verdict| verdicts.iter().filter(|v| **v == ParityOutcome::Solver(verdict)).count();
    let refused = verdicts.iter().filter(|v| **v == ParityOutcome::InvalidInput).count();
    assert_eq!(
        count(Verdict::Proved) + count(Verdict::Refuted) + count(Verdict::Unknown) + refused,
        48
    );
    if std::env::var_os("PARITY_DEBUG").is_some() {
        eprintln!(
            "proved {}, refuted {}, unknown {}, invalid-input refusals {refused}, \
             total {}, decided only as one query {decided_only_as_one_query}",
            count(Verdict::Proved),
            count(Verdict::Refuted),
            count(Verdict::Unknown),
            verdicts.len()
        );
    }
    assert!(count(Verdict::Proved) > 0 && count(Verdict::Refuted) > 0, "{verdicts:?}");
}

/// A `k`-way switch on the entry's `sel`; arm `i` passes `(i % 200) + 1`
/// (computed in the arm) to `join(p)`, the default the entry's `x`; the join
/// asserts `p != 250` — refutable at `x = 250`, and true once `bounded` assumes
/// `x < 200`. A join of in-degree `k + 1`: its column is one selection chain of
/// depth-one definitions, so the query does not deepen as `k` grows (the 8e
/// review measured a stack overflow at k = 1 500 with the nested selection it
/// replaced; trust-mc-trust-bmc's `wide_joins_stay_linear_and_shallow` pins the
/// depth and size up to k = 4 096). The verdicts are compared at in-degrees the
/// whole-function query decides well inside the composer's per-query SMT budget
/// on any load. Wider joins are `measure_8e_wide_switch_in_degree`'s: at ay
/// 2fb40f95 the query decides at k = 1 024 in a fraction of that budget, and
/// from k = 2 048 ay-chc's fixed size ceilings refuse it whatever the budget
/// (docs/DECISION_QUEUE.md, 8e; docs/ay-asks/2026-10-01-large-query-size-ceilings-and-deterministic-effort).
fn wide_join(k: usize, bounded: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("wide_join");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U8], vec![]);
    let mut fb = mb.function("wide_join", ft);
    let entry = fb.create_block();
    let arms: Vec<BlockId> = (0..k).map(|_| fb.create_block()).collect();
    let join = fb.create_block();
    fb.set_entry(entry);
    let sel = fb.add_block_param(entry, Ty::U64);
    let input = fb.add_block_param(entry, Ty::U8);
    let joined = fb.add_block_param(join, Ty::U8);
    fb.switch_to_block(entry);
    if bounded {
        let limit = fb.iconst(Ty::U8, 200);
        let small = fb.icmp(ICmpOp::Ult, Ty::U8, input, limit);
        fb.assume(small);
    }
    let cases = (0..k)
        .map(|i| SwitchCase { value: Constant::Int(i as i128), target: arms[i], args: vec![] })
        .collect();
    fb.switch(sel, cases, join, vec![input]);
    for (i, arm) in arms.iter().enumerate() {
        fb.switch_to_block(*arm);
        let literal = fb.iconst(Ty::U8, (i % 200) as i128);
        let one = fb.iconst(Ty::U8, 1);
        let (passed, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U8, literal, one);
        let no = fb.bool_const(false);
        let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
        fb.assert(ok);
        fb.br(join, vec![passed]);
    }
    fb.switch_to_block(join);
    let forbidden = fb.iconst(Ty::U8, 250);
    let ok = fb.icmp(ICmpOp::Ne, Ty::U8, joined, forbidden);
    fb.assert(ok);
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

#[test]
fn wide_joins_keep_their_verdicts() {
    for k in [64, 256] {
        for bounded in [false, true] {
            let (module, _) = wide_join(k, bounded);
            let (verdicts, _) = assert_parity(&module, &format!("wide_join({k}, {bounded})"));
            let expected =
                ParityOutcome::Solver(if bounded { Verdict::Proved } else { Verdict::Refuted });
            assert_eq!(verdicts, [expected], "wide_join({k}, {bounded})");
        }
    }
}

/// Measurement of record for design step 8e: the verdict and wall time of the
/// wide-switch family under both encodings, per in-degree, through the public
/// pipeline (a refutation counts only when the consumer admits its witness).
/// Wall-clock numbers depend on the build and the host's load; record them with
/// both.
///
/// ```text
/// MEASURE_8E_K=256,1024,2048,4096 \
///   targo --unverified test -p trust-mc-driver --test chc_large_block_verdict_parity \
///   -- --ignored --nocapture measure_8e
/// ```
#[test]
#[ignore = "measurement of record: the wide-switch in-degree the one query decides"]
fn measure_8e_wide_switch_in_degree() {
    let in_degrees: Vec<usize> = std::env::var("MEASURE_8E_K")
        .unwrap_or_else(|_| "256,1024,2048".to_owned())
        .split(',')
        .filter_map(|k| k.trim().parse().ok())
        .collect();
    let options = TranslateOptions::default();
    for k in in_degrees {
        for bounded in [false, true] {
            let (module, func) = wide_join(k, bounded);
            for per_block in [false, true] {
                let output = if per_block {
                    trust_ir_function_to_chc_translation_output_per_block(&module, func, &options)
                } else {
                    trust_ir_function_to_chc_translation_output(&module, func, &options)
                }
                .expect("wide_join translates");
                let encoded_as_one_query = output.large_block.is_some();
                let started = std::time::Instant::now();
                let verdict = solve(output, "wide_join", k);
                eprintln!(
                    "[measure_8e] wide_join k={k} bounded={bounded} encoding={} one_query={encoded_as_one_query} verdict={verdict:?} seconds={:.3}",
                    if per_block { "per_block" } else { "large_block" },
                    started.elapsed().as_secs_f64()
                );
            }
        }
    }
}
