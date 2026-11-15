// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Relation liveness of the CHC translation: precise, query-complete, and
//! proportional to what is live.
//!
//! The pre-fix analysis asked every instruction for terminator successors, and
//! every ordinary instruction answered "conservative", so every block holding
//! one carried every threaded value and promoted cell (measured on the
//! ever-init family: all block relations carried the same 14-15 values at N=1,
//! 28 at N=2). These tests pin the replacement against an independent oracle,
//! against the translation's own reads (`carried_value_misses`), and against
//! the legacy analysis it replaces.
//!
//! Every assertion is on a deterministic counter or on the emitted relations;
//! none on time or memory.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::inst::{ICmpOp, Inst, OverflowOp, SwitchCase};
use trust_ir::ty::Ty;
use trust_ir::value::{BlockId, FuncId};
use trust_ir::{Constant, Function, Module};
use trust_ir_build::ModuleBuilder;

use super::{
    ChcTranslationOutput, ChcTranslationWork, carried_live_in, legacy_carried_live_in,
    trust_ir_function_to_chc_translation_output_per_block,
    trust_ir_function_to_chc_translation_output_with_legacy_liveness,
};
use crate::TranslateOptions;

// ---------------------------------------------------------------------------
// An independent liveness oracle
// ---------------------------------------------------------------------------

/// The blocks a terminator transfers to, restated here (not shared with the
/// production code) so the oracle cannot inherit a bug from it.
fn oracle_successors(inst: &Inst) -> Vec<BlockId> {
    match inst {
        Inst::Br { target, .. } => vec![*target],
        Inst::CondBr { then_target, else_target, .. } => vec![*then_target, *else_target],
        Inst::Switch { default, cases, .. } => {
            let mut targets = vec![*default];
            targets.extend(cases.iter().map(|case| case.target));
            targets
        }
        Inst::Invoke { normal_dest, unwind_dest, .. } => vec![*normal_dest, *unwind_dest],
        _ => Vec::new(),
    }
}

/// Textbook liveness, one value at a time: `v` is live-in at `b` iff `b` does not
/// own `v` (define it or take it as a block param) and some path from `b`'s entry
/// reaches a use of `v` without passing a block that owns it. Computed by a
/// backward search from the using blocks — a different algorithm from the
/// production delta propagation.
fn oracle_live_in(
    func: &Function,
    carried: &BTreeSet<u32>,
    def_block: &BTreeMap<u32, BlockId>,
) -> BTreeMap<BlockId, BTreeSet<u32>> {
    let mut preds: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    let mut uses: BTreeMap<BlockId, BTreeSet<u32>> = BTreeMap::new();
    for block in &func.blocks {
        for node in &block.body {
            node.inst.visit_value_operands(|value| {
                uses.entry(block.id).or_default().insert(value.index());
            });
            if node.inst.is_terminator() {
                for target in oracle_successors(&node.inst) {
                    preds.entry(target).or_default().insert(block.id);
                }
            }
        }
    }
    let owns = |block: BlockId, id: u32| {
        def_block.get(&id) == Some(&block)
            || func
                .block(block)
                .is_some_and(|b| b.params.iter().any(|(param, _)| param.index() == id))
    };
    let mut live: BTreeMap<BlockId, BTreeSet<u32>> =
        func.blocks.iter().map(|b| (b.id, BTreeSet::new())).collect();
    for &id in carried {
        let mut stack: Vec<BlockId> = func
            .blocks
            .iter()
            .filter(|b| uses.get(&b.id).is_some_and(|u| u.contains(&id)) && !owns(b.id, id))
            .map(|b| b.id)
            .collect();
        let mut seen = BTreeSet::new();
        while let Some(block) = stack.pop() {
            if !seen.insert(block) {
                continue;
            }
            live.get_mut(&block).expect("block exists").insert(id);
            for pred in preds.get(&block).into_iter().flatten() {
                if !owns(*pred, id) {
                    stack.push(*pred);
                }
            }
        }
    }
    live
}

/// Every instruction result and entry param of `func`, with its defining block.
fn all_values(func: &Function) -> (BTreeSet<u32>, BTreeMap<u32, BlockId>) {
    let mut def_block = BTreeMap::new();
    if let Some(entry) = func.block(func.entry) {
        for (param, _) in &entry.params {
            def_block.insert(param.index(), entry.id);
        }
    }
    for block in &func.blocks {
        for node in &block.body {
            for result in &node.results {
                def_block.insert(result.index(), block.id);
            }
        }
    }
    (def_block.keys().copied().collect(), def_block)
}

// ---------------------------------------------------------------------------
// Deterministic pseudo-random CFGs
// ---------------------------------------------------------------------------

struct Lcg(u64);

impl Lcg {
    fn below(&mut self, bound: usize) -> usize {
        self.0 =
            self.0.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        ((self.0 >> 33) as usize) % bound
    }
}

/// A function over `blocks` blocks whose instructions read arbitrary earlier
/// values (SSA dominance is deliberately NOT respected: liveness must be right
/// on any operand graph) and whose terminators cover every successor shape the
/// analysis distinguishes, `Invoke` and `Resume` included.
fn random_function(seed: u64, blocks: usize) -> (Module, FuncId) {
    let mut rng = Lcg(seed);
    let mut mb = ModuleBuilder::new("liveness_random");
    let callee_ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let callee = {
        let mut fb = mb.function("callee", callee_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U64);
        fb.ret(vec![x]);
        fb.build()
    };
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("random", ft);
    let ids: Vec<BlockId> = (0..blocks).map(|_| fb.create_block()).collect();
    fb.set_entry(ids[0]);
    let mut values = vec![fb.add_block_param(ids[0], Ty::U64), fb.add_block_param(ids[0], Ty::U64)];
    for (index, &block) in ids.iter().enumerate() {
        fb.switch_to_block(block);
        for _ in 0..rng.below(4) {
            let lhs = values[rng.below(values.len())];
            let rhs = values[rng.below(values.len())];
            values.push(fb.add(Ty::U64, lhs, rhs));
        }
        if rng.below(3) == 0 {
            values.push(fb.undef(Ty::U64));
        }
        let pick = |rng: &mut Lcg| ids[rng.below(ids.len())];
        let operand = values[rng.below(values.len())];
        match rng.below(8) {
            0 | 1 => {
                let target = pick(&mut rng);
                fb.br(target, vec![]);
            }
            2 | 3 => {
                let zero = fb.iconst(Ty::U64, 0);
                let cond = fb.icmp(ICmpOp::Eq, Ty::U64, operand, zero);
                let (then_target, else_target) = (pick(&mut rng), pick(&mut rng));
                fb.condbr(cond, then_target, vec![], else_target, vec![]);
            }
            4 => {
                let cases = (0..=rng.below(3))
                    .map(|case| SwitchCase {
                        value: Constant::Int(case as i128),
                        target: pick(&mut rng),
                        args: vec![],
                    })
                    .collect();
                let default = pick(&mut rng);
                fb.switch(operand, cases, default, vec![]);
            }
            5 => {
                let (normal, unwind) = (pick(&mut rng), pick(&mut rng));
                values.push(fb.invoke(callee, vec![operand], normal, vec![], unwind));
            }
            6 if index % 2 == 0 => fb.resume(operand),
            6 => fb.unreachable(),
            _ => fb.ret(vec![operand]),
        }
    }
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

#[test]
fn precise_liveness_is_the_textbook_least_solution_on_random_cfgs() {
    for seed in 0..200u64 {
        let blocks = 2 + (seed as usize % 23);
        let (module, function) = random_function(seed, blocks);
        let func = module.function_by_id(function).expect("generated function");
        let (carried, def_block) = all_values(func);
        let mut work = ChcTranslationWork::default();
        let precise = carried_live_in(func, &carried, &def_block, &mut work);
        let oracle = oracle_live_in(func, &carried, &def_block);
        assert_eq!(precise, oracle, "seed {seed}: precise liveness differs from the oracle");
        let summed: u64 = precise.values().map(|live| live.len() as u64).sum();
        assert_eq!(work.live_in_insertions, summed, "seed {seed}: one insertion per live pair");

        // The legacy analysis over-approximates it everywhere: dropping a column it
        // carried is only ever dropping a column no read needs.
        let legacy = legacy_carried_live_in(func, &carried, &def_block);
        for (block, live) in &precise {
            assert!(
                live.is_subset(&legacy[block]),
                "seed {seed}: bb{} precise {live:?} is not within legacy {:?}",
                block.index(),
                legacy[block]
            );
        }
    }
}

/// `Invoke` is a terminator with two edges and exactly its listed operands.
/// The legacy analysis read it (like every non-terminator it was asked about)
/// as "reads every carried value".
#[test]
fn an_invoke_terminated_block_carries_exactly_its_operands_and_successors_needs() {
    let mut mb = ModuleBuilder::new("liveness_invoke");
    let callee_ft = mb.add_func_type(vec![Ty::U64], vec![Ty::U64]);
    let callee = {
        let mut fb = mb.function("callee", callee_ft);
        let entry = fb.create_block();
        fb.switch_to_block(entry);
        fb.set_entry(entry);
        let x = fb.add_block_param(entry, Ty::U64);
        fb.ret(vec![x]);
        fb.build()
    };
    let ft = mb.add_func_type(vec![Ty::U64, Ty::U64, Ty::U64, Ty::U64], vec![Ty::U64]);
    let mut fb = mb.function("invoker", ft);
    let (entry, call, normal, unwind, elsewhere) = (
        fb.create_block(),
        fb.create_block(),
        fb.create_block(),
        fb.create_block(),
        fb.create_block(),
    );
    fb.set_entry(entry);
    let arg = fb.add_block_param(entry, Ty::U64);
    let on_normal = fb.add_block_param(entry, Ty::U64);
    let on_unwind = fb.add_block_param(entry, Ty::U64);
    let unrelated = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let zero = fb.iconst(Ty::U64, 0);
    let cond = fb.icmp(ICmpOp::Eq, Ty::U64, arg, zero);
    fb.condbr(cond, call, vec![], elsewhere, vec![]);
    fb.switch_to_block(call);
    let _ = fb.invoke(callee, vec![arg], normal, vec![], unwind);
    fb.switch_to_block(normal);
    fb.ret(vec![on_normal]);
    fb.switch_to_block(unwind);
    fb.resume(on_unwind);
    fb.switch_to_block(elsewhere);
    fb.ret(vec![unrelated]);
    let function = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let func = module.function_by_id(function).expect("generated function");
    let (carried, def_block) = all_values(func);

    let mut work = ChcTranslationWork::default();
    let precise = carried_live_in(func, &carried, &def_block, &mut work);
    let expected: BTreeSet<u32> =
        [arg, on_normal, on_unwind].iter().map(|value| value.index()).collect();
    assert_eq!(precise[&call], expected);
    assert_eq!(precise[&elsewhere], BTreeSet::from([unrelated.index()]));

    let legacy = legacy_carried_live_in(func, &carried, &def_block);
    assert!(
        legacy[&call].contains(&unrelated.index()),
        "the legacy analysis was conservative here"
    );
}

// ---------------------------------------------------------------------------
// Generated families, translated end to end
// ---------------------------------------------------------------------------

/// Straight-line chain: block `i` makes `x_i` (an `Undef`, which the translator
/// always threads) and reads `x_{i-1}` in an overflow-checked add. Each value is
/// live in exactly one block, so Σ arity is linear in `n`; the legacy analysis
/// carried every value into every block (quadratic).
fn straight_line_family(n: usize) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("straight_line_family");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let mut fb = mb.function("chain", ft);
    let blocks: Vec<BlockId> = (0..=n).map(|_| fb.create_block()).collect();
    fb.set_entry(blocks[0]);
    fb.switch_to_block(blocks[0]);
    let mut previous = fb.undef(Ty::U64);
    fb.br(blocks[1], vec![]);
    for &block in &blocks[1..] {
        fb.switch_to_block(block);
        let fresh = fb.undef(Ty::U64);
        let (sum, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, previous, fresh);
        let no = fb.bool_const(false);
        let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
        fb.assert(ok);
        let _ = sum;
        previous = fresh;
        if let Some(next) = blocks.iter().skip_while(|b| **b != block).nth(1) {
            fb.br(*next, vec![]);
        } else {
            fb.ret(vec![previous]);
        }
    }
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// The shape `tests/ui/borrowck/ever-init-many-locals.rs` lowers to, as the
/// seal's native-bundle dump shows it: per local a drop flag and a checked-add
/// tuple cell allocated in the entry; a block making the boxed value (an
/// `Undef`) and choosing whether its construction unwinds into the cleanup
/// chain; the overflow-checked `sum += *a_i` through the tuple cell; a second
/// unwind choice (the `drop` call); and a cleanup chain that tests every earlier
/// drop flag. The flags are genuinely live along the whole chain, so this family
/// pins arity against what is live, not against a linear bound.
pub(crate) fn ever_init_family(n: usize) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("ever_init_family");
    let ft = mb.add_func_type(vec![], vec![Ty::U64]);
    let tuple = Ty::Tuple(vec![Ty::U64, Ty::Bool]);
    let mut fb = mb.function("many_locals", ft);
    let entry = fb.create_block();
    let make: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let add: Vec<BlockId> = (0..n).map(|_| fb.create_block()).collect();
    let exit = fb.create_block();
    // cleanup[i] tests the flag of local i-1 (cleanup[0] is the unwind exit);
    // drop[i-1] drops local i-1.
    let cleanup: Vec<BlockId> = (0..=n).map(|_| fb.create_block()).collect();
    // There is no local before cleanup[0], so no drop[0] block exists. Every
    // stored block must be reachable for canonical module admission.
    let drop: Vec<BlockId> = (1..=n).map(|_| fb.create_block()).collect();
    fb.set_entry(entry);

    fb.switch_to_block(entry);
    let sum = fb.alloca(Ty::U64);
    let zero = fb.iconst(Ty::U64, 0);
    fb.store(Ty::U64, sum, zero);
    let mut flags = Vec::with_capacity(n);
    let mut tuples = Vec::with_capacity(n);
    for _ in 0..n {
        let flag = fb.alloca(Ty::Bool);
        let no = fb.bool_const(false);
        fb.store(Ty::Bool, flag, no);
        flags.push(flag);
        tuples.push(fb.alloca(tuple.clone()));
    }
    fb.br(make[0], vec![]);

    for i in 0..n {
        fb.switch_to_block(make[i]);
        let boxed = fb.undef(Ty::U64);
        let yes = fb.bool_const(true);
        fb.store(Ty::Bool, flags[i], yes);
        let unwinds = fb.undef(Ty::Bool);
        fb.condbr(unwinds, cleanup[i], vec![], add[i], vec![]);

        fb.switch_to_block(add[i]);
        let before = fb.load(Ty::U64, sum);
        let (total, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, before, boxed);
        let empty = fb.undef(tuple.clone());
        let with_total = fb.insert_field(tuple.clone(), empty, 0, total);
        let checked = fb.insert_field(tuple.clone(), with_total, 1, overflowed);
        fb.store(tuple.clone(), tuples[i], checked);
        let reread = fb.load(tuple.clone(), tuples[i]);
        let flag_bit = fb.extract_field(Ty::Bool, reread, 1);
        let no = fb.bool_const(false);
        let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, flag_bit, no);
        fb.assert(ok);
        let value = fb.extract_field(Ty::U64, reread, 0);
        fb.store(Ty::U64, sum, value);
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

/// The per-block encoding: these tests pin its relation layout, which the
/// large-block encoding of an acyclic function keeps as the column layout of
/// its merged blocks (`translate_chc_large_block.rs`).
fn translate(module: &Module, function: FuncId) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output_per_block(
        module,
        function,
        &TranslateOptions::default(),
    )
    .expect("fixture function translates")
}

fn translate_legacy(module: &Module, function: FuncId) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output_with_legacy_liveness(
        module,
        function,
        &TranslateOptions::default(),
    )
    .expect("fixture function translates")
}

/// The carried value ids of every block relation, read back from the relation
/// formals the translation declared (`bb{b}_thr_v{v}` / `bb{b}_cell_v{v}`, plus
/// `_field{i}` leaves for an aggregate).
fn carried_by_block(output: &ChcTranslationOutput) -> BTreeMap<u32, BTreeSet<u32>> {
    let mut carried: BTreeMap<u32, BTreeSet<u32>> = BTreeMap::new();
    for var in output.vc.vars() {
        let name = var.name.to_string();
        let Some(rest) = name.strip_prefix("bb") else { continue };
        let Some((block, rest)) = rest.split_once('_') else { continue };
        let Some(rest) = rest.strip_prefix("thr_v").or_else(|| rest.strip_prefix("cell_v")) else {
            continue;
        };
        let value = rest.split('_').next().unwrap_or(rest);
        if let (Ok(block), Ok(value)) = (block.parse::<u32>(), value.parse::<u32>()) {
            carried.entry(block).or_default().insert(value);
        }
    }
    carried
}

fn relation_arguments(output: &ChcTranslationOutput) -> usize {
    output.vc.relations.iter().map(|relation| relation.arity()).sum()
}

fn max_predecessors(module: &Module, function: FuncId) -> u64 {
    let func = module.function_by_id(function).expect("function");
    let mut preds: BTreeMap<BlockId, BTreeSet<BlockId>> = BTreeMap::new();
    for block in &func.blocks {
        for node in block.body.iter().filter(|node| node.inst.is_terminator()) {
            for target in oracle_successors(&node.inst) {
                preds.entry(target).or_default().insert(block.id);
            }
        }
    }
    preds.values().map(|p| p.len() as u64).max().unwrap_or(0)
}

fn instruction_count(module: &Module, function: FuncId) -> u64 {
    let func = module.function_by_id(function).expect("function");
    func.blocks.iter().map(|block| block.body.len() as u64).sum()
}

/// What the translation carries equals what the oracle says is live, block by
/// block, for the values the translation chose to carry at all.
fn assert_relations_carry_exactly_what_is_live(module: &Module, function: FuncId, what: &str) {
    let output = translate(module, function);
    let func = module.function_by_id(function).expect("function");
    let carried = carried_by_block(&output);
    let candidates: BTreeSet<u32> = carried.values().flatten().copied().collect();
    let (_, def_block) = all_values(func);
    let oracle = oracle_live_in(func, &candidates, &def_block);
    for block in &func.blocks {
        if block.id == func.entry {
            continue;
        }
        let got = carried.get(&block.id.index()).cloned().unwrap_or_default();
        assert_eq!(
            got,
            oracle[&block.id],
            "{what}: bb{} carries {got:?}, live is {:?}",
            block.id.index(),
            oracle[&block.id]
        );
    }
    assert_eq!(output.work.carried_value_misses, 0, "{what}: a read the relations do not carry");
}

/// A valid runtime closure with repeated, ordered captures from an earlier
/// block. Its unused result must not erase either capture reads or refusal.
pub(crate) fn runtime_closure_fixture()
-> (Module, FuncId, BlockId, Vec<trust_ir::ValueId>, trust_ir::ValueId) {
    let mut mb = ModuleBuilder::new("runtime_closure_capture_liveness");
    let apparent = mb.add_func_type(vec![], vec![]);
    let physical = mb.add_func_type(vec![Ty::I64, Ty::I64, Ty::I64], vec![]);
    let closure = mb.add_closure_type(trust_ir::ClosureTy {
        func: apparent,
        captures: vec![Ty::I64, Ty::I64, Ty::I64],
    });
    let mut target = mb.function("target", physical);
    let entry = target.create_block();
    target.set_entry(entry);
    target.switch_to_block(entry);
    for _ in 0..3 {
        target.add_block_param(entry, Ty::I64);
    }
    target.ret(vec![]);
    let target = target.build();

    let host_ty = mb.add_func_type(vec![Ty::I64, Ty::I64], vec![]);
    let mut host = mb.function("construct", host_ty);
    let entry = host.create_block();
    let construct = host.create_block();
    host.set_entry(entry);
    host.switch_to_block(entry);
    let x = host.add_block_param(entry, Ty::I64);
    let y = host.add_block_param(entry, Ty::I64);
    host.br(construct, vec![]);
    host.switch_to_block(construct);
    host.ret(vec![]);
    let host = host.build();
    let mut module = mb.build().expect("valid closure signatures and host");
    let result = trust_ir::ValueId::new(x.index().max(y.index()) + 1);
    let captures = vec![y, x, y];
    let block = module
        .functions
        .iter_mut()
        .find(|f| f.id == host)
        .unwrap()
        .blocks
        .iter_mut()
        .find(|b| b.id == construct)
        .unwrap();
    block.body.insert(
        0,
        trust_ir::InstrNode::new(Inst::MakeClosure {
            ty: closure,
            func: target,
            captures: captures.clone(),
        })
        .with_result(result),
    );
    assert!(trust_ir_build::validate_module(&module).is_empty());
    (module, host, construct, captures, result)
}

#[test]
fn runtime_closure_captures_are_live_across_blocks() {
    let (module, host, construct, captures, _) = runtime_closure_fixture();
    assert_relations_carry_exactly_what_is_live(&module, host, "runtime closure captures");
    let output = translate(&module, host);
    let expected: BTreeSet<u32> = captures.iter().map(|value| value.index()).collect();
    assert_eq!(expected.len(), 2, "the repeated capture is distinct from a new value");
    assert_eq!(carried_by_block(&output).get(&construct.index()), Some(&expected));
}

#[test]
fn relations_carry_exactly_the_live_values_on_both_families() {
    for n in [1, 2, 3, 5, 8] {
        let (module, function) = straight_line_family(n);
        assert_relations_carry_exactly_what_is_live(
            &module,
            function,
            &format!("straight_line({n})"),
        );
        let (module, function) = ever_init_family(n);
        assert_relations_carry_exactly_what_is_live(&module, function, &format!("ever_init({n})"));
    }
}

#[test]
fn straight_line_arity_is_linear_where_the_legacy_analysis_was_quadratic() {
    let mut previous: Option<(usize, usize)> = None;
    for n in [16, 32, 64, 128] {
        let (module, function) = straight_line_family(n);
        let precise = translate(&module, function);
        let legacy = translate_legacy(&module, function);
        let (arity, legacy_arity) = (relation_arguments(&precise), relation_arguments(&legacy));
        // One threaded value per non-entry block, and nothing else.
        assert_eq!(arity, n, "straight_line({n}): Σ arity");
        assert!(
            legacy_arity >= n * (n - 1) / 2,
            "straight_line({n}): legacy Σ arity {legacy_arity}"
        );
        assert_eq!(precise.work.instructions_translated, instruction_count(&module, function));
        assert!(precise.work.live_in_edge_visits <= 2 * precise.work.live_in_insertions);
        if let Some((prev_arity, prev_visits)) = previous {
            assert!(arity * 2 <= prev_arity * 5, "Σ arity {prev_arity} -> {arity} per doubling");
            let visits = precise.work.live_in_edge_visits as usize;
            assert!(
                visits * 2 <= prev_visits * 5,
                "edge visits {prev_visits} -> {visits} per doubling"
            );
        }
        previous = Some((arity, precise.work.live_in_edge_visits as usize));
    }
}

#[test]
fn ever_init_arity_follows_the_live_drop_flags_and_stays_below_legacy() {
    for n in [4, 8, 16, 32] {
        let (module, function) = ever_init_family(n);
        let precise = translate(&module, function);
        let legacy = translate_legacy(&module, function);
        let (arity, legacy_arity) = (relation_arguments(&precise), relation_arguments(&legacy));
        assert!(arity < legacy_arity, "ever_init({n}): {arity} !< legacy {legacy_arity}");
        assert_eq!(precise.work.instructions_translated, instruction_count(&module, function));
        // Work is bounded by what it produces: each live pair is offered to each
        // of its block's predecessors once (a cleanup block has four).
        assert!(
            precise.work.live_in_edge_visits
                <= max_predecessors(&module, function) * precise.work.live_in_insertions,
            "ever_init({n}): {:?}",
            precise.work
        );
        assert_eq!(precise.work.carried_value_misses, 0);
    }
}
