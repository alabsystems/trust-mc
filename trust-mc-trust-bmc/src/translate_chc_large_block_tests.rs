// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! The large-block encoding of an acyclic function (`translate_chc_large_block.rs`):
//! its plan, its shape, its size on the ever-init family, and the block path a
//! model maps back to. Equisatisfiability with the per-block encoding is pinned
//! by the driver's solver-backed tests (`trust-mc-driver`, `large_block_*`).

use std::collections::{BTreeMap, BTreeSet, HashMap};

use trust_ir::inst::{ICmpOp, OverflowOp, SwitchCase};
use trust_ir::ty::{FatPtrKind, Ty};
use trust_ir::value::{BlockId, FuncId, ValueId};
use trust_ir::{Constant, Module};
use trust_ir_build::{FunctionBuilder, ModuleBuilder, ValidationError};

use super::liveness_tests::ever_init_family;
use super::{
    ChcTranslationOutput, ERROR_REL, output_equates_array_terms,
    trust_ir_function_to_chc_translation_output,
    trust_ir_function_to_chc_translation_output_per_block,
};
use crate::TranslateOptions;

fn translate(module: &Module, function: FuncId) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output(module, function, &TranslateOptions::default())
        .expect("fixture function translates")
}

fn translate_per_block(module: &Module, function: FuncId) -> ChcTranslationOutput {
    trust_ir_function_to_chc_translation_output_per_block(
        module,
        function,
        &TranslateOptions::default(),
    )
    .expect("fixture function translates")
}

/// Keep hostile internal algorithm coverage while checking that no public
/// translation entry admits this malformed source. The raw translator below
/// exists only under cfg(test); it grants no module validity or proof authority.
fn translate_hostile_algorithm_fixture(
    module: &Module,
    function: FuncId,
    expected: impl Fn(&ValidationError) -> bool,
) -> ChcTranslationOutput {
    let errors = trust_ir_build::validate_module(module);
    assert!(!errors.is_empty(), "hostile fixture must remain invalid");
    assert!(errors.iter().all(expected), "unexpected invalidity: {errors:?}");
    for refused in [translate(module, function), translate_per_block(module, function)] {
        assert!(refused.module_input_refusal.is_some());
        assert!(refused.large_block.is_none());
        assert_eq!(refused.work.instructions_translated, 0);
        assert_eq!(refused.vc.rules.len(), 1);
        let fact = &refused.vc.rules[0];
        assert_eq!(fact.head.name.as_str(), ERROR_REL);
        assert!(fact.body.relation.is_none());
        assert!(fact.body.constraints.is_empty());
    }
    super::translate_function(
        module.function_by_id(function).expect("hostile fixture function"),
        module,
        &TranslateOptions::default(),
    )
}

fn relation_arguments(output: &ChcTranslationOutput) -> usize {
    output.vc.relations.iter().map(|relation| relation.arity()).sum()
}

/// Every node of every rule, shared subterms once: the size of the CHC a
/// consumer lowers.
fn rule_nodes(output: &ChcTranslationOutput) -> usize {
    let mut seen = std::collections::BTreeSet::new();
    let mut stack: Vec<&ay_bindings::Expr> = Vec::new();
    for rule in &output.vc.rules {
        stack.extend(rule.body.constraints.iter());
        if let Some(app) = &rule.body.relation {
            stack.extend(app.args.iter());
        }
        stack.extend(rule.head.args.iter());
    }
    while let Some(expr) = stack.pop() {
        if seen.insert(std::ptr::from_ref(expr.value())) {
            stack.extend(expr.children());
        }
    }
    seen.len()
}

#[test]
fn ever_init_is_one_query_over_the_entry_relation() {
    for n in [1, 2, 4, 8] {
        let (module, function) = ever_init_family(n);
        let output = translate(&module, function);
        let names: Vec<String> =
            output.vc.relations.iter().map(|relation| relation.name.clone()).collect();
        assert_eq!(names, ["bb0".to_string(), ERROR_REL.to_string()]);
        // The entry fact and the one query rule. The fixture has no unused
        // drop[0] sentinel: canonical admission requires every stored block
        // to be reachable.
        assert_eq!(output.vc.rules.len(), 2, "ever_init({n}): rules");
        assert_eq!(output.work.large_block_fallbacks, 0);
        assert_eq!(output.work.carried_value_misses, 0);
        let blocks = module.function_by_id(function).expect("function").blocks.len() as u64;
        assert_eq!(output.work.large_block_merged_blocks, blocks - 1);
        assert!(output.large_block.is_some());
        assert!(!output_equates_array_terms(&output));
    }
}

#[test]
fn ever_init_size_is_linear_where_the_per_block_relations_were_quadratic() {
    let mut previous: Option<(u64, usize)> = None;
    for n in [8, 16, 32, 64, 128] {
        let (module, function) = ever_init_family(n);
        let large = translate(&module, function);
        let per_block = translate_per_block(&module, function);
        assert_eq!(relation_arguments(&large), 0, "ever_init({n}): the entry takes no argument");
        assert!(
            relation_arguments(&per_block) >= n * n,
            "ever_init({n}): per-block Σ arity {}",
            relation_arguments(&per_block)
        );
        let variables = large.work.large_block_variables;
        let nodes = rule_nodes(&large);
        // The drop flags reach every cleanup block as the same literal, so no
        // column of them needs a variable: one `sum` column per merge point.
        assert!(
            large.work.large_block_column_variables <= 4 * n as u64,
            "ever_init({n}): {:?}",
            large.work
        );
        if let Some((prev_variables, prev_nodes)) = previous {
            assert!(
                variables * 2 <= prev_variables * 5,
                "ever_init({n}): variables {prev_variables} -> {variables} per doubling"
            );
            assert!(
                nodes * 2 <= prev_nodes * 5,
                "ever_init({n}): rule nodes {prev_nodes} -> {nodes} per doubling"
            );
        }
        previous = Some((variables, nodes));
        eprintln!(
            "ever_init({n}): large: relation args {}, vars {}, nodes {}, work {:?}; per-block: relation args {}, nodes {}",
            relation_arguments(&large),
            large.vc.vars().len(),
            nodes,
            large.work,
            relation_arguments(&per_block),
            rule_nodes(&per_block),
        );
    }
}

/// `entry: c ? a : b; a: x = 1; b: x = 2 (block param); join: assert(x != 3)`.
fn diamond() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("diamond");
    let ft = mb.add_func_type(vec![Ty::Bool, Ty::U8], vec![]);
    let mut fb = mb.function("diamond", ft);
    let (entry, left, right, join) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    let c = fb.add_block_param(entry, Ty::Bool);
    let y = fb.add_block_param(entry, Ty::U8);
    let x = fb.add_block_param(join, Ty::U8);
    fb.switch_to_block(entry);
    fb.condbr(c, left, vec![], right, vec![]);
    fb.switch_to_block(left);
    let one = fb.iconst(Ty::U8, 1);
    fb.br(join, vec![one]);
    fb.switch_to_block(right);
    fb.br(join, vec![y]);
    fb.switch_to_block(join);
    let three = fb.iconst(Ty::U8, 3);
    let bad = fb.icmp(ICmpOp::Ne, Ty::U8, x, three);
    fb.assert(bad);
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// `switch sel { 1 => a, 1 => b, _ => c }`, the arms passing 10, 20 and 30 to
/// `join(p)`, which asserts `p != 20`. The two cases' guards are both
/// `sel == 1`, so two transitions into the join can be taken together; the
/// at-most-one ladder is what keeps the join's selection one in-edge's terms
/// (without it, `a` and `b` taken together reach the site with `b`'s 20 while
/// the block path walks back through `a`).
fn duplicate_cases() -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("duplicate_cases");
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let mut fb = mb.function("duplicate_cases", ft);
    let entry = fb.create_block();
    let arms: Vec<BlockId> = (0..3).map(|_| fb.create_block()).collect();
    let join = fb.create_block();
    fb.set_entry(entry);
    let sel = fb.add_block_param(entry, Ty::U64);
    let joined = fb.add_block_param(join, Ty::U8);
    fb.switch_to_block(entry);
    let cases = (0..2)
        .map(|arm| SwitchCase { value: Constant::Int(1), target: arms[arm], args: vec![] })
        .collect();
    fb.switch(sel, cases, arms[2], vec![]);
    for (index, arm) in arms.iter().enumerate() {
        fb.switch_to_block(*arm);
        let literal = fb.iconst(Ty::U8, 10 * (index as i128 + 1));
        fb.br(join, vec![literal]);
    }
    fb.switch_to_block(join);
    let twenty = fb.iconst(Ty::U8, 20);
    let ok = fb.icmp(ICmpOp::Ne, Ty::U8, joined, twenty);
    fb.assert(ok);
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

#[test]
fn a_model_maps_back_to_its_block_path() {
    let (module, function) = diamond();
    let output = translate(&module, function);
    let map = output.large_block.as_ref().expect("an acyclic function is one query");
    // The join's parameter differs per in-edge (the literal 1, the entry's
    // `y`): ONE column variable, `c = ite(s, 1, y)` over the in-edge that does
    // not pass the first most frequent term, and the join reads `c` — never the
    // selection itself.
    assert_eq!(output.work.large_block_column_variables, 1);
    assert_eq!(map.columns.len(), 1);
    let site = map.sites.first().expect("the assertion is an error site").clone();
    assert_eq!(site.block, BlockId::new(3));
    let edges = &map.in_edges[&BlockId::new(3)];
    assert_eq!(edges.len(), 2);
    // A model through the right arm: the second in-edge of the join is the
    // selected one, the first is false.
    let mut values: BTreeMap<String, bool> = BTreeMap::new();
    values.insert(site.var.clone(), true);
    values.insert(edges[0].selector.clone(), false);
    values.insert(edges[1].selector.clone(), true);
    for edge in &map.in_edges[&edges[1].source] {
        values.insert(edge.selector.clone(), true);
    }
    let path =
        map.counterexample_path(|var| values.get(var).copied()).expect("a path to the error site");
    assert_eq!(path.blocks, [BlockId::new(0), BlockId::new(2), BlockId::new(3)]);
    assert_eq!(path.site, site);
    // An assignment that selects no in-edge into the join is not a model.
    values.insert(edges[1].selector.clone(), false);
    assert_eq!(map.counterexample_path(|var| values.get(var).copied()), None);
}

#[test]
fn diagnostics_keep_the_per_block_order() {
    for n in [1, 3, 6] {
        let (module, function) = ever_init_family(n);
        let large = translate(&module, function);
        let per_block = translate_per_block(&module, function);
        let key = |output: &ChcTranslationOutput| {
            output
                .diagnostics
                .iter()
                .map(|row| (row.block, row.instruction_index, row.reason))
                .collect::<Vec<_>>()
        };
        assert_eq!(key(&large), key(&per_block), "ever_init({n})");
    }
}

/// A translation that abandons the large-block encoding returns exactly the
/// per-block translation, and says so in its work counters.
#[test]
fn an_abandoned_large_block_translation_is_the_per_block_one() {
    let (module, function) = ever_init_family(3);
    super::large_block::FORCE_VIOLATION.with(|force| force.set(true));
    let fallen_back = translate(&module, function);
    super::large_block::FORCE_VIOLATION.with(|force| force.set(false));
    let per_block = translate_per_block(&module, function);
    assert_eq!(fallen_back.work.large_block_fallbacks, 1);
    assert!(fallen_back.large_block.is_none());
    assert_eq!(format!("{:?}", fallen_back.vc.rules), format!("{:?}", per_block.vc.rules));
    assert_eq!(fallen_back.vc.relations, per_block.vc.relations);
    assert_eq!(fallen_back.diagnostics, per_block.diagnostics);
}

/// Whether `constraints` are satisfiable, over every variable `output` declares.
fn satisfiable(output: &ChcTranslationOutput, constraints: &[ay_bindings::Expr]) -> bool {
    use ay_bindings::execute_direct::{ExecuteResult, execute};
    let mut program = ay_bindings::AYProgram::new();
    program.set_logic("QF_ABV");
    for var in output.vc.vars() {
        let _ = program.declare_const(var.name.to_string(), var.sort.clone());
    }
    for constraint in constraints {
        program.assert(constraint.clone());
    }
    program.check_sat();
    match execute(&program).expect("in-process ay solves the query") {
        ExecuteResult::Counterexample { .. } => true,
        ExecuteResult::Verified => false,
        other => panic!("unexpected solver outcome: {other:?}"),
    }
}

/// JUSTIFICATION holds for EVERY model, not only the ones a solver happens to
/// return: with the error disjunction removed, no transition can be taken
/// without reaching its target (a dropped target included: its selector is
/// `false`), and no block whose error site fires takes a transition.
#[test]
fn justification_makes_every_model_one_derivation() {
    use ay_bindings::{Expr, Sort};
    for (what, (module, function)) in [
        ("ever_init(2)", ever_init_family(2)),
        ("diamond", diamond()),
        ("duplicate_cases", duplicate_cases()),
    ] {
        let output = if what == "duplicate_cases" {
            translate_hostile_algorithm_fixture(&module, function, |error| {
                matches!(error, ValidationError::DuplicateSwitchCase { .. })
            })
        } else {
            translate(&module, function)
        };
        let map = output.large_block.as_ref().expect("one query");
        let query = output
            .vc
            .rules
            .iter()
            .find(|rule| {
                rule.head.name.as_str() == ERROR_REL
                    && rule.body.relation.as_ref().is_some_and(|app| app.name.as_str() == "bb0")
            })
            .expect("the large-block query");
        // Every block formula, without the final `f₁ ∨ … ∨ fₘ`.
        let constraints: Vec<Expr> = query.body.constraints.iter().cloned().collect();
        let blocks = &constraints[..constraints.len() - 1];
        let var = |name: &str| Expr::var(name.to_string(), Sort::bool());
        assert!(satisfiable(&output, blocks), "{what}: the block formulas alone");
        for (target, edges) in &map.in_edges {
            for edge in edges {
                let mut taken = blocks.to_vec();
                taken.push(var(&edge.selector));
                taken.push(var(&format!("bb{}_lbe_r", target.index())).not());
                assert!(
                    !satisfiable(&output, &taken),
                    "{what}: {} taken without reaching bb{}",
                    edge.selector,
                    target.index()
                );
            }
        }
        // A block whose columns select takes at most one in-edge (the ladder),
        // whatever the guards say.
        for (target, edges) in &map.in_edges {
            let selecting = map
                .columns
                .iter()
                .any(|name| name.starts_with(&format!("bb{}_lbe_c", target.index())));
            if !selecting {
                continue;
            }
            for (index, first) in edges.iter().enumerate() {
                for second in edges.iter().skip(index + 1) {
                    let mut both = blocks.to_vec();
                    both.push(var(&first.selector));
                    both.push(var(&second.selector));
                    assert!(
                        !satisfiable(&output, &both),
                        "{what}: {} and {} together into bb{}",
                        first.selector,
                        second.selector,
                        target.index()
                    );
                }
            }
        }
        for site in &map.sites {
            for (_, edges) in &map.in_edges {
                for edge in edges.iter().filter(|edge| edge.source == site.block) {
                    let mut both = blocks.to_vec();
                    both.push(var(&site.var));
                    both.push(var(&edge.selector));
                    assert!(
                        !satisfiable(&output, &both),
                        "{what}: site {} fires and {} is taken",
                        site.var,
                        edge.selector
                    );
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Size, depth and identity on wide joins and shared terms (the 8e principle
// review): every term a block reads is atomic, a selection costs one variable
// per in-edge that passes another term than the column's most frequent one,
// and in-edge terms are compared in O(1).
// ---------------------------------------------------------------------------

/// The query's size as a tree-spelling consumer prints it (every shared node
/// once per use; saturating) and its deepest term, each shared node computed
/// once.
fn tree_size_and_depth(output: &ChcTranslationOutput) -> (u128, usize) {
    let mut memo: HashMap<*const ay_bindings::ExprValue, (u128, usize)> = HashMap::new();
    let mut roots: Vec<&ay_bindings::Expr> = Vec::new();
    for rule in &output.vc.rules {
        roots.extend(rule.body.constraints.iter());
        if let Some(app) = &rule.body.relation {
            roots.extend(app.args.iter());
        }
        roots.extend(rule.head.args.iter());
    }
    let (mut size, mut depth) = (0u128, 0usize);
    for root in roots {
        let mut stack = vec![(root, false)];
        while let Some((node, expanded)) = stack.pop() {
            let key = std::ptr::from_ref(node.value());
            if memo.contains_key(&key) {
                continue;
            }
            if expanded {
                let (mut tree, mut deepest) = (1u128, 0usize);
                for child in node.children() {
                    let (child_tree, child_depth) = memo[&std::ptr::from_ref(child.value())];
                    tree = tree.saturating_add(child_tree);
                    deepest = deepest.max(child_depth);
                }
                memo.insert(key, (tree, deepest + 1));
            } else {
                stack.push((node, true));
                stack.extend(node.children().map(|child| (child, false)));
            }
        }
        let (tree, deepest) = memo[&std::ptr::from_ref(root.value())];
        size = size.saturating_add(tree);
        depth = depth.max(deepest);
    }
    (size, depth)
}

/// `cells(k)`: `k` cells set to 0 in the entry; a `k`-way dispatch chain on the
/// entry's `sel`; arm `i` stores 1 into cell `i`; the join asserts every cell
/// is below 2. Every column of the join differs on exactly one in-edge.
fn cells(k: usize) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("cells");
    let ft = mb.add_func_type(vec![Ty::U64], vec![]);
    let mut fb = mb.function("cells", ft);
    let entry = fb.create_block();
    let dispatch: Vec<BlockId> = (0..k).map(|_| fb.create_block()).collect();
    let arms: Vec<BlockId> = (0..k).map(|_| fb.create_block()).collect();
    let join = fb.create_block();
    fb.set_entry(entry);
    let sel = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let slots: Vec<ValueId> = (0..k)
        .map(|_| {
            let slot = fb.alloca(Ty::U8);
            let zero = fb.iconst(Ty::U8, 0);
            fb.store(Ty::U8, slot, zero);
            slot
        })
        .collect();
    fb.br(dispatch[0], vec![]);
    for i in 0..k {
        fb.switch_to_block(dispatch[i]);
        let case = fb.iconst(Ty::U64, i as i128);
        let hit = fb.icmp(ICmpOp::Eq, Ty::U64, sel, case);
        let next = if i + 1 < k { dispatch[i + 1] } else { join };
        fb.condbr(hit, arms[i], vec![], next, vec![]);
        fb.switch_to_block(arms[i]);
        let one = fb.iconst(Ty::U8, 1);
        fb.store(Ty::U8, slots[i], one);
        fb.br(join, vec![]);
    }
    fb.switch_to_block(join);
    for slot in &slots {
        let value = fb.load(Ty::U8, *slot);
        let two = fb.iconst(Ty::U8, 2);
        let ok = fb.icmp(ICmpOp::Ult, Ty::U8, value, two);
        fb.assert(ok);
    }
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// A `k`-way switch on the entry's `sel`; arm `i` passes `(i % 200) + 1`,
/// computed in the arm, to `join(p)`, the default passes the entry's `x`; the
/// join reads `p` in `uses` assertions `p != 250` (refutable at `x = 250`).
fn wide_join(k: usize, uses: usize) -> (Module, FuncId) {
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
    let cases = (0..k)
        .map(|i| SwitchCase { value: Constant::Int(i as i128), target: arms[i], args: vec![] })
        .collect();
    fb.switch(sel, cases, join, vec![input]);
    for (i, arm) in arms.iter().enumerate() {
        fb.switch_to_block(*arm);
        let literal = fb.iconst(Ty::U8, (i % 200) as i128);
        let one = fb.iconst(Ty::U8, 1);
        let passed = fb.add(Ty::U8, literal, one);
        fb.br(join, vec![passed]);
    }
    fb.switch_to_block(join);
    for _ in 0..uses {
        let forbidden = fb.iconst(Ty::U8, 250);
        let ok = fb.icmp(ICmpOp::Ne, Ty::U8, joined, forbidden);
        fb.assert(ok);
    }
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// `entry(x, c)`: each arm of `c` squares `x` `k` times (`a ← a·a`, the same
/// DAG shape built separately in each arm) and passes it to `join(p)`, which
/// asserts `p != 3`.
fn squares(k: usize) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("squares");
    let ft = mb.add_func_type(vec![Ty::U64, Ty::Bool], vec![]);
    let mut fb = mb.function("squares", ft);
    let (entry, left, right, join) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    let input = fb.add_block_param(entry, Ty::U64);
    let choice = fb.add_block_param(entry, Ty::Bool);
    let joined = fb.add_block_param(join, Ty::U64);
    fb.switch_to_block(entry);
    fb.condbr(choice, left, vec![], right, vec![]);
    for arm in [left, right] {
        fb.switch_to_block(arm);
        let mut power = input;
        for _ in 0..k {
            power = fb.mul(Ty::U64, power, power);
        }
        fb.br(join, vec![power]);
    }
    fb.switch_to_block(join);
    let three = fb.iconst(Ty::U64, 3);
    let ok = fb.icmp(ICmpOp::Ne, Ty::U64, joined, three);
    fb.assert(ok);
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

/// On joins whose in-degree quadruples (up to 4 096), the query a tree-spelling
/// consumer prints grows at most 4.5x, and its deepest term not at all: the
/// selection is a chain of depth-one definitions over the in-edges that pass
/// another term than the most frequent one, read through one variable.
#[test]
fn wide_joins_stay_linear_and_shallow() {
    type Family = fn(usize) -> (Module, FuncId);
    // `cells` stops at 1 024: its K cells are live down the K-block dispatch
    // chain, and the translator's liveness — not the query — is Θ(K²) there
    // (docs/DECISION_QUEUE.md, 8e, "Not done").
    let families: [(&str, Family, &[usize]); 3] = [
        ("cells", cells, &[16, 64, 256, 1024]),
        ("fanuse", |k| wide_join(k, k), &[16, 64, 256, 1024, 4096]),
        ("param", |k| wide_join(k, 1), &[16, 64, 256, 1024, 4096]),
    ];
    for (name, family, sizes) in families {
        let mut previous: Option<(u128, usize)> = None;
        for &k in sizes {
            let (module, function) = family(k);
            let output = translate(&module, function);
            assert!(output.large_block.is_some(), "{name}({k})");
            assert_eq!(output.work.large_block_fallbacks, 0, "{name}({k})");
            let (size, depth) = tree_size_and_depth(&output);
            if let Some((prev_size, prev_depth)) = previous {
                // `k` quadruples per step: at most 4.5x (a quadratic would be 16x).
                assert!(size * 2 <= prev_size * 9, "{name}({k}): tree size {prev_size} -> {size}");
                assert_eq!(depth, prev_depth, "{name}({k}): depth {prev_depth} -> {depth}");
            }
            assert!(depth <= 16, "{name}({k}): depth {depth}");
            previous = Some((size, depth));
        }
    }
    // `cells`: one column variable per cell (its one differing in-edge), not
    // one per (cell, arm).
    let (module, function) = cells(64);
    let output = translate(&module, function);
    assert!(output.work.large_block_column_variables <= 2 * 64, "{:?}", output.work);
}

/// In-edge terms are compared by identity, never by a structural walk: two arms
/// that each square `x` 64 times build the same DAG shape separately, and the
/// join reads one column variable over them (a structural comparison would
/// walk 2^64 paths).
#[test]
fn in_edge_terms_are_compared_by_identity() {
    let (module, function) = squares(64);
    let output = translate(&module, function);
    let map = output.large_block.as_ref().expect("one query");
    assert_eq!(map.columns.len(), 1, "{:?}", map.columns);
    assert_eq!(output.work.large_block_fallbacks, 0);
}

/// The region's dominator tree answers exactly what removing a block from the
/// CFG does to reachability, on random DAGs (including joins of in-degree up
/// to 6 and long chains).
#[test]
fn region_dominators_match_brute_force() {
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    let mut below = |bound: usize| {
        state =
            state.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        ((state >> 33) as usize) % bound
    };
    for _ in 0..200 {
        let n = 2 + below(30);
        // Node `i > 0` gets 1..=3 predecessors among `0..i`, so `0..n` is a
        // topological order and every node is reachable from 0.
        let preds: Vec<Vec<usize>> = (0..n)
            .map(|i| if i == 0 { Vec::new() } else { (0..=below(3)).map(|_| below(i)).collect() })
            .collect();
        let order: Vec<BlockId> = (0..n).map(|i| BlockId::new(i as u32)).collect();
        let tree = super::large_block::RegionDominators::new(&order, &preds);
        let mut successors = vec![Vec::new(); n];
        for (node, sources) in preds.iter().enumerate() {
            for &source in sources {
                successors[source].push(node);
            }
        }
        for a in 0..n {
            // Reachability from 0 with `a` removed.
            let mut reached = vec![false; n];
            if a != 0 {
                reached[0] = true;
                let mut stack = vec![0];
                while let Some(node) = stack.pop() {
                    for &next in &successors[node] {
                        if next != a && !reached[next] {
                            reached[next] = true;
                            stack.push(next);
                        }
                    }
                }
            }
            for b in 0..n {
                let expected = a == b || !reached[b];
                assert_eq!(tree.dominates(order[a], order[b]), expected, "{preds:?}: {a} dom {b}");
            }
        }
    }
    assert!(
        !super::large_block::RegionDominators::new(&[BlockId::new(0)], &[Vec::new()])
            .dominates(BlockId::new(0), BlockId::new(1))
    );
}

// ---------------------------------------------------------------------------
// Fat-pointer parts across blocks (the 8e soundness review's blocker)
// ---------------------------------------------------------------------------

fn slice_ty(mb: &mut ModuleBuilder) -> Ty {
    let u8_id = mb.add_type(Ty::U8);
    Ty::FatPtr(FatPtrKind::Slice(u8_id))
}

/// `PtrMetadata(fat) + 1`, overflow-checked (the blocker's shape).
fn len_plus_one(fb: &mut FunctionBuilder<'_>, fat_ty: &Ty, fat: ValueId) {
    let len = fb.ptr_metadata(fat_ty.clone(), Ty::U64, fat);
    let one = fb.iconst(Ty::U64, 1);
    let (_, overflowed) = fb.overflow(OverflowOp::AddOverflow, Ty::U64, len, one);
    let no = fb.bool_const(false);
    let ok = fb.icmp(ICmpOp::Eq, Ty::Bool, overflowed, no);
    fb.assert(ok);
}

/// `f(data, n)`: the entry builds `fat = PtrFromParts(data, n + extra)` (a
/// compound metadata when `extra`), copies it in `next` and reads its length
/// in `next` and in `last`.
fn raw_slice_across_blocks(extra: bool) -> (Module, FuncId) {
    let mut mb = ModuleBuilder::new("raw_slice_across_blocks");
    let fat_ty = slice_ty(&mut mb);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::U64], vec![]);
    let mut fb = mb.function("f", ft);
    let (entry, next, last) = (fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    let data = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    fb.switch_to_block(entry);
    let len = if extra {
        let two = fb.iconst(Ty::U64, 2);
        fb.add(Ty::U64, n, two)
    } else {
        n
    };
    let fat = fb.ptr_from_parts(fat_ty.clone(), Ty::U64, data, len);
    fb.br(next, vec![]);
    fb.switch_to_block(next);
    let copy = fb.copy(fat_ty.clone(), fat);
    len_plus_one(&mut fb, &fat_ty, fat);
    fb.br(last, vec![]);
    fb.switch_to_block(last);
    len_plus_one(&mut fb, &fat_ty, copy);
    fb.ret(vec![]);
    let function = fb.build();
    (mb.build().expect("ModuleBuilder::build: test fixture"), function)
}

fn mentions_var(output: &ChcTranslationOutput, needle: &str) -> bool {
    output.vc.vars().iter().any(|var| var.name.contains(needle))
}

/// In the large-block query a dominated block reads a fat pointer's parts
/// EXACTLY — the entry's own `n`, never a `slice_len` symbol with its
/// `isize::MAX` bound (the false proof the soundness review found) — and a
/// compound part through one part variable. The per-block encoding reads them
/// in a later block as an OPAQUE value: an unbounded `fat_metadata` havoc, and
/// never the earlier rule's variables free.
#[test]
fn fat_pointer_parts_across_blocks() {
    for extra in [false, true] {
        let (module, function) = raw_slice_across_blocks(extra);
        let large = translate(&module, function);
        let map = large.large_block.as_ref().expect("one query");
        assert!(!mentions_var(&large, "slice_len"), "extra={extra}");
        assert!(!mentions_var(&large, "fat_metadata"), "extra={extra}");
        let part_variables = map.columns.iter().filter(|name| name.contains("_lbe_m")).count();
        // `n + 2` is read in two blocks through ONE part variable, owned by the
        // entry; the plain `n` needs none.
        assert_eq!(part_variables, usize::from(extra), "extra={extra}: {:?}", map.columns);

        let per_block = translate_per_block(&module, function);
        assert!(!mentions_var(&per_block, "slice_len"), "extra={extra}");
        assert!(mentions_var(&per_block, "fat_metadata"), "extra={extra}");
        // No rule reads a variable that is neither one of its relation
        // arguments nor a havoc: an earlier rule's variable is never free here.
        for rule in &per_block.vc.rules {
            let mut bound: BTreeSet<String> = BTreeSet::new();
            let args = rule.body.relation.iter().flat_map(|app| app.args.iter());
            for arg in args.chain(rule.head.args.iter()) {
                collect_var_names(arg, &mut bound);
            }
            let mut read = BTreeSet::new();
            for constraint in rule.body.constraints.iter() {
                collect_var_names(constraint, &mut read);
            }
            for name in read {
                assert!(
                    bound.contains(&name) || trust_mc_core::chc::is_translation_havoc_var(&name),
                    "extra={extra}: `{name}` is free in {rule:?}"
                );
            }
        }
    }
}

fn collect_var_names(expr: &ay_bindings::Expr, names: &mut BTreeSet<String>) {
    let mut stack = vec![expr];
    let mut seen = BTreeSet::new();
    while let Some(node) = stack.pop() {
        if !seen.insert(std::ptr::from_ref(node.value())) {
            continue;
        }
        if let ay_bindings::ExprValue::Var { name } = node.value() {
            names.insert(name.clone());
        }
        stack.extend(node.children());
    }
}

/// A fat pointer built in a block that does NOT dominate its reader — an SSA
/// violation a hand-built module can still spell — is read as OPAQUE in the
/// large-block query too: off the building block's path its variables mean
/// nothing (a column variable there is its default), so its parts must not be.
#[test]
fn parts_from_a_block_that_does_not_dominate_are_opaque() {
    let mut mb = ModuleBuilder::new("non_dominating_parts");
    let fat_ty = slice_ty(&mut mb);
    let ft = mb.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Bool], vec![]);
    let mut fb = mb.function("f", ft);
    let (entry, left, right, join) =
        (fb.create_block(), fb.create_block(), fb.create_block(), fb.create_block());
    fb.set_entry(entry);
    let data = fb.add_block_param(entry, Ty::Ptr);
    let n = fb.add_block_param(entry, Ty::U64);
    let c = fb.add_block_param(entry, Ty::Bool);
    fb.switch_to_block(entry);
    fb.condbr(c, left, vec![], right, vec![]);
    fb.switch_to_block(left);
    let fat = fb.ptr_from_parts(fat_ty.clone(), Ty::U64, data, n);
    fb.br(join, vec![]);
    fb.switch_to_block(right);
    fb.br(join, vec![]);
    fb.switch_to_block(join);
    len_plus_one(&mut fb, &fat_ty, fat);
    fb.ret(vec![]);
    let function = fb.build();
    let module = mb.build().expect("ModuleBuilder::build: test fixture");
    let large = translate_hostile_algorithm_fixture(&module, function, |error| {
        matches!(error, ValidationError::UseBeforeDefInBlock { .. })
    });
    assert!(large.large_block.is_some());
    assert!(mentions_var(&large, "fat_metadata"));
    assert!(!mentions_var(&large, "slice_len"));
}
