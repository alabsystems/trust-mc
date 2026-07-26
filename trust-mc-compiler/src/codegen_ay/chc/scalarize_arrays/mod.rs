// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Post-pruning scalarization of constant-index array state variables.
//!
//! For Array-sorted state variables where ALL Store/Select operations in
//! CHC rule constraint bodies use constant (bitvec literal) indices, this
//! pass replaces the single Array parameter with N scalar parameters
//! (one per unique constant index).
//!
//! **Why this matters:** The ay-chc PDR engine cannot synthesize inductive
//! invariants when CHC relation predicates carry ≥2 Array-sorted parameters.
//! This is the structural bottleneck for ~57% of UNKNOWN harnesses (heap and
//! collection patterns). Scalarizing constant-index arrays pushes the count
//! below that threshold, enabling PROOF.
//!
//! **How it works:** After `prune_vc_unused_type_arrays` removes dead arrays,
//! this pass scans the surviving arrays' Store/Select usage in constraint
//! bodies. Arrays where every index is a bitvec constant are replaced with
//! one scalar state variable per unique constant index. The relation
//! declarations, relation applications, and constraint expressions are all
//! rewritten.
//!
//! Part of #4050: PDR array-param bottleneck optimization.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort};
use num_bigint::BigInt;
use trust_mc_core::chc::{ChcVc, VarDecl};

use super::codegen_ctx::{ChcCtx, chc_debug_enabled};

mod collapse_mid_aliases;
mod const_fold;
mod const_fold_apply;
mod lane_dependencies;
mod output_copies;
mod protect_lanes;
mod prune_dead_scalars;
mod rewrite;
use lane_dependencies::{
    LaneDependency, is_supported_array_base, output_var_usage_supported, propagate_required_lanes,
};
pub(in crate::codegen_ay) use rewrite::scalarize_vc;
use rewrite::{RewriteMaps, rewrite_expr_children};

/// Maximum number of scalar replacements per array variable.
/// Keep this bounded, but high enough for the fixed-width SIMD array
/// replacement harnesses that compare all lanes of `[u8; 16]`.
const MAX_SCALARS_PER_ARRAY: usize = 16;

/// Stack red-zone / segment sizes for `stacker::maybe_grow`, mirroring
/// ay-bindings `fold_expr` (#8414). The `rewrite_expr` / `rewrite_expr_children`
/// mutual recursion descends deep dyn-trait Store chains that can overflow the
/// native stack; growing onto a heap-backed segment is verdict-identical.
const REWRITE_STACK_RED_ZONE: usize = 32 * 1024;
const REWRITE_STACK_SIZE: usize = 1024 * 1024;

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Scalarize constant-index array state variables in the VC.
    ///
    /// Runs after `prune_vc_unused_type_arrays`. For each surviving
    /// Array-sorted state variable, checks whether all Store/Select
    /// operations use constant BV indices. If so, replaces the array
    /// with scalar state variables (one per constant index).
    pub(super) fn scalarize_const_index_arrays(&mut self) {
        rewrite::scalarize_vc(&mut self.vc);
    }
}

/// A constant bitvec index extracted from an expression.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct ConstIdx {
    pub(super) value: BigInt,
    pub(super) width: u32,
}

impl ConstIdx {
    /// Format as a hex string for use in variable names.
    pub(super) fn hex_label(&self) -> String {
        format!("0x{:x}_bv{}", self.value, self.width)
    }
}

/// Information about a scalarizable array variable pair (input + output).
pub(super) struct ScalarInfo {
    /// The input variable name (e.g., `region_44_bv32`).
    pub(super) input_name: String,
    /// The output variable name (e.g., `region_44_bv32__out`).
    pub(super) output_name: String,
    /// The element sort of the array (e.g., `BV32`).
    pub(super) elem_sort: Sort,
    /// The constant indices, sorted for determinism.
    /// Maps each constant index to the scalar var base name.
    pub(super) index_to_scalar: BTreeMap<ConstIdx, String>,
}

pub(super) struct RewriteContext {
    extra_vars: Vec<VarDecl>,
    next_dead_const_lane: usize,
    /// Input names of scalarized arrays whose rewrite encountered a select
    /// with a SYMBOLIC index that identification never vetted. Completing the
    /// scalarization of such an array is unsound: the historical fallback
    /// minted an unconstrained `_select_any_N` free variable (optionally
    /// wrapped in a tracked-lane ITE whose else-branch was still that free
    /// var), which lets the solver pick the read result at will and fabricate
    /// counterexample witnesses (false CTREX). The orchestrator
    /// (`scalarize_vc`) treats a non-empty set as a fail-closed signal: it
    /// discards the staged rewrite, bans these arrays, and re-runs
    /// identification so the arrays (and anything lane-dependent on them)
    /// survive the pass as real arrays with their actual constraints.
    rejected_arrays: BTreeSet<String>,
}

impl RewriteContext {
    pub(super) fn new() -> Self {
        Self { extra_vars: Vec::new(), next_dead_const_lane: 0, rejected_arrays: BTreeSet::new() }
    }

    pub(super) fn take_extra_vars(self) -> Vec<VarDecl> {
        self.extra_vars
    }

    pub(super) fn rejected_arrays(&self) -> &BTreeSet<String> {
        &self.rejected_arrays
    }

    fn reject_array(&mut self, input_name: &str) {
        self.rejected_arrays.insert(input_name.to_string());
    }

    /// Mint a fresh variable for a select at a CONSTANT index on an untracked
    /// lane. See `rewrite_expr` for the proof that such lanes are dead.
    fn dead_const_lane_var(&mut self, array_name: &str, sort: &Sort) -> Expr {
        let name = format!("{array_name}_dead_const_lane_{}", self.next_dead_const_lane);
        self.next_dead_const_lane += 1;
        self.extra_vars.push(VarDecl::new(name.clone(), sort.clone()));
        Expr::var(name, sort.clone())
    }
}

impl ScalarInfo {
    pub(super) fn scalar_input_name(&self, idx: &ConstIdx) -> String {
        self.index_to_scalar[idx].clone()
    }

    pub(super) fn scalar_output_name(&self, idx: &ConstIdx) -> String {
        format!("{}__out", self.index_to_scalar[idx])
    }
}

// ---------------------------------------------------------------------------
// Phase 1: Identify scalarizable arrays
// ---------------------------------------------------------------------------

/// Try to extract a constant bitvec index from an expression.
///
/// Handles compound constant expressions common in heap encoding:
/// - `BitVecConst` — direct constant
/// - `BvConcat(const, const)` — heap addresses: `concat(obj_id_32, offset_32)`
/// - `BvExtract(const_expr, high, low)` — obj_id extraction: `extract[63:32](ptr)`
/// - `BvAdd(const, const)` — struct field offsets: `base_addr + field_offset`
pub(super) fn try_extract_const_idx(expr: &Expr) -> Option<ConstIdx> {
    match expr.value() {
        ExprValue::BitVecConst { value, width } => {
            Some(ConstIdx { value: value.clone(), width: *width })
        }
        ExprValue::BvConcat(high, low) => {
            let h = try_extract_const_idx(high)?;
            let l = try_extract_const_idx(low)?;
            let combined_width = h.width + l.width;
            let combined_value = (h.value << l.width) | l.value;
            Some(ConstIdx { value: combined_value, width: combined_width })
        }
        ExprValue::BvExtract { expr: inner, high, low } => {
            let base = try_extract_const_idx(inner)?;
            let mask = (BigInt::from(1u64) << (high - low + 1)) - 1;
            let extracted = (base.value >> low) & mask;
            Some(ConstIdx { value: extracted, width: high - low + 1 })
        }
        ExprValue::BvAdd(lhs, rhs) => {
            let l = try_extract_const_idx(lhs)?;
            let r = try_extract_const_idx(rhs)?;
            if l.width != r.width {
                return None;
            }
            Some(ConstIdx { value: l.value + r.value, width: l.width })
        }
        // Fallback: delegate to the full BV constant evaluator for ops
        // not handled above (BvSub, BvMul, BvShl, BvZeroExtend, etc.).
        _ => {
            let folded = trust_mc_core::chc_const_prop::eval::try_eval_to_const(expr)?;
            if let ExprValue::BitVecConst { value, width } = folded.value() {
                Some(ConstIdx { value: value.clone(), width: *width })
            } else {
                None
            }
        }
    }
}

/// Decompose a store chain into (base_var_name, [(const_idx, value_expr), ...]).
///
/// Returns `None` if the chain contains any symbolic (non-constant) index
/// or the base is not a simple Var.
pub(super) fn decompose_store_chain(expr: &Expr) -> Option<(String, Vec<(ConstIdx, Expr)>)> {
    match expr.value() {
        ExprValue::Var { name } => Some((name.clone(), Vec::new())),
        ExprValue::Store { array, index, value } => {
            let idx = try_extract_const_idx(index)?;
            let (base, mut pairs) = decompose_store_chain(array)?;
            pairs.push((idx, value.clone()));
            Some((base, pairs))
        }
        ExprValue::ConstArray { .. } => Some(("__const_array__".to_string(), Vec::new())),
        _ => None,
    }
}

pub(super) fn const_array_default_for_store_chain(expr: &Expr) -> Option<&Expr> {
    match expr.value() {
        ExprValue::ConstArray { value, .. } => Some(value),
        ExprValue::Store { array, .. } => const_array_default_for_store_chain(array),
        _ => None,
    }
}

/// Classification result for a constraint expression's array usage.
enum ArrayUse {
    /// `(= out_var (store ... chain ...))` — store chain with constant indices.
    StoreChain { base: String, stores: Vec<(ConstIdx, Expr)> },
    /// `(= out_var const_array)` — initialization with constant array.
    ConstArrayInit,
    /// `(= out_var input_var)` — explicit identity (rare, usually implicit).
    ExplicitIdentity { base: String },
    /// The constraint doesn't involve the target array.
    NotRelated,
    /// The constraint uses the array in an unrecognized pattern.
    Unrecognized,
}

/// Analyze a top-level constraint for array-output patterns.
fn classify_constraint_for_array(
    constraint: &Expr,
    target_input: &str,
    target_output: &str,
    input_vars: &HashMap<String, Sort>,
) -> ArrayUse {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        if expr_mentions_var(constraint, target_output) {
            return ArrayUse::Unrecognized;
        }
        return ArrayUse::NotRelated;
    };

    let (out_expr, val_expr) = if matches!(lhs.value(), ExprValue::Var { name } if name == target_output)
    {
        (lhs, rhs)
    } else if matches!(rhs.value(), ExprValue::Var { name } if name == target_output) {
        (rhs, lhs)
    } else if expr_mentions_var(constraint, target_output) {
        return if output_var_usage_supported(constraint, target_output)
            || transparently_forwards_target_output(lhs, rhs, target_output)
        {
            ArrayUse::NotRelated
        } else {
            ArrayUse::Unrecognized
        };
    } else {
        return ArrayUse::NotRelated;
    };

    if !matches!(out_expr.value(), ExprValue::Var { .. }) {
        return ArrayUse::Unrecognized;
    }

    match val_expr.value() {
        ExprValue::Var { name } if name == target_input => {
            ArrayUse::ExplicitIdentity { base: name.clone() }
        }
        ExprValue::Var { name } => ArrayUse::ExplicitIdentity { base: name.clone() },
        ExprValue::ConstArray { .. } => ArrayUse::ConstArrayInit,
        ExprValue::Store { .. } => {
            if let Some((base, stores)) = decompose_store_chain(val_expr) {
                ArrayUse::StoreChain { base, stores }
            } else {
                ArrayUse::Unrecognized
            }
        }
        _ => {
            if let Some(base) = transparent_forwarded_array_base(val_expr, &|name| {
                input_vars.contains_key(name)
                    || name
                        .strip_suffix("__out")
                        .is_some_and(|input_name| input_vars.contains_key(input_name))
            }) {
                ArrayUse::ExplicitIdentity { base }
            } else {
                ArrayUse::Unrecognized
            }
        }
    }
}

fn transparently_forwards_target_output(lhs: &Expr, rhs: &Expr, target_output: &str) -> bool {
    let is_target = |name: &str| name == target_output;
    matches!(
        transparent_forwarded_array_base(lhs, &is_target)
            .or_else(|| transparent_forwarded_array_base(rhs, &is_target)),
        Some(base) if base == target_output
    )
}

/// Detect expressions that only forward one candidate array through datatype
/// constructors/selectors, such as `fld_data(Slice_mk(ptr, len, arr))`.
pub(super) fn transparent_forwarded_array_base<F>(expr: &Expr, is_candidate: &F) -> Option<String>
where
    F: Fn(&str) -> bool,
{
    if !expr.sort().is_array() {
        return None;
    }
    collect_transparent_forwarded_array_base(expr, is_candidate).ok().flatten()
}

fn collect_transparent_forwarded_array_base<F>(
    expr: &Expr,
    is_candidate: &F,
) -> Result<Option<String>, ()>
where
    F: Fn(&str) -> bool,
{
    match expr.value() {
        ExprValue::Var { name } if is_candidate(name) => Ok(Some(name.clone())),
        ExprValue::Var { .. }
        | ExprValue::BoolConst(_)
        | ExprValue::BitVecConst { .. }
        | ExprValue::IntConst(_)
        | ExprValue::RealConst(_) => Ok(None),
        ExprValue::DatatypeSelector { selector_name, expr: inner, .. } => {
            collect_transparent_selector_base(selector_name, inner, is_candidate)
        }
        ExprValue::DatatypeConstructor { args, .. } => {
            merge_transparent_child_bases(args.iter(), is_candidate)
        }
        ExprValue::Ite { cond, then_expr, else_expr } => {
            if expr_mentions_candidate_var(cond, is_candidate) {
                return Err(());
            }
            let then_base = collect_transparent_forwarded_array_base(then_expr, is_candidate)?;
            let else_base = collect_transparent_forwarded_array_base(else_expr, is_candidate)?;
            if then_base == else_base { Ok(then_base) } else { Err(()) }
        }
        ExprValue::Store { .. } | ExprValue::Select { .. } | ExprValue::ConstArray { .. } => {
            Err(())
        }
        _ => {
            if expr_mentions_candidate_var(expr, is_candidate) {
                Err(())
            } else {
                Ok(None)
            }
        }
    }
}

fn collect_transparent_selector_base<F>(
    selector_name: &str,
    inner: &Expr,
    is_candidate: &F,
) -> Result<Option<String>, ()>
where
    F: Fn(&str) -> bool,
{
    let ExprValue::DatatypeConstructor { constructor_name, args, .. } = inner.value() else {
        return if expr_mentions_candidate_var(inner, is_candidate) { Err(()) } else { Ok(None) };
    };
    let Some(dt) = inner.sort().datatype_sort() else {
        return Err(());
    };
    let Some(ctor) = dt.constructors.iter().find(|ctor| &*ctor.name == constructor_name) else {
        return Err(());
    };
    let Some(field_idx) = ctor.fields.iter().position(|field| &*field.name == selector_name) else {
        return Err(());
    };
    let Some(selected_arg) = args.get(field_idx) else {
        return Err(());
    };
    collect_transparent_forwarded_array_base(selected_arg, is_candidate)
}

fn merge_transparent_child_bases<'a, I, F>(
    children: I,
    is_candidate: &F,
) -> Result<Option<String>, ()>
where
    I: IntoIterator<Item = &'a Expr>,
    F: Fn(&str) -> bool,
{
    let mut base: Option<String> = None;
    for child in children {
        let child_base = collect_transparent_forwarded_array_base(child, is_candidate)?;
        if let Some(child_base) = child_base {
            match &base {
                Some(existing) if existing != &child_base => return Err(()),
                Some(_) => {}
                None => base = Some(child_base),
            }
        }
    }
    Ok(base)
}

fn expr_mentions_candidate_var<F>(expr: &Expr, is_candidate: &F) -> bool
where
    F: Fn(&str) -> bool,
{
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } if is_candidate(name) => return true,
            _ => stack.extend(node.children()),
        }
    }
    false
}

/// Check if an expression tree references a specific variable name.
fn expr_mentions_var(expr: &Expr, target: &str) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } if name == target => return true,
            _ => stack.extend(node.children()),
        }
    }
    false
}

/// Collect constant-index Select operations on a target variable.
///
/// Returns `Ok(indices)` for constant-index selects, `Err(())` if any
/// select targets a non-Var base OR uses a symbolic index. Symbolic-index
/// selects produce a soundness hole: the prior rewrite-to-tracked-lane-ITE
/// fallback returned a fresh unconstrained var, which the solver picks
/// freely, fabricating witnesses (e.g., `tests/ay/btreemap_store_dual_select::store_select_original_only`
/// CTREX'd because `a.select(j)` lowered to two `_select_any_*` free vars
/// instead of reading `a.stores`'s actual `const_array(default)`).
fn collect_selects_on_var(expr: &Expr, target_var: &str) -> Result<Vec<ConstIdx>, ()> {
    let mut indices = Vec::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Select { array, index } => {
                if matches!(array.value(), ExprValue::Var { name } if name == target_var) {
                    if let Some(idx) = try_extract_const_idx(index) {
                        indices.push(idx);
                    } else {
                        return Err(());
                    }
                } else if expr_mentions_var(array, target_var) {
                    return Err(());
                }
                stack.push(index);
            }
            _ => {
                stack.extend(node.children());
            }
        }
    }
    Ok(indices)
}

/// Scan the VC to identify arrays eligible for scalarization.
///
/// `banned` holds input names that previously FAILED a staged rewrite (see
/// `RewriteContext::rejected_arrays`). Banned arrays are excluded from the
/// candidate set entirely, so arrays that copy from / store onto them are
/// rejected through the regular `is_supported_array_base` /
/// `propagate_required_lanes` paths — unwinding the whole dependent group
/// instead of leaving it half-scalarized against a missing base.
pub(super) fn identify_scalarizable_arrays(
    vc: &ChcVc,
    banned: &BTreeSet<String>,
) -> Vec<ScalarInfo> {
    // Step 1: Find Array-sorted var pairs from declare-var entries.
    let mut input_vars: HashMap<String, Sort> = HashMap::new();
    for v in vc.vars() {
        if v.sort.is_array() && !v.name.ends_with("__out") && !banned.contains(&*v.name) {
            input_vars.insert(v.name.to_string(), v.sort.clone());
        }
    }
    if chc_debug_enabled() {
        let mut names: Vec<_> = input_vars.keys().collect();
        names.sort();
        tracing::debug!("scalarize: {} candidate arrays: {names:?}", input_vars.len());
    }

    // Step 2: Collect constant indices per array, rejecting symbolic usage.
    let (var_indices, non_scalarizable) = scan_array_usage(vc, &input_vars);

    // Step 3: Build ScalarInfo for qualifying arrays.
    build_scalar_infos(input_vars, var_indices, &non_scalarizable)
}

/// Scan all rules to collect constant indices and detect symbolic array usage.
fn scan_array_usage(
    vc: &ChcVc,
    input_vars: &HashMap<String, Sort>,
) -> (HashMap<String, HashSet<ConstIdx>>, HashSet<String>) {
    let mut var_indices: HashMap<String, HashSet<ConstIdx>> = HashMap::new();
    let mut non_scalarizable: HashSet<String> = HashSet::new();
    let mut dependencies = Vec::new();
    let scan_constraints = collect_scan_constraints(vc);

    for (input_name, _sort) in input_vars {
        let output_name = format!("{input_name}__out");
        let mut all_indices: HashSet<ConstIdx> = HashSet::new();
        for scan_constraint in &scan_constraints {
            let mentions_input = scan_constraint.vars.contains(input_name.as_str());
            let mentions_output = scan_constraint.vars.contains(output_name.as_str());
            if !mentions_input && !mentions_output {
                continue;
            }

            let constraint = scan_constraint.expr;
            if scan_constraint.is_entry_rule
                && is_entry_pointwise_seed_for_array(constraint, input_name)
            {
                continue;
            }

            if mentions_input {
                match collect_selects_on_var(constraint, input_name) {
                    Ok(indices) => all_indices.extend(indices),
                    Err(()) => {
                        if chc_debug_enabled() {
                            tracing::debug!("scalarize: REJECT {input_name} -- symbolic select");
                        }
                        non_scalarizable.insert(input_name.clone());
                        break;
                    }
                }
            }
            if mentions_output {
                match collect_selects_on_var(constraint, &output_name) {
                    Ok(indices) => all_indices.extend(indices),
                    Err(()) => {
                        if chc_debug_enabled() {
                            tracing::debug!(
                                "scalarize: REJECT {input_name} -- symbolic output select"
                            );
                        }
                        non_scalarizable.insert(input_name.clone());
                        break;
                    }
                }
            }

            if !mentions_output {
                continue;
            }

            let classification =
                classify_constraint_for_array(constraint, input_name, &output_name, input_vars);
            match classification {
                ArrayUse::StoreChain { base, stores } => {
                    if !is_supported_array_base(&base, input_vars) {
                        if chc_debug_enabled() {
                            tracing::debug!(
                                "scalarize: REJECT {input_name} -- unsupported store base {base}"
                            );
                        }
                        non_scalarizable.insert(input_name.clone());
                        break;
                    }
                    for (idx, _) in &stores {
                        all_indices.insert(idx.clone());
                    }
                    if base.as_str() != input_name && base != "__const_array__" {
                        dependencies.push(LaneDependency::StoreBase {
                            dst: input_name.clone(),
                            base,
                            overwritten: stores.into_iter().map(|(idx, _)| idx).collect(),
                        });
                    }
                }
                ArrayUse::ExplicitIdentity { base } => {
                    if base.as_str() != input_name {
                        if !is_supported_array_base(&base, input_vars) {
                            if chc_debug_enabled() {
                                tracing::debug!(
                                    "scalarize: REJECT {input_name} -- unsupported copy base {base}"
                                );
                            }
                            non_scalarizable.insert(input_name.clone());
                            break;
                        }
                        dependencies.push(LaneDependency::Copy { dst: input_name.clone(), base });
                    }
                }
                ArrayUse::ConstArrayInit | ArrayUse::NotRelated => {}
                ArrayUse::Unrecognized => {
                    if chc_debug_enabled() {
                        tracing::debug!(
                            "scalarize: REJECT {input_name} -- unrecognized: {constraint:?}"
                        );
                    }
                    non_scalarizable.insert(input_name.clone());
                    break;
                }
            }
        }

        if !non_scalarizable.contains(input_name) {
            var_indices.insert(input_name.clone(), all_indices);
        }
    }

    propagate_required_lanes(
        &mut var_indices,
        &mut non_scalarizable,
        &dependencies,
        input_vars,
        MAX_SCALARS_PER_ARRAY,
    );

    (var_indices, non_scalarizable)
}

struct ScanConstraint<'a> {
    expr: &'a Expr,
    is_entry_rule: bool,
    vars: HashSet<String>,
}

fn collect_scan_constraints(vc: &ChcVc) -> Vec<ScanConstraint<'_>> {
    let mut result = Vec::new();
    for rule in &vc.rules {
        let is_entry_rule = rule.body.relation.is_none();
        for constraint in rule.body.constraints.iter() {
            push_scan_constraint(constraint, is_entry_rule, &mut result);
        }
    }
    result
}

fn push_scan_constraint<'a>(
    constraint: &'a Expr,
    is_entry_rule: bool,
    result: &mut Vec<ScanConstraint<'a>>,
) {
    if is_entry_rule && let ExprValue::And(conjuncts) = constraint.value() {
        for conjunct in conjuncts {
            push_scan_constraint(conjunct, is_entry_rule, result);
        }
        return;
    }

    result.push(ScanConstraint {
        expr: constraint,
        is_entry_rule,
        vars: collect_expr_vars(constraint),
    });
}

fn collect_expr_vars(expr: &Expr) -> HashSet<String> {
    let mut vars = HashSet::new();
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } => {
                vars.insert(name.clone());
            }
            _ => stack.extend(node.children()),
        }
    }
    vars
}

fn is_entry_pointwise_seed_for_array(constraint: &Expr, target_var: &str) -> bool {
    let ExprValue::Eq(lhs, rhs) = constraint.value() else {
        return false;
    };

    is_pointwise_seed_pair(lhs, rhs, target_var) || is_pointwise_seed_pair(rhs, lhs, target_var)
}

fn is_pointwise_seed_pair(select_side: &Expr, value_side: &Expr, target_var: &str) -> bool {
    let ExprValue::Select { array, index } = select_side.value() else {
        return false;
    };
    if !matches!(array.value(), ExprValue::Var { name } if name == target_var) {
        return false;
    }
    try_extract_const_idx(index).is_some() && !expr_mentions_var(value_side, target_var)
}

/// Build ScalarInfo entries from qualifying arrays.
fn build_scalar_infos(
    input_vars: HashMap<String, Sort>,
    var_indices: HashMap<String, HashSet<ConstIdx>>,
    non_scalarizable: &HashSet<String>,
) -> Vec<ScalarInfo> {
    let mut result = Vec::new();
    for (input_name, indices) in var_indices {
        // Empty index sets are still useful: the array is only initialized or
        // forwarded, so relation-app expansion can drop the Array parameter.
        if indices.len() > MAX_SCALARS_PER_ARRAY {
            if chc_debug_enabled() {
                tracing::debug!(
                    "scalarize: SKIP {input_name} — {} > MAX {MAX_SCALARS_PER_ARRAY}",
                    indices.len()
                );
            }
            continue;
        }
        if non_scalarizable.contains(&input_name) {
            continue;
        }

        let sort = input_vars.get(&input_name).expect("input var exists");
        let elem_sort = sort.array_sort().expect("already verified as array").element_sort.clone();

        let mut sorted_indices: Vec<ConstIdx> = indices.into_iter().collect();
        sorted_indices.sort();

        let mut index_to_scalar = BTreeMap::new();
        for idx in &sorted_indices {
            let scalar_name = format!("{}_at_{}", input_name, idx.hex_label());
            index_to_scalar.insert(idx.clone(), scalar_name);
        }

        let output_name = format!("{input_name}__out");
        result.push(ScalarInfo { input_name, output_name, elem_sort, index_to_scalar });
    }
    result
}

/// Rewrite a single expression, replacing Select operations on scalarizable
/// arrays with scalar variable references.
pub(in crate::codegen_ay::chc::scalarize_arrays) fn rewrite_expr(
    expr: &Expr,
    infos: &[ScalarInfo],
    maps: &RewriteMaps,
    ctx: &mut RewriteContext,
) -> Expr {
    stacker::maybe_grow(REWRITE_STACK_RED_ZONE, REWRITE_STACK_SIZE, || match expr.value() {
        ExprValue::Select { array, index } => {
            if let ExprValue::Var { name } = array.value() {
                let scalarized = maps
                    .by_input
                    .get(name)
                    .map(|&info_idx| (info_idx, false))
                    .or_else(|| maps.by_output.get(name).map(|&info_idx| (info_idx, true)));
                if let Some((info_idx, is_output)) = scalarized {
                    let info = &infos[info_idx];
                    if let Some(const_idx) = try_extract_const_idx(index) {
                        if info.index_to_scalar.contains_key(&const_idx) {
                            let scalar_name = if is_output {
                                info.scalar_output_name(&const_idx)
                            } else {
                                info.scalar_input_name(&const_idx)
                            };
                            return Expr::var(scalar_name, info.elem_sort.clone());
                        }
                        // Constant index on an UNTRACKED lane. The only way a
                        // constant-index select survives identification without
                        // its lane being tracked is the entry-rule pointwise
                        // seed skip (`is_entry_pointwise_seed_for_array`):
                        // every other constraint mentioning the array is fed
                        // through `collect_selects_on_var`, which records all
                        // constant indices into `index_to_scalar`. A seed lane
                        // that is untracked is therefore never read or written
                        // by any transition rule — it is dead state — and the
                        // seed constraint's value side provably does not
                        // mention the array. Rewriting the select to a fresh,
                        // single-use variable turns the seed `(= (select arr
                        // #xN) val)` into the benign tautology `(= fresh val)`
                        // without weakening or strengthening any reachable
                        // observable state.
                        return ctx.dead_const_lane_var(name, &info.elem_sort);
                    }
                    // SYMBOLIC index discovered only at rewrite time:
                    // identification should have rejected this array
                    // (`collect_selects_on_var` returns Err on symbolic
                    // selects), so reaching this point means a select escaped
                    // the scan. Minting an unconstrained free var here (the
                    // historical `_select_any_N` fallback, with or without a
                    // tracked-lane ITE around it) lets the solver fabricate
                    // counterexample witnesses. FAIL CLOSED instead: record
                    // the array for rejection and leave the expression
                    // untouched. `scalarize_vc` discards this entire staged
                    // rewrite and re-identifies with the array banned, so the
                    // array survives the pass with its real constraints.
                    ctx.reject_array(&info.input_name);
                    return expr.clone();
                }
            }
            let new_array = rewrite_expr(array, infos, maps, ctx);
            let new_index = rewrite_expr(index, infos, maps, ctx);
            new_array.select(new_index)
        }
        ExprValue::Eq(lhs, rhs) => {
            let new_lhs = rewrite_expr(lhs, infos, maps, ctx);
            let new_rhs = rewrite_expr(rhs, infos, maps, ctx);
            new_lhs.eq(new_rhs)
        }
        _ => rewrite_expr_children(expr, infos, maps, ctx),
    })
}

#[cfg(test)]
mod tests;
