// Copyright 2026 Andrew Yates, Inc.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Heap-liveness guards for CHC constant propagation.

use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue};

use crate::chc::ChcVc;

/// Returns whether the VC carries scalarized heap-liveness state.
///
/// `obj_valid_at_*` lanes encode whether an allocation object is still live.
/// They are safety-critical for stale-pointer checks and must be treated
/// conservatively by CHC optimization passes.
pub fn has_scalarized_obj_valid_liveness(vc: &ChcVc) -> bool {
    vc.vars().iter().any(|var| is_scalarized_obj_valid_name(&var.name))
        || vc.rules.iter().any(|rule| {
            rule.head.args.iter().any(expr_mentions_scalarized_obj_valid)
                || rule.body.relation.as_ref().is_some_and(|relation| {
                    relation.args.iter().any(expr_mentions_scalarized_obj_valid)
                })
                || rule.body.constraints.iter().any(expr_mentions_scalarized_obj_valid)
        })
}

/// Returns whether the VC carries a constant-address heap access whose
/// out-of-bounds `obj_size` obligation constant propagation can silently drop.
///
/// Constant-address heap cells are scalarized to per-address lanes named
/// `..._at_0x<addr>_...` (e.g. `_main_mem_i16_at_0xc000000004_bv64`) during the
/// first scalarization pass. When such a lane exists alongside the heap
/// allocation metadata (`obj_valid` / `obj_size` arrays), the access is a
/// dynamic-allocation access whose bounds check references `obj_size`.
/// Constant propagation over the scalarized form can eliminate the `obj_size`
/// bounds obligation for the out-of-bounds cell (the read collapses to a free
/// scalar), so the reduced VC no longer contains the reachable OOB error edge
/// and the straight-line discharge then proves the buggy program SAFE
/// (e.g. `expected/realloc/shrink`). Leave these VCs unreduced so the bounds
/// obligation survives to the solver. This mirrors the `obj_valid` mitigation
/// (ay#9227) for the `obj_size` bounds lane.
///
/// The hazard is an OUT-OF-BOUNDS cell. When every scalarized constant-address
/// cell (heap or region lane) provably lies inside its object — the object has
/// exactly one size in the VC, a constant, and the cell's bytes end at or before
/// it — there is no such cell and the guard stays off
/// (`scalarized_cells_provably_in_bounds`). Without that exemption the guard
/// fired on any VC whose memory happened to scalarize before constant
/// propagation, whatever the cells were: a `Box` payload written at constant
/// addresses and then coerced to `Box<dyn T>` (fix/chc-lost-writes) kept its
/// drop's nineteen memory-safety obligations over symbolic pointers, where
/// const-prop collapses them to two, and the per-property solve overran its
/// deadline into the driver watchdog. `realloc/shrink` still fires: its cells
/// run past the shrunk object's size, and that size is not a constant.
pub fn has_scalarized_obj_size_bounds(vc: &ChcVc) -> bool {
    if !vc_mentions_heap_metadata(vc) {
        return false;
    }
    if !vc.vars().iter().any(|var| is_scalarized_const_address_cell(&var.name, var.sort.is_array()))
    {
        return false;
    }
    !scalarized_cells_provably_in_bounds(vc)
}

/// A scalarized constant-address memory or region lane: the object id and byte
/// offset its name encodes (`..._at_0x<obj:32><offset:32>_bv64`) and its width
/// in bytes. `None` for a name or sort this does not read with certainty.
fn const_address_cell(name: &str, sort: &ay_bindings::Sort) -> Option<(u64, u64, u64)> {
    if sort.is_array() || !(name.contains("_mem_") || name.contains("_region_")) {
        return None;
    }
    let name = name.strip_suffix("__out").unwrap_or(name);
    let (_, rest) = name.rsplit_once("_at_0x")?;
    let hex = rest.strip_suffix("_bv64")?;
    let addr = u64::from_str_radix(hex, 16).ok()?;
    let width_bytes = if sort.is_bool() { 1 } else { u64::from(sort.bitvec_width()?).div_ceil(8) };
    Some((addr >> 32, addr & 0xffff_ffff, width_bytes))
}

/// The unsigned value of a constant expression (after constant folding).
fn const_u64(expr: &Expr) -> Option<u64> {
    let folded = crate::chc_const_prop::eval::try_eval_to_const(expr)?;
    let ExprValue::BitVecConst { value, .. } = folded.value() else { return None };
    let (sign, digits) = value.to_u64_digits();
    if sign == num_bigint::Sign::Minus {
        return None;
    }
    match digits.as_slice() {
        [] => Some(0),
        [d] => Some(*d),
        _ => None,
    }
}

/// Every size the VC gives an object, keyed by object id; `None` for an object
/// given a size that is not a constant. `Err(())` when an `obj_size` store has a
/// symbolic index, which may resize any object.
///
/// A size comes from a store into the `obj_size` array (at any depth of a store
/// chain), from the definition of a scalarized size lane
/// (`obj_size_at_0x<obj>_bv32__out = v`, identity copies aside), or from a
/// top-level fact of an entry rule (`(select obj_size c) = v`, `lane = v`).
fn object_sizes(vc: &ChcVc) -> Result<HashMap<u64, Option<HashSet<u64>>>, ()> {
    fn note(sizes: &mut HashMap<u64, Option<HashSet<u64>>>, obj: u64, size: Option<u64>) {
        let entry = sizes.entry(obj).or_insert_with(|| Some(HashSet::new()));
        match (entry.as_mut(), size) {
            (Some(set), Some(size)) => {
                set.insert(size);
            }
            _ => *entry = None,
        }
    }
    fn is_obj_size_array(expr: &Expr) -> bool {
        matches!(expr.value(), ExprValue::Var { name } if name.starts_with("obj_size"))
            && expr.sort().is_array()
    }
    fn store_chain_base(mut expr: &Expr) -> &Expr {
        while let ExprValue::Store { array, .. } = expr.value() {
            expr = array;
        }
        expr
    }
    /// The object id of a size lane (`obj_size_at_0x<obj>_bv32`, or its `__out`).
    fn lane_obj(name: &str) -> Option<u64> {
        let rest = name.strip_prefix("obj_size_at_0x")?;
        let rest = rest.strip_suffix("__out").unwrap_or(rest);
        u64::from_str_radix(rest.strip_suffix("_bv32")?, 16).ok()
    }
    fn conjuncts<'a>(expr: &'a Expr, out: &mut Vec<&'a Expr>) {
        match expr.value() {
            ExprValue::And(children) => children.iter().for_each(|c| conjuncts(c, out)),
            _ => out.push(expr),
        }
    }

    let mut sizes: HashMap<u64, Option<HashSet<u64>>> = HashMap::new();
    for rule in &vc.rules {
        if rule.body.relation.is_none() {
            let mut facts = Vec::new();
            rule.body.constraints.iter().for_each(|c| conjuncts(c, &mut facts));
            for fact in facts {
                let ExprValue::Eq(lhs, rhs) = fact.value() else { continue };
                let obj = match lhs.value() {
                    ExprValue::Select { array, index } if is_obj_size_array(array) => {
                        const_u64(index)
                    }
                    ExprValue::Var { name } if !name.ends_with("__out") => lane_obj(name),
                    _ => None,
                };
                if let Some(obj) = obj {
                    note(&mut sizes, obj, const_u64(rhs));
                }
            }
        }
        let mut stack: Vec<&Expr> = rule.body.constraints.iter().collect();
        while let Some(expr) = stack.pop() {
            match expr.value() {
                ExprValue::Store { index, value, .. } if is_obj_size_array(store_chain_base(expr)) => {
                    let Some(obj) = const_u64(index) else { return Err(()) };
                    note(&mut sizes, obj, const_u64(value));
                }
                ExprValue::Eq(lhs, rhs) => {
                    if let ExprValue::Var { name } = lhs.value()
                        && name.ends_with("__out")
                        && let Some(obj) = lane_obj(name)
                    {
                        let identity = matches!(rhs.value(), ExprValue::Var { name: r }
                            if !r.ends_with("__out") && lane_obj(r) == Some(obj));
                        if !identity {
                            note(&mut sizes, obj, const_u64(rhs));
                        }
                    }
                }
                _ => {}
            }
            stack.extend(expr.value().children());
        }
    }
    Ok(sizes)
}

/// Whether every scalarized constant-address cell of the VC lies inside its
/// object: the object has exactly one size, a constant, and the cell's bytes
/// end at or before it. Any cell this cannot read, and any object with no
/// size, a symbolic size or two sizes (a resize), answers `false`.
fn scalarized_cells_provably_in_bounds(vc: &ChcVc) -> bool {
    let Ok(sizes) = object_sizes(vc) else { return false };
    for var in vc.vars() {
        let name: &str = &var.name;
        let memory_lane = name.contains("_mem_") || name.contains("_region_");
        if var.sort.is_array() || !memory_lane || !name.contains("_at_0x") {
            continue;
        }
        let Some((obj, offset, width)) = const_address_cell(name, &var.sort) else {
            return false;
        };
        let Some(Some(obj_sizes)) = sizes.get(&obj) else { return false };
        let [size] = obj_sizes.iter().copied().collect::<Vec<_>>()[..] else { return false };
        if offset.checked_add(width).is_none_or(|end| end > size) {
            return false;
        }
    }
    true
}

/// Returns whether the VC carries an error-reachable edge guarded by the
/// pointer byte-offset-overflow check `bvsdiv(bvmul(count, size), size) == count`.
///
/// Neither the straight-line prover nor ay's PDR folds this `bvsdiv`-over-`bvmul`
/// round-trip soundly on the constant-propagated symbolic form: the prover
/// mis-evaluates the overflow edge as satisfied (pruning it) and PDR false-proves
/// it (e.g. `expected/offset-bytes-overflow`). Leave these VCs unreduced so the
/// overflow edge stays reachable for a fail-closed verdict.
///
/// Matches the precise `bvsdiv(bvmul(..), ..)` shape rather than any signed
/// division, so ordinary div-by-zero / `INT_MIN/-1` / user `a / b` checks do not
/// trip the guard.
pub fn has_signed_overflow_error_edge(vc: &ChcVc) -> bool {
    vc.rules.iter().any(|rule| {
        is_error_reachable_head(rule.head.name.as_str())
            && rule.body.constraints.iter().any(expr_has_sdiv_over_mul)
    })
}

fn is_error_reachable_head(name: &str) -> bool {
    name == "error" || name.starts_with("error_p")
}

/// Returns whether the VC's block-relation graph contains a cycle (a loop
/// back-edge). Straight-line (acyclic) VCs gain nothing from constant
/// propagation's arity reduction — there is no loop invariant for PDR to
/// converge on — so callers may safely skip const-prop for acyclic VCs when a
/// reachable obligation would otherwise be weakened, without regressing the
/// cyclic proofs that do rely on it. `error` / `error_p*` sink relations are
/// ignored (they are never loop headers).
pub fn has_block_relation_cycle(vc: &ChcVc) -> bool {
    // Build the relation-application edge set: body relation -> head relation.
    let mut edges: HashMap<&str, HashSet<&str>> = HashMap::new();
    for rule in &vc.rules {
        let head = rule.head.name.as_str();
        if is_error_reachable_head(head) {
            continue;
        }
        if let Some(body_rel) = &rule.body.relation {
            let body = body_rel.name.as_str();
            if is_error_reachable_head(body) {
                continue;
            }
            edges.entry(body).or_default().insert(head);
        }
    }

    // DFS cycle detection over the directed graph.
    let mut state: HashMap<&str, u8> = HashMap::new(); // 0=unseen,1=on-stack,2=done
    let nodes: Vec<&str> = edges.keys().copied().collect();
    for &start in &nodes {
        if state.get(start).copied().unwrap_or(0) != 0 {
            continue;
        }
        let mut stack: Vec<(&str, bool)> = vec![(start, false)];
        while let Some((node, post)) = stack.pop() {
            if post {
                state.insert(node, 2);
                continue;
            }
            // Skip nodes already on-stack (1) or finished (2).
            if state.get(node).copied().unwrap_or(0) != 0 {
                continue;
            }
            state.insert(node, 1);
            stack.push((node, true));
            if let Some(succs) = edges.get(node) {
                for &succ in succs {
                    match state.get(succ).copied().unwrap_or(0) {
                        1 => return true, // back-edge to an on-stack node
                        0 => stack.push((succ, false)),
                        _ => {}
                    }
                }
            }
        }
    }
    false
}

fn vc_mentions_heap_metadata(vc: &ChcVc) -> bool {
    vc.vars().iter().any(|var| is_heap_metadata_array(&var.name, var.sort.is_array()))
}

fn is_heap_metadata_array(name: &str, is_array: bool) -> bool {
    is_array
        && (name == "obj_valid"
            || name == "obj_size"
            || name.starts_with("obj_valid")
            || name.starts_with("obj_size"))
}

fn is_scalarized_const_address_cell(name: &str, is_array: bool) -> bool {
    !is_array && name.contains("_mem_") && name.contains("_at_0x")
}

fn expr_has_sdiv_over_mul(expr: &Expr) -> bool {
    // Match `bvsdiv(bvmul(_, _), _)` — the round-trip that the byte-offset
    // overflow check uses to detect `count * size` wrapping `isize`. Requiring
    // the `bvmul` numerator keeps the guard off ordinary signed division.
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::BvSDiv(numerator, _) = node.value() {
            if matches!(numerator.value(), ExprValue::BvMul(_, _)) {
                return true;
            }
        }
        stack.extend(node.children());
    }
    false
}

pub(super) fn heap_liveness_positions(vc: &ChcVc) -> HashMap<&str, HashSet<usize>> {
    let mut positions: HashMap<&str, HashSet<usize>> = HashMap::new();
    for rule in &vc.rules {
        mark_heap_liveness_args(rule.head.name.as_str(), &rule.head.args, &mut positions);
        if let Some(body_rel) = &rule.body.relation {
            mark_heap_liveness_args(body_rel.name.as_str(), &body_rel.args, &mut positions);
        }
    }
    positions
}

fn mark_heap_liveness_args<'a>(
    relation: &'a str,
    args: &'a [Expr],
    positions: &mut HashMap<&'a str, HashSet<usize>>,
) {
    for (idx, arg) in args.iter().enumerate() {
        if expr_mentions_scalarized_obj_valid(arg) {
            positions.entry(relation).or_default().insert(idx);
        }
    }
}

fn expr_mentions_scalarized_obj_valid(expr: &Expr) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Var { name } if is_scalarized_obj_valid_name(name) => return true,
            _ => stack.extend(node.children()),
        }
    }
    false
}

fn is_scalarized_obj_valid_name(name: &str) -> bool {
    name.starts_with("obj_valid_at_")
}
