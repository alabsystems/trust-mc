// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Relation-state protection for scalarized lanes used after array extraction.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use ay_bindings::{Expr, ExprValue, Sort};
use trust_mc_core::chc::{ChcVc, RelationApp};

/// Carry scalarized lane inputs that are read in constraints but are not
/// relation state yet.
///
/// Final dead-variable pruning treats relation arguments as the roots of
/// liveness. If a scalarized lane is only used as a RHS after `into_array` or
/// transmute extraction, the final pass can keep the consuming equality while
/// dropping the predecessor equality that defined the lane. Carrying the lane
/// through the affected relation gives the final prune a state edge to follow.
pub(super) fn carry_rhs_scalarized_lanes(vc: &mut ChcVc) -> usize {
    let var_sorts = collect_var_sorts(vc);
    let carried_lanes = collect_carried_lanes(vc, &var_sorts);
    let mut required: BTreeMap<String, BTreeMap<String, Sort>> = BTreeMap::new();

    for rule in &vc.rules {
        let Some(body_rel) = &rule.body.relation else {
            continue;
        };
        let relation = body_rel.name.to_string();
        let mut constraint_lanes = BTreeSet::new();
        for constraint in rule.body.constraints.iter() {
            collect_input_lane_vars(constraint, &var_sorts, &mut constraint_lanes);
        }

        for lane in constraint_lanes {
            if carried_lanes
                .get(relation.as_str())
                .is_some_and(|lanes| lanes.contains(lane.as_str()))
            {
                continue;
            }
            require_lane(
                &mut required,
                &carried_lanes,
                relation.as_str(),
                lane.as_str(),
                var_sorts.get(lane.as_str()),
            );
        }
    }

    propagate_required_lanes(vc, &var_sorts, &carried_lanes, &mut required);
    retain_grounded_lanes(vc, &carried_lanes, &mut required);
    drop_constant_conflicted_lanes(vc, &mut required);

    if required.is_empty() {
        return 0;
    }

    let mut added_args = 0usize;
    for rule in &mut vc.rules {
        if let Some(body_rel) = &mut rule.body.relation {
            if let Some(lanes) = required.get(body_rel.name.as_str()) {
                added_args += append_body_lane_args(body_rel, lanes);
            }
        }

        if let Some(lanes) = required.get(rule.head.name.as_str()) {
            added_args += append_head_lane_args(&mut rule.head, &rule.body.constraints, lanes);
        }
    }

    for rel in &mut vc.relations {
        if let Some(lanes) = required.get(rel.name.as_str()) {
            rel.arg_sorts.extend(lanes.values().cloned());
        }
    }

    added_args
}

fn propagate_required_lanes(
    vc: &ChcVc,
    var_sorts: &HashMap<String, Sort>,
    carried_lanes: &HashMap<String, HashSet<String>>,
    required: &mut BTreeMap<String, BTreeMap<String, Sort>>,
) {
    loop {
        let mut changed = false;
        let snapshot = required.clone();
        for rule in &vc.rules {
            let Some(head_lanes) = snapshot.get(rule.head.name.as_str()) else {
                continue;
            };

            for lane in head_lanes.keys() {
                let output_lane = format!("{lane}__out");
                if constraints_mention_var(&rule.body.constraints, &output_lane) {
                    continue;
                }
                let Some(body_rel) = &rule.body.relation else {
                    continue;
                };
                changed |= require_lane(
                    required,
                    carried_lanes,
                    body_rel.name.as_str(),
                    lane.as_str(),
                    var_sorts.get(lane.as_str()),
                );
            }
        }

        if !changed {
            break;
        }
    }
}

/// P4-1 SOUNDNESS: refuse to carry a lane that different rules pin to
/// DIFFERENT constants.
///
/// Constant propagation strips a constant relation position and re-adds a
/// per-rule free-var equality `(= lane C)` binding the STRIPPED value — a
/// per-rule ghost, where `lane` in one rule's constraints denotes a different
/// state instance (with a different constant) than in the next rule.
/// Identity-carrying such a lane as shared relation state asserts the value
/// is invariant across the transition, conjoining `lane = C_pre` (from the
/// incoming rule) with `lane = C_post` (from the outgoing rule): an
/// infeasible premise that makes genuinely-reachable downstream blocks —
/// including refutable error edges — vacuously unreachable (observed: false
/// PROOF of a refuted assertion after an overlapping `copy`, where the
/// scalarized cross-slot shuffle const-propagates different pre/post slot
/// values). Leaving the lane un-carried keeps each rule's ghost binding
/// locally satisfiable — an over-approximation, which is sound.
///
/// Only lanes with two or more DISTINCT direct constant bindings are
/// dropped: a single constant everywhere is consistent with the identity
/// carry, and non-constant bindings are the pass's original extraction-read
/// use case.
fn drop_constant_conflicted_lanes(
    vc: &ChcVc,
    required: &mut BTreeMap<String, BTreeMap<String, Sort>>,
) {
    if required.is_empty() {
        return;
    }
    // lane name -> distinct scalar constants it is directly equated to.
    let mut lane_constants: HashMap<String, BTreeSet<String>> = HashMap::new();
    let mut record = |lane: &str, constant: &Expr| {
        lane_constants.entry(lane.to_string()).or_default().insert(format!("{constant:?}"));
    };
    for rule in &vc.rules {
        for constraint in rule.body.constraints.iter() {
            let ExprValue::Eq(lhs, rhs) = constraint.value() else {
                continue;
            };
            match (lhs.value(), rhs.value()) {
                (ExprValue::Var { name }, _) if is_scalar_constant_value(rhs) => record(name, rhs),
                (_, ExprValue::Var { name }) if is_scalar_constant_value(lhs) => record(name, lhs),
                _ => {}
            }
        }
    }
    let conflicted: HashSet<&String> =
        lane_constants.iter().filter(|(_, consts)| consts.len() > 1).map(|(k, _)| k).collect();
    if conflicted.is_empty() {
        return;
    }
    required.retain(|_, lanes| {
        lanes.retain(|lane, _| {
            let keep = !conflicted.contains(lane);
            if !keep {
                tracing::debug!(
                    lane,
                    "CHC: refusing identity lane carry — conflicting per-rule constant \
                     bindings (const-prop ghost, P4-1 fail-closed)"
                );
            }
            keep
        });
        !lanes.is_empty()
    });
}

fn is_scalar_constant_value(expr: &Expr) -> bool {
    matches!(
        expr.value(),
        ExprValue::BoolConst(_)
            | ExprValue::BitVecConst { .. }
            | ExprValue::IntConst(_)
            | ExprValue::RealConst(_)
    )
}

fn retain_grounded_lanes(
    vc: &ChcVc,
    carried_lanes: &HashMap<String, HashSet<String>>,
    required: &mut BTreeMap<String, BTreeMap<String, Sort>>,
) {
    let mut grounded = HashSet::new();
    loop {
        let mut changed = false;
        for relation in required.keys() {
            let Some(lanes) = required.get(relation) else {
                continue;
            };
            for lane in lanes.keys() {
                let key = (relation.clone(), lane.clone());
                if grounded.contains(&key) {
                    continue;
                }
                if relation_lane_is_grounded(vc, carried_lanes, required, &grounded, relation, lane)
                {
                    changed |= grounded.insert(key);
                }
            }
        }

        if !changed {
            break;
        }
    }

    required.retain(|relation, lanes| {
        lanes.retain(|lane, _| grounded.contains(&(relation.clone(), lane.clone())));
        !lanes.is_empty()
    });
}

fn relation_lane_is_grounded(
    vc: &ChcVc,
    carried_lanes: &HashMap<String, HashSet<String>>,
    required: &BTreeMap<String, BTreeMap<String, Sort>>,
    grounded: &HashSet<(String, String)>,
    relation: &str,
    lane: &str,
) -> bool {
    let mut saw_predecessor = false;
    for rule in &vc.rules {
        if rule.head.name.as_str() != relation {
            continue;
        }
        saw_predecessor = true;

        let output_lane = format!("{lane}__out");
        if constraints_mention_var(&rule.body.constraints, &output_lane) {
            continue;
        }

        let Some(body_rel) = &rule.body.relation else {
            return false;
        };
        if carried_lanes.get(body_rel.name.as_str()).is_some_and(|lanes| lanes.contains(lane)) {
            continue;
        }
        if required.get(body_rel.name.as_str()).is_some_and(|lanes| lanes.contains_key(lane))
            && grounded.contains(&(body_rel.name.to_string(), lane.to_string()))
        {
            continue;
        }

        return false;
    }

    saw_predecessor
}

fn require_lane(
    required: &mut BTreeMap<String, BTreeMap<String, Sort>>,
    carried_lanes: &HashMap<String, HashSet<String>>,
    relation: &str,
    lane: &str,
    sort: Option<&Sort>,
) -> bool {
    if carried_lanes.get(relation).is_some_and(|lanes| lanes.contains(lane)) {
        return false;
    }
    let Some(sort) = sort else {
        return false;
    };

    required
        .entry(relation.to_string())
        .or_default()
        .insert(lane.to_string(), sort.clone())
        .is_none()
}

fn collect_var_sorts(vc: &ChcVc) -> HashMap<String, Sort> {
    let mut sorts: HashMap<String, Sort> =
        vc.vars().iter().map(|var| (var.name.to_string(), var.sort.clone())).collect();

    for rule in &vc.rules {
        collect_relation_app_var_sorts(&rule.head, &mut sorts);
        if let Some(body_rel) = &rule.body.relation {
            collect_relation_app_var_sorts(body_rel, &mut sorts);
        }
        for constraint in rule.body.constraints.iter() {
            collect_expr_var_sorts(constraint, &mut sorts);
        }
    }

    sorts
}

fn collect_relation_app_var_sorts(app: &RelationApp, sorts: &mut HashMap<String, Sort>) {
    for arg in app.args.iter() {
        collect_expr_var_sorts(arg, sorts);
    }
}

fn collect_expr_var_sorts(expr: &Expr, sorts: &mut HashMap<String, Sort>) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value() {
            sorts.entry(name.to_string()).or_insert_with(|| node.sort().clone());
        }
        stack.extend(node.children());
    }
}

fn collect_carried_lanes(
    vc: &ChcVc,
    var_sorts: &HashMap<String, Sort>,
) -> HashMap<String, HashSet<String>> {
    let mut carried: HashMap<String, HashSet<String>> = HashMap::new();
    for rule in &vc.rules {
        collect_relation_app_lanes(&rule.head, var_sorts, &mut carried);
        if let Some(body_rel) = &rule.body.relation {
            collect_relation_app_lanes(body_rel, var_sorts, &mut carried);
        }
    }
    carried
}

fn collect_relation_app_lanes(
    app: &RelationApp,
    var_sorts: &HashMap<String, Sort>,
    carried: &mut HashMap<String, HashSet<String>>,
) {
    for arg in app.args.iter() {
        let ExprValue::Var { name } = arg.value() else {
            continue;
        };
        if let Some(input_lane) = normalize_lane_name(name, var_sorts) {
            carried.entry(app.name.to_string()).or_default().insert(input_lane);
        }
    }
}

fn collect_input_lane_vars(
    expr: &Expr,
    var_sorts: &HashMap<String, Sort>,
    lanes: &mut BTreeSet<String>,
) {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if let ExprValue::Var { name } = node.value() {
            if !name.ends_with("__out") && is_scalarized_lane_var(name, var_sorts) {
                lanes.insert(name.to_string());
            }
        }
        stack.extend(node.children());
    }
}

fn normalize_lane_name(name: &str, var_sorts: &HashMap<String, Sort>) -> Option<String> {
    if is_scalarized_lane_var(name, var_sorts) {
        return Some(name.to_string());
    }

    let input_name = name.strip_suffix("__out")?;
    is_scalarized_lane_var(input_name, var_sorts).then(|| input_name.to_string())
}

fn is_scalarized_lane_var(name: &str, var_sorts: &HashMap<String, Sort>) -> bool {
    name.contains("_at_0x")
        && name.contains("_bv")
        && var_sorts.get(name).is_some_and(|sort| !sort.is_array())
}

fn append_body_lane_args(app: &mut RelationApp, lanes: &BTreeMap<String, Sort>) -> usize {
    let mut args = (*app.args).clone();
    let old_len = args.len();
    for (lane, sort) in lanes {
        args.push(Expr::var(lane.clone(), sort.clone()));
    }
    app.args = Arc::new(args);
    app.args.len() - old_len
}

fn append_head_lane_args(
    app: &mut RelationApp,
    constraints: &trust_mc_core::constraints::Constraints,
    lanes: &BTreeMap<String, Sort>,
) -> usize {
    let mut args = (*app.args).clone();
    let old_len = args.len();
    for (lane, sort) in lanes {
        let output_lane = format!("{lane}__out");
        let arg_name = if constraints_mention_var(constraints, &output_lane) {
            output_lane
        } else {
            lane.clone()
        };
        args.push(Expr::var(arg_name, sort.clone()));
    }
    app.args = Arc::new(args);
    app.args.len() - old_len
}

fn constraints_mention_var(
    constraints: &trust_mc_core::constraints::Constraints,
    var_name: &str,
) -> bool {
    constraints.iter().any(|constraint| expr_mentions_var(constraint, var_name))
}

fn expr_mentions_var(expr: &Expr, var_name: &str) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        if matches!(node.value(), ExprValue::Var { name } if name == var_name) {
            return true;
        }
        stack.extend(node.children());
    }
    false
}
