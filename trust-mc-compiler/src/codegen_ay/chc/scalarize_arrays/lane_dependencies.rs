// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Required-lane propagation for scalarizer array copy chains.

use std::collections::{HashMap, HashSet};

use ay_bindings::{Expr, ExprValue, Sort};

use super::{ConstIdx, decompose_store_chain};

pub(super) enum LaneDependency {
    Copy { dst: String, base: String },
    StoreBase { dst: String, base: String, overwritten: HashSet<ConstIdx> },
}

pub(super) fn is_supported_array_base(base: &str, input_vars: &HashMap<String, Sort>) -> bool {
    base == "__const_array__" || canonical_input_name(base, input_vars).is_some()
}

pub(super) fn output_var_usage_supported(expr: &Expr, target: &str) -> bool {
    let mut stack = vec![expr];
    while let Some(node) = stack.pop() {
        match node.value() {
            ExprValue::Store { .. } => {
                if let Some((base, _)) = decompose_store_chain(node) {
                    if base == target {
                        continue;
                    }
                }
                stack.extend(node.children());
            }
            ExprValue::Select { array, index } => {
                if !matches!(array.value(), ExprValue::Var { name } if name == target) {
                    stack.push(array);
                }
                stack.push(index);
            }
            ExprValue::Var { name } if name == target => return false,
            _ => stack.extend(node.children()),
        }
    }
    true
}

pub(super) fn propagate_required_lanes(
    var_indices: &mut HashMap<String, HashSet<ConstIdx>>,
    non_scalarizable: &mut HashSet<String>,
    dependencies: &[LaneDependency],
    input_vars: &HashMap<String, Sort>,
    max_lanes: usize,
) {
    let mut changed = true;
    while changed {
        changed = false;
        for dep in dependencies {
            let (dst, base, required) = required_indices_for_dependency(dep, var_indices);
            if base == "__const_array__" || required.is_empty() {
                if let LaneDependency::Copy { dst, base } = dep {
                    changed |= propagate_copy_base_indices_to_dst(
                        dst,
                        base,
                        var_indices,
                        non_scalarizable,
                        input_vars,
                        max_lanes,
                    );
                }
                continue;
            }

            let Some(base_input) = canonical_input_name(&base, input_vars).map(str::to_string)
            else {
                changed |= mark_non_scalarizable(&dst, var_indices, non_scalarizable);
                continue;
            };
            if non_scalarizable.contains(base_input.as_str()) {
                changed |= mark_non_scalarizable(&dst, var_indices, non_scalarizable);
                continue;
            }

            let Some(base_indices) = var_indices.get_mut(base_input.as_str()) else {
                continue;
            };
            for idx in required {
                changed |= base_indices.insert(idx);
            }
            if base_indices.len() > max_lanes {
                changed |= mark_non_scalarizable(&base_input, var_indices, non_scalarizable);
            }

            if let LaneDependency::Copy { dst, base } = dep {
                changed |= propagate_copy_base_indices_to_dst(
                    dst,
                    base,
                    var_indices,
                    non_scalarizable,
                    input_vars,
                    max_lanes,
                );
            }
        }
    }
}

fn propagate_copy_base_indices_to_dst(
    dst: &str,
    base: &str,
    var_indices: &mut HashMap<String, HashSet<ConstIdx>>,
    non_scalarizable: &mut HashSet<String>,
    input_vars: &HashMap<String, Sort>,
    max_lanes: usize,
) -> bool {
    if non_scalarizable.contains(dst) {
        return false;
    }

    let Some(base_input) = canonical_input_name(base, input_vars).map(str::to_string) else {
        return mark_non_scalarizable(dst, var_indices, non_scalarizable);
    };
    if non_scalarizable.contains(base_input.as_str()) {
        return mark_non_scalarizable(dst, var_indices, non_scalarizable);
    }

    let Some(base_indices) = var_indices.get(base_input.as_str()).cloned() else {
        return false;
    };
    if base_indices.is_empty() {
        return false;
    }

    let Some(dst_indices) = var_indices.get_mut(dst) else {
        return false;
    };
    let mut changed = false;
    for idx in base_indices {
        changed |= dst_indices.insert(idx);
    }
    if dst_indices.len() > max_lanes {
        changed |= mark_non_scalarizable(dst, var_indices, non_scalarizable);
    }
    changed
}

fn required_indices_for_dependency(
    dep: &LaneDependency,
    var_indices: &HashMap<String, HashSet<ConstIdx>>,
) -> (String, String, Vec<ConstIdx>) {
    match dep {
        LaneDependency::Copy { dst, base } => {
            let required = var_indices
                .get(dst)
                .map(|indices| indices.iter().cloned().collect())
                .unwrap_or_default();
            (dst.clone(), base.clone(), required)
        }
        LaneDependency::StoreBase { dst, base, overwritten } => {
            let required = var_indices
                .get(dst)
                .map(|indices| {
                    indices.iter().filter(|idx| !overwritten.contains(*idx)).cloned().collect()
                })
                .unwrap_or_default();
            (dst.clone(), base.clone(), required)
        }
    }
}

fn canonical_input_name<'a>(
    var_name: &'a str,
    input_vars: &'a HashMap<String, Sort>,
) -> Option<&'a str> {
    if input_vars.contains_key(var_name) {
        return Some(var_name);
    }
    let input_name = var_name.strip_suffix("__out")?;
    input_vars.contains_key(input_name).then_some(input_name)
}

fn mark_non_scalarizable(
    name: &str,
    var_indices: &mut HashMap<String, HashSet<ConstIdx>>,
    non_scalarizable: &mut HashSet<String>,
) -> bool {
    var_indices.remove(name);
    non_scalarizable.insert(name.to_string())
}
