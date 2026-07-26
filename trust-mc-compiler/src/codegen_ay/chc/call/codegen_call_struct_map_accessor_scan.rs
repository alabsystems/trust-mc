// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR pattern scanning for struct-embedded BTreeMap accessors and mutators.

use std::collections::{HashMap, HashSet};

use rustc_public::CrateDef;
use rustc_public::mir::{Body, Operand, Rvalue, StatementKind, TerminatorKind};
use rustc_public::ty::{RigidTy, TyKind};

/// Detected BTreeMap access pattern from MIR body scan.
pub(in crate::codegen_ay::chc) struct MapAccessPattern {
    /// Which struct field is the BTreeMap (index in ADT variant fields).
    pub(in crate::codegen_ay::chc) map_field_idx: usize,
    /// Callee local that holds the key argument.
    pub(in crate::codegen_ay::chc) key_local: usize,
    /// Source of the unwrap_or default value.
    pub(in crate::codegen_ay::chc) default_source: DefaultSource,
}

/// Detected BTreeMap store pattern from MIR body scan.
pub(in crate::codegen_ay::chc) struct MapStorePattern {
    /// Which struct field is the BTreeMap (index in ADT variant fields).
    pub(in crate::codegen_ay::chc) map_field_idx: usize,
    /// Callee local that holds the key argument.
    pub(in crate::codegen_ay::chc) key_local: usize,
    /// Callee local that holds the stored value argument.
    pub(in crate::codegen_ay::chc) value_local: usize,
}

/// Source of the unwrap_or default value.
pub(in crate::codegen_ay::chc) enum DefaultSource {
    /// A field of `self` (callee local 1), by field index.
    StructField(usize),
    /// A method parameter (callee local index, where 1=self, 2=first param, etc.).
    Parameter(usize),
}

/// Scan a callee's MIR body for a BTreeMap get + unwrap_or pattern.
pub(in crate::codegen_ay::chc) fn scan_map_get_pattern(body: &Body) -> Option<MapAccessPattern> {
    let arg_count = body.arg_locals().len();
    let (map_field_idx, default_source) = scan_map_statement_patterns(body)?;
    let (has_get, key_local, param_default) = scan_map_call_patterns(body, arg_count);
    if !has_get {
        return None;
    }

    let key_local = resolve_key_through_refs(body, key_local?, arg_count)?;
    let default_source =
        param_default.or(default_source).or_else(|| scan_default_from_field_access(body))?;
    Some(MapAccessPattern { map_field_idx, key_local, default_source })
}

/// Scan a callee's MIR body for:
/// `let mut result = self.clone(); result.map.insert(key, value); result`.
pub(in crate::codegen_ay::chc) fn scan_map_store_pattern(body: &Body) -> Option<MapStorePattern> {
    let arg_count = body.arg_locals().len();
    let mut refs_to_self: HashSet<usize> = HashSet::new();
    let mut field_refs: HashMap<usize, (usize, usize)> = HashMap::new();
    let mut returned_locals: HashSet<usize> = HashSet::from([0]);

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(dest, rvalue) = &stmt.kind else { continue };
            match rvalue {
                Rvalue::Ref(_, _, src) if dest.projection.is_empty() => {
                    if src.local == 1 && src.projection.is_empty() {
                        refs_to_self.insert(dest.local);
                    }
                    if let Some(field_idx) = first_field_projection(src) {
                        field_refs.insert(dest.local, (src.local, field_idx));
                    }
                }
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if dest.local == 0
                        && dest.projection.is_empty()
                        && src.projection.is_empty() =>
                {
                    returned_locals.insert(src.local);
                }
                _ => {}
            }
        }
    }

    let mut cloned_from_self: HashSet<usize> = HashSet::new();
    let mut insert_pattern: Option<(usize, usize, usize, usize)> = None;

    for block in &body.blocks {
        let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
            continue;
        };
        let Some(name) = call_trimmed_name(body, func) else { continue };
        match name.as_str() {
            "clone" | "Clone::clone" => {
                if call_arg_is_self(args.first(), &refs_to_self) {
                    cloned_from_self.insert(destination.local);
                }
            }
            "insert" => {
                let recv_local = extract_plain_local(args.first())?;
                let (base_local, field_idx) = *field_refs.get(&recv_local)?;
                let key_local =
                    resolve_key_through_refs(body, extract_plain_local(args.get(1))?, arg_count)?;
                let value_local =
                    resolve_key_through_refs(body, extract_plain_local(args.get(2))?, arg_count)?;
                insert_pattern = Some((base_local, field_idx, key_local, value_local));
            }
            _ => {}
        }
    }

    let (result_local, map_field_idx, key_local, value_local) = insert_pattern?;
    let cloned_result = cloned_from_self.contains(&result_local)
        || (result_local == 0 && !cloned_from_self.is_empty());
    if !cloned_result || !returned_locals.contains(&result_local) {
        return None;
    }

    Some(MapStorePattern { map_field_idx, key_local, value_local })
}

fn scan_map_statement_patterns(body: &Body) -> Option<(usize, Option<DefaultSource>)> {
    let mut map_field_idx = None;
    let mut default_source = None;

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(_place, rvalue) = &stmt.kind else { continue };
            if let Rvalue::Ref(_, _, src_place) = rvalue {
                map_field_idx = map_field_idx.or_else(|| scan_self_field_ref(src_place));
            }
            if let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue {
                default_source =
                    default_source.or_else(|| scan_self_field_default(src, map_field_idx));
            }
        }
    }

    Some((map_field_idx?, default_source))
}

fn scan_self_field_ref(place: &rustc_public::mir::Place) -> Option<usize> {
    if place.local != 1 {
        return None;
    }
    place.projection.iter().find_map(|proj| match proj {
        rustc_public::mir::ProjectionElem::Field(idx, _) => Some(*idx),
        _ => None,
    })
}

fn first_field_projection(place: &rustc_public::mir::Place) -> Option<usize> {
    place.projection.iter().find_map(|proj| match proj {
        rustc_public::mir::ProjectionElem::Field(idx, _) => Some(*idx),
        _ => None,
    })
}

fn call_trimmed_name(body: &Body, func: &Operand) -> Option<String> {
    func.ty(body.locals()).ok().and_then(|ty| match ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def.trimmed_name()),
        _ => None,
    })
}

fn call_arg_is_self(operand: Option<&Operand>, refs_to_self: &HashSet<usize>) -> bool {
    extract_plain_local(operand).is_some_and(|local| local == 1 || refs_to_self.contains(&local))
}

fn scan_self_field_default(
    place: &rustc_public::mir::Place,
    map_field_idx: Option<usize>,
) -> Option<DefaultSource> {
    if place.local != 1 {
        return None;
    }
    place.projection.iter().find_map(|proj| match proj {
        rustc_public::mir::ProjectionElem::Field(idx, _) if Some(*idx) != map_field_idx => {
            Some(DefaultSource::StructField(*idx))
        }
        _ => None,
    })
}

fn scan_map_call_patterns(
    body: &Body,
    arg_count: usize,
) -> (bool, Option<usize>, Option<DefaultSource>) {
    let mut has_get = false;
    let mut key_local = None;
    let mut default_source = None;

    for block in &body.blocks {
        let TerminatorKind::Call { func, args, .. } = &block.terminator.kind else { continue };
        let Some(fn_def) = func.ty(body.locals()).ok().and_then(|ty| match ty.kind() {
            TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def),
            _ => None,
        }) else {
            continue;
        };

        match fn_def.trimmed_name().as_str() {
            "get" => {
                has_get = true;
                key_local = extract_plain_local(args.get(1));
            }
            "unwrap_or" | "unwrap_or_default" => {
                default_source = default_source.or_else(|| {
                    extract_plain_local(args.get(1)).and_then(|local| {
                        (local >= 2 && local <= arg_count)
                            .then_some(DefaultSource::Parameter(local))
                    })
                });
            }
            _ => {}
        }
    }

    (has_get, key_local, default_source)
}

fn extract_plain_local(operand: Option<&Operand>) -> Option<usize> {
    match operand? {
        Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
            Some(place.local)
        }
        _ => None,
    }
}

fn resolve_key_through_refs(body: &Body, mut local: usize, arg_count: usize) -> Option<usize> {
    if (1..=arg_count).contains(&local) {
        return Some(local);
    }

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(place, rvalue) = &stmt.kind else { continue };
            if place.local != local || !place.projection.is_empty() {
                continue;
            }
            let next_local = match rvalue {
                Rvalue::Ref(_, _, src) if src.projection.is_empty() => Some(src.local),
                Rvalue::Use(Operand::Copy(src) | Operand::Move(src))
                    if src.projection.is_empty() =>
                {
                    Some(src.local)
                }
                _ => None,
            }?;
            if (1..=arg_count).contains(&next_local) {
                return Some(next_local);
            }
            local = next_local;
        }
    }
    None
}

fn scan_default_from_field_access(body: &Body) -> Option<DefaultSource> {
    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(_place, rvalue) = &stmt.kind else { continue };
            let Rvalue::Use(Operand::Copy(src) | Operand::Move(src)) = rvalue else { continue };
            if src.local != 1 {
                continue;
            }
            for proj in &src.projection {
                if let rustc_public::mir::ProjectionElem::Field(idx, _) = proj {
                    return Some(DefaultSource::StructField(*idx));
                }
            }
        }
    }
    None
}
