// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! MIR body pattern scanners for struct Vec accessor dispatch.
//!
//! Extracted from `codegen_call_struct_vec_accessor.rs` to stay under
//! the 500-line file limit. These free functions scan callee MIR bodies
//! for Vec access patterns (Index, IndexMut, Len).
//!
//! Part of #3348: method-based Vec accessor/mutator encoding gap.

use rustc_public::CrateDef;
use rustc_public::mir::mono::Instance;
use rustc_public::mir::{
    Body, CastKind, Operand, PointerCoercion, Rvalue, StatementKind, TerminatorKind,
};
use rustc_public::ty::{RigidTy, TyKind};

use super::{StoredValue, VecAccessKind, VecAccessPattern};

pub(in crate::codegen_ay::chc) type FieldRefMap = std::collections::HashMap<usize, usize>;
pub(in crate::codegen_ay::chc) type DerefMap = std::collections::HashMap<usize, usize>;

/// Resolve callee FnDef + substs to a MIR Body.
pub(in crate::codegen_ay::chc) fn resolve_callee_body(
    fn_def: rustc_public::ty::FnDef,
    fn_substs: &rustc_public::ty::GenericArgs,
) -> Option<Body> {
    Instance::resolve(fn_def, fn_substs).ok()?.body()
}

/// Scan callee MIR for Vec Index/IndexMut, tracing field ref → deref → index
/// to associate each operation with its source struct field. Part of #3348.
pub(in crate::codegen_ay::chc) fn scan_vec_access_pattern(body: &Body) -> Option<VecAccessPattern> {
    let (field_ref_locals, deref_store_value) = scan_field_refs_and_stores(body);
    let (deref_dest_to_source, index_info, index_arg0_local) = scan_call_chain(body);
    let (is_index_mut, index_local) = index_info?;
    let vec_field_idx =
        trace_index_to_field(&field_ref_locals, &deref_dest_to_source, index_arg0_local?)?;

    if is_index_mut {
        let stored = deref_store_value?;
        Some(VecAccessPattern {
            vec_field_idx,
            kind: VecAccessKind::Write { index_local, stored_value: stored },
        })
    } else {
        Some(VecAccessPattern { vec_field_idx, kind: VecAccessKind::Read { index_local } })
    }
}

/// Scan callee MIR for `self.vec_field.len()` pattern.
///
/// Detects methods that return the length of a Vec field, like
/// `fn width(&self) -> usize { self.0.len() }`. Part of #3348.
pub(in crate::codegen_ay::chc) fn scan_vec_len_pattern(body: &Body) -> Option<VecAccessPattern> {
    let (field_ref_locals, _) = scan_field_refs_and_stores(body);

    let (deref_dest_to_source, len_arg0_local) = scan_len_call_chain(body);

    let arg0_local = len_arg0_local?;
    let vec_field_idx = trace_index_to_field(&field_ref_locals, &deref_dest_to_source, arg0_local)?;

    Some(VecAccessPattern { vec_field_idx, kind: VecAccessKind::Len })
}

/// Scan callee MIR for `&self.vec_field` / `&self.0` slice-return accessors.
///
/// Detects methods that return a slice view of a Vec field, like
/// `fn literals(&self) -> &[T] { &self.0 }`. The returned slice is typically
/// produced by a ref-to-field followed by an `Unsize` cast to `&[T]`.
pub(in crate::codegen_ay::chc) fn scan_vec_as_slice_pattern(
    body: &Body,
) -> Option<VecAccessPattern> {
    let (field_ref_locals, _) = scan_field_refs_and_stores(body);
    let mut aliases: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    let mut deref_returns: std::collections::HashMap<usize, usize> =
        std::collections::HashMap::new();

    for block in &body.blocks {
        for stmt in &block.statements {
            let StatementKind::Assign(lhs, rhs) = &stmt.kind else { continue };
            if !lhs.projection.is_empty() {
                continue;
            }
            match rhs {
                Rvalue::Use(Operand::Copy(place) | Operand::Move(place))
                    if place.projection.is_empty() =>
                {
                    aliases.insert(lhs.local, place.local);
                }
                Rvalue::Cast(
                    CastKind::PointerCoercion(PointerCoercion::Unsize),
                    Operand::Copy(place) | Operand::Move(place),
                    target_ty,
                ) if place.projection.is_empty() && is_slice_reference(target_ty) => {
                    aliases.insert(lhs.local, place.local);
                }
                _ => {}
            }
        }
        let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind else {
            continue;
        };
        let Some(name) = resolve_call_name(func, body) else { continue };
        if is_deref_call_name(&name)
            && let Some(src) = operand_bare_local(args.first())
        {
            deref_returns.insert(destination.local, src);
        }
    }

    let mut current = 0;
    let mut visited = std::collections::HashSet::new();
    while visited.insert(current) {
        if let Some(&src_local) = deref_returns.get(&current) {
            let vec_field_idx = trace_alias_to_field(&field_ref_locals, &aliases, src_local)?;
            return Some(VecAccessPattern { vec_field_idx, kind: VecAccessKind::AsSlice });
        }
        current = match aliases.get(&current) {
            Some(local) => *local,
            None => break,
        };
    }
    None
}

/// Scan callee MIR for `self.vec_field.is_empty()` pattern. Part of #3348.
pub(in crate::codegen_ay::chc) fn scan_vec_is_empty_pattern(
    body: &Body,
) -> Option<VecAccessPattern> {
    let (field_ref_locals, _) = scan_field_refs_and_stores(body);
    let (deref_dest_to_source, is_empty_arg0_local) = scan_is_empty_call_chain(body);
    let arg0_local = is_empty_arg0_local?;
    let vec_field_idx = trace_index_to_field(&field_ref_locals, &deref_dest_to_source, arg0_local)?;
    Some(VecAccessPattern { vec_field_idx, kind: VecAccessKind::IsEmpty })
}

/// Scan terminators for deref → is_empty call chain.
fn scan_is_empty_call_chain(body: &Body) -> (DerefMap, Option<usize>) {
    let mut deref_dest_to_source = DerefMap::new();
    let mut is_empty_arg0_local: Option<usize> = None;
    for block in &body.blocks {
        if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
            let Some(name) = resolve_call_name(func, body) else { continue };
            if is_deref_call_name(&name) {
                if let Some(src) = operand_bare_local(args.first()) {
                    deref_dest_to_source.insert(destination.local, src);
                }
            }
            if name == "is_empty" || name.ends_with("::is_empty") {
                is_empty_arg0_local = operand_bare_local(args.first());
            }
        }
    }
    (deref_dest_to_source, is_empty_arg0_local)
}

/// Scan terminators for deref → len call chain.
fn scan_len_call_chain(body: &Body) -> (DerefMap, Option<usize>) {
    let mut deref_dest_to_source = DerefMap::new();
    let mut len_arg0_local: Option<usize> = None;

    for block in &body.blocks {
        if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
            let Some(name) = resolve_call_name(func, body) else { continue };
            if is_deref_call_name(&name) {
                if let Some(src) = operand_bare_local(args.first()) {
                    deref_dest_to_source.insert(destination.local, src);
                }
            }
            // Match Vec::len, <[T]>::len, and other len() variants.
            // trimmed_name() may return "len" or "Vec::<T, A>::len".
            if name == "len" || name.ends_with("::len") {
                len_arg0_local = operand_bare_local(args.first());
            }
        }
    }
    (deref_dest_to_source, len_arg0_local)
}

/// Phase 1: Scan MIR statements for field references and deref stores.
fn scan_field_refs_and_stores(body: &Body) -> (FieldRefMap, Option<StoredValue>) {
    let arg_count = body.arg_locals().len();
    let mut field_ref_locals = FieldRefMap::new();
    let mut deref_store_value: Option<StoredValue> = None;
    for block in &body.blocks {
        for stmt in &block.statements {
            if let StatementKind::Assign(place, rvalue) = &stmt.kind {
                try_record_field_ref(place, rvalue, &mut field_ref_locals);
                if let Some(rustc_public::mir::ProjectionElem::Deref) = place.projection.first() {
                    if let Rvalue::Use(operand) = rvalue {
                        deref_store_value = extract_stored_value(operand, arg_count);
                    }
                }
            }
        }
    }
    (field_ref_locals, deref_store_value)
}

/// Record `_N = &(*_1).field_k` or `_N = &raw (*_1).field_k` into the map.
fn try_record_field_ref(place: &rustc_public::mir::Place, rvalue: &Rvalue, map: &mut FieldRefMap) {
    let src_place = match rvalue {
        Rvalue::Ref(_, _, p) | Rvalue::AddressOf(_, p) => p,
        _ => return,
    };
    if src_place.local != 1 || !place.projection.is_empty() {
        return;
    }
    for proj in &src_place.projection {
        if let rustc_public::mir::ProjectionElem::Field(idx, _) = proj {
            map.insert(place.local, *idx);
        }
    }
}

/// Phase 2: Scan terminators for deref/index call chain.
fn scan_call_chain(body: &Body) -> (DerefMap, Option<(bool, usize)>, Option<usize>) {
    let mut deref_dest_to_source = DerefMap::new();
    let mut index_info: Option<(bool, usize)> = None;
    let mut index_arg0_local: Option<usize> = None;

    for block in &body.blocks {
        if let TerminatorKind::Call { func, args, destination, .. } = &block.terminator.kind {
            let Some(name) = resolve_call_name(func, body) else { continue };
            if is_deref_call_name(&name) {
                if let Some(src) = operand_bare_local(args.first()) {
                    deref_dest_to_source.insert(destination.local, src);
                }
            }
            if name == "index"
                || name == "index_mut"
                || name.ends_with("::index")
                || name.ends_with("::index_mut")
            {
                index_arg0_local = operand_bare_local(args.first());
                if let Some(idx_l) = operand_bare_local(args.get(1)) {
                    index_info = Some((name.ends_with("index_mut"), idx_l));
                }
            }
        }
    }
    (deref_dest_to_source, index_info, index_arg0_local)
}

/// Phase 3: Trace index arg0 through deref chain to a field reference.
fn trace_index_to_field(fields: &FieldRefMap, derefs: &DerefMap, start: usize) -> Option<usize> {
    if let Some(&idx) = fields.get(&start) {
        return Some(idx);
    }
    let &hop1 = derefs.get(&start)?;
    if let Some(&idx) = fields.get(&hop1) {
        return Some(idx);
    }
    let &hop2 = derefs.get(&hop1)?;
    fields.get(&hop2).copied()
}

/// Trace simple Copy/Move/Unsize alias chains back to a field reference.
fn trace_alias_to_field(
    fields: &FieldRefMap,
    aliases: &std::collections::HashMap<usize, usize>,
    start: usize,
) -> Option<usize> {
    let mut current = start;
    let mut visited = std::collections::HashSet::new();
    while visited.insert(current) {
        if let Some(&idx) = fields.get(&current) {
            return Some(idx);
        }
        current = *aliases.get(&current)?;
    }
    None
}

/// Extract the trimmed callee name from a Call terminator's func operand.
fn resolve_call_name(func: &Operand, body: &Body) -> Option<String> {
    let func_ty = func.ty(body.locals()).ok()?;
    match func_ty.kind() {
        TyKind::RigidTy(RigidTy::FnDef(def, _)) => Some(def.trimmed_name()),
        _ => None,
    }
}

/// Check if a resolved call name refers to `Deref::deref` or `DerefMut::deref_mut`.
///
/// `trimmed_name()` returns trait-qualified names like `"Deref::deref"` rather
/// than bare `"deref"`. Match both forms to handle all compiler output formats.
/// Part of #3348: fixes scan_vec_as_slice_pattern not detecting the deref call.
fn is_deref_call_name(name: &str) -> bool {
    name == "deref"
        || name == "deref_mut"
        || name.ends_with("::deref")
        || name.ends_with("::deref_mut")
}

/// Extract the bare local index from an operand (no projections).
pub(in crate::codegen_ay::chc) fn operand_bare_local(op: Option<&Operand>) -> Option<usize> {
    match op? {
        Operand::Copy(p) | Operand::Move(p) if p.projection.is_empty() => Some(p.local),
        _ => None,
    }
}

fn is_slice_reference(ty: &rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) | TyKind::RigidTy(RigidTy::RawPtr(inner, _)) => {
            matches!(inner.kind(), TyKind::RigidTy(RigidTy::Slice(_)))
        }
        _ => false,
    }
}

/// Extract the stored value from an operand in a deref store.
fn extract_stored_value(operand: &Operand, arg_count: usize) -> Option<StoredValue> {
    match operand {
        Operand::Constant(const_op) => Some(StoredValue::ConstantOp(Box::new(const_op.clone()))),
        Operand::Copy(p) | Operand::Move(p) => {
            if p.projection.is_empty() && p.local >= 1 && p.local <= arg_count {
                Some(StoredValue::Parameter(p.local))
            } else {
                None
            }
        }
    }
}

/// Check if a type is `Vec` (traversing references).
pub(in crate::codegen_ay::chc) fn type_is_vec(ty: &rustc_public::ty::Ty) -> bool {
    match ty.kind() {
        TyKind::RigidTy(RigidTy::Adt(def, _)) => def.trimmed_name() == "Vec",
        TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => type_is_vec(&inner),
        _ => false,
    }
}
