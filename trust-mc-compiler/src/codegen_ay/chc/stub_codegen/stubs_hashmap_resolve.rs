// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! HashMap/BTreeMap data and presence resolution helpers.
//!
//! Extracted from `stubs_hashmap_translate.rs` — Part of #4206.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::{
    mir::Operand,
    ty::{RigidTy, TyKind},
};
use tracing::debug;

use super::codegen_types::CodegenTypes;
use super::types::{bool_sort, int_sort};
use super::{
    ChcCtx, UnknownProjectionPolicy, chc_fresh_name, codegen_decl_flatten,
    collect_field_projections, declare_pending_var, record_type_sort_fallback,
};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Resolve the data array for a HashMap operand.
    ///
    /// Part of #3057: Returns `Array(K, V)` — the data array without Option wrapping.
    pub(in crate::codegen_ay::chc) fn get_hashmap_arg(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Use shared collection arg resolution (ref_targets + state_vars).
        if let Some(expr) = self.get_collection_arg(operand, modified_locals)
            && expr.sort().is_array()
        {
            return Some(expr);
        }

        // Part of #3348: Struct-embedded HashMap/BTreeMap resolution.
        // When ref_targets resolves to a struct local with field projections
        // pointing to a collection field, navigate the struct's Datatype to
        // extract the Array sub-expression.
        if let Some(expr) = self.get_struct_embedded_hashmap_data(operand, modified_locals)
            && expr.sort().is_array()
        {
            return Some(expr);
        }

        // Additional: resolve tracked reference projections for HashMap locals.
        if let Some(expr) = self.resolve_ref_operand(operand, modified_locals)
            && expr.sort().is_array()
        {
            return Some(expr);
        }

        // Create fresh symbolic array for arguments we can't resolve.
        debug!(?operand, "CHC: HashMap data arg fallback to symbolic array");

        let (key_sort, val_sort) = if let Ok(ty) = operand.ty(self.body.locals()) {
            let inner_ty = match ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
                _ => ty,
            };
            Self::extract_hashmap_sorts(inner_ty).unwrap_or_else(|| {
                record_type_sort_fallback("HashMap symbolic array key+value sorts");
                (int_sort(), int_sort())
            })
        } else {
            record_type_sort_fallback("HashMap symbolic array (no operand type)");
            (int_sort(), int_sort())
        };

        // Part of #3447: Record that HashMap data array is fully unconstrained
        // (argument resolution failed — entire data array is symbolic).
        self.record_sound_fallback_reason("hashmap_data_symbolic_fallback");
        let sym_name = chc_fresh_name("hashmap_data");
        let sym_sort = Sort::array(key_sort, val_sort);
        Some(declare_pending_var(sym_name, sym_sort))
    }

    /// Resolve the data array for a struct-embedded HashMap/BTreeMap.
    ///
    /// Part of #3348: When an operand resolves through ref_targets to a struct
    /// local with field projections (e.g., `_tmp -> RefTarget { local: _result,
    /// projections: [Field(0, BTreeMap)] }`), navigates the struct's state var
    /// through field projections to extract the Array(K, V) sub-expression.
    ///
    /// Supports two sub-cases:
    ///   - Datatype struct: navigate Datatype selectors via `apply_field_selections`
    ///   - Flattened struct: compute flat leaf offset to the Array state var
    fn get_struct_embedded_hashmap_data(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        let ref_local = place.local;
        let rt = self.ref_resolution.ref_targets.get(&ref_local)?;
        if rt.projections.is_empty() {
            return None;
        }
        let struct_local = rt.local;
        let field_projs = collect_field_projections(&rt.projections, UnknownProjectionPolicy::Skip);
        if field_projs.is_empty() {
            return None;
        }

        let struct_state_idx = self.try_state_idx_for_local(struct_local)?;

        // Check if the struct was modified in this block — use output var if so.
        let (var_name, var_sort) = if modified_locals.contains(&struct_local) {
            self.state_var_mgr.output_state_vars.get(struct_state_idx)?.clone()
        } else {
            self.state_var_mgr.state_vars.get(struct_state_idx)?.clone()
        };
        let struct_var = Expr::var(&*var_name, var_sort.clone());

        // Datatype struct: navigate selectors to collection field.
        if var_sort.datatype_name().is_some() {
            let field_expr = Self::apply_field_selections(struct_var, &field_projs)?;
            if field_expr.sort().is_array() {
                debug!(
                    struct_local,
                    ref_local,
                    "CHC: struct-embedded HashMap data resolved via Datatype selectors (#3348)"
                );
                return Some(field_expr);
            }
            return None;
        }

        // Flattened struct: compute flat leaf offset to the Array.
        let local_ty = self.body.locals().get(struct_local).map(|l| l.ty)?;
        let struct_sort = Self::translate_ty(local_ty)?;
        let dt = struct_sort.datatype_sort()?;
        let cons = dt.constructors.first()?;
        if field_projs.len() != 1 {
            return None;
        }
        let target_field_idx = field_projs[0].field_idx;
        if target_field_idx >= cons.fields.len() {
            return None;
        }

        // Sum leaf counts for all preceding fields to get the flat offset.
        let mut flat_offset = 0;
        for f in &cons.fields[..target_field_idx] {
            flat_offset += codegen_decl_flatten::collect_leaf_sorts(&f.sort, 0).len();
        }

        // The HashMap/BTreeMap field translates to a single Array leaf.
        let target_sort = &cons.fields[target_field_idx].sort;
        if !target_sort.is_array() {
            return None;
        }

        let data = self.flattened_local_field_expr(struct_local, flat_offset, modified_locals)?;
        if data.sort().is_array() {
            debug!(
                struct_local,
                ref_local,
                flat_offset,
                "CHC: struct-embedded HashMap data resolved via flattened offset (#3348)"
            );
            Some(data)
        } else {
            None
        }
    }

    /// Resolve the presence array for a HashMap operand.
    ///
    /// Part of #3057: Returns `Array(K, Bool)` from the auxiliary present state var.
    pub(in crate::codegen_ay::chc) fn get_hashmap_present_arg(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let local_idx = self.extract_local_index(operand)?;
        let resolved_idx =
            self.ref_resolution.ref_targets.get(&local_idx).map_or(local_idx, |rt| rt.local);

        let present_var_name = self
            .collections
            .len_state
            .get_present_var(resolved_idx)
            .or_else(|| self.collections.len_state.get_present_var(local_idx))
            .cloned();

        // Part of #3348 Direction 3: Consult the explicit embedded-map aux bridge
        // before falling back to MIR aggregate scanning. This resolves the present
        // var for struct-embedded maps created via constructor methods (where the
        // aggregate is in the callee body, not the caller body).
        let present_var_name = present_var_name.or_else(|| {
            self.resolve_embedded_map_present_from_bridge(operand, local_idx, resolved_idx)
        });

        // Legacy fallback: struct-embedded BTreeMap present array via MIR aggregate scan.
        // Works for struct literals built in the caller body. Kept as a compatibility
        // fallback until the explicit bridge covers all constructor patterns.
        let present_var_name =
            present_var_name.or_else(|| self.get_struct_embedded_hashmap_present_var(operand));

        let present_var_name = present_var_name?;

        // Use input variable (same rationale as collection_current_len).
        let present_sort = self
            .state_var_index_by_name(&present_var_name)
            .and_then(|idx| self.state_var_mgr.state_vars.get(idx))
            .map(|(_, sort)| sort.clone())
            .unwrap_or_else(|| Sort::array(int_sort(), bool_sort()));

        // Check if modified in this block.
        if modified_locals.contains(&resolved_idx)
            && self.collections.len_state.modified_present_vars.contains(&*present_var_name)
        {
            let out_name = crate::codegen_ay::names::out_name(&present_var_name);
            return Some(Expr::var(&out_name, present_sort));
        }

        Some(Expr::var(&*present_var_name, present_sort))
    }

    /// Part of #3348 Direction 3: Resolve present var from the explicit embedded-map
    /// aux bridge.
    ///
    /// Checks whether the operand resolves to a struct field with registered
    /// embedded-map aux state. This works for maps created via constructor methods
    /// (where the aggregate is in the callee body, not the caller body).
    fn resolve_embedded_map_present_from_bridge(
        &self,
        operand: &Operand,
        _local_idx: usize,
        resolved_idx: usize,
    ) -> Option<std::sync::Arc<str>> {
        // First: check if the resolved_idx itself has embedded aux registered
        // (e.g., the struct local was populated by a constructor dispatcher).
        // Try all field indices for this struct local.
        for (key, state) in &self.collections.embedded_map_aux {
            if key.struct_local == resolved_idx {
                if let Some(ref pvar) = state.present_var {
                    debug!(
                        struct_local = resolved_idx,
                        field_idx = key.field_idx,
                        %pvar,
                        "CHC: embedded map present resolved via bridge (#3348)"
                    );
                    return Some(pvar.clone());
                }
            }
        }

        // Second: check via ref_targets projection to find (struct_local, field_idx).
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        let rt = self.ref_resolution.ref_targets.get(&place.local)?;
        if rt.projections.is_empty() {
            return None;
        }
        let struct_local = rt.local;
        let field_projs = collect_field_projections(&rt.projections, UnknownProjectionPolicy::Skip);
        if field_projs.len() != 1 {
            return None;
        }
        let field_idx = field_projs[0].field_idx;

        let state = self.collections.get_embedded_map_aux(struct_local, field_idx)?;
        let pvar = state.present_var.as_ref()?;
        debug!(
            struct_local,
            field_idx,
            %pvar,
            "CHC: embedded map present resolved via bridge+projection (#3348)"
        );
        Some(pvar.clone())
    }

    /// Part of #3348: Find the present var for a struct-embedded BTreeMap/HashMap.
    ///
    /// When `&self.stores` resolves through ref_targets to `RefTarget { local: struct_local,
    /// projections: [Field(N, BTreeMap)] }`, walks MIR Aggregate statements to find the
    /// BTreeMap local that was assigned to field N, then returns its present var.
    fn get_struct_embedded_hashmap_present_var(
        &self,
        operand: &Operand,
    ) -> Option<std::sync::Arc<str>> {
        let (Operand::Copy(place) | Operand::Move(place)) = operand else {
            return None;
        };
        let ref_local = place.local;
        let rt = self.ref_resolution.ref_targets.get(&ref_local)?;
        if rt.projections.is_empty() {
            return None;
        }
        let struct_local = rt.local;
        let field_projs = collect_field_projections(&rt.projections, UnknownProjectionPolicy::Skip);
        if field_projs.len() != 1 {
            return None;
        }
        let target_field_idx = field_projs[0].field_idx;

        // Walk MIR to find Aggregate statements that build this struct local.
        // The operand at the target field index is the BTreeMap source local.
        for block in &self.body.blocks {
            for stmt in &block.statements {
                let rustc_public::mir::StatementKind::Assign(dest_place, rvalue) = &stmt.kind
                else {
                    continue;
                };
                if dest_place.local != struct_local || !dest_place.projection.is_empty() {
                    continue;
                }
                let rustc_public::mir::Rvalue::Aggregate(
                    rustc_public::mir::AggregateKind::Adt(_, _, _, _, _),
                    operands,
                ) = rvalue
                else {
                    continue;
                };
                if let Some(field_op) = operands.get(target_field_idx) {
                    let src_local = match field_op {
                        Operand::Copy(p) | Operand::Move(p) => p.local,
                        _ => continue,
                    };
                    if let Some(pvar) = self.collections.len_state.get_present_var(src_local) {
                        debug!(
                            struct_local,
                            ref_local,
                            src_local,
                            target_field_idx,
                            %pvar,
                            "CHC: struct-embedded HashMap present resolved via Aggregate (#3348)"
                        );
                        return Some(pvar.clone());
                    }
                }
            }
        }
        None
    }

    /// Translates a HashMap key operand, resolving references when tracked.
    pub(in crate::codegen_ay::chc) fn translate_hashmap_key(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        if let Ok(ty) = operand.ty(self.body.locals())
            && matches!(ty.kind(), TyKind::RigidTy(RigidTy::Ref(..)))
            && let Some(expr) = self.resolve_ref_operand(operand, modified_locals)
        {
            return Some(expr);
        }
        if let Some(expr) = self.translate_operand_with_modified(operand, modified_locals) {
            return Some(expr);
        }
        self.resolve_ref_operand(operand, modified_locals)
    }
    // extract_hashmap_sorts moved to stubs_hashmap_sorts.rs per #3199.
}
