// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! CHC collection predicate stubs and helpers.
//! Converted from include!() to proper module per #2595.
//!
//! Extracted from stubs_util.rs per #2220 decomposition.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::{Operand, ProjectionElem};
use tracing::{debug, error, warn};

use crate::codegen_ay::chc::call::codegen_call_misc::CallMisc;

use super::codegen_ctx::diagnostics::CellCounter;
use super::names::{self, struct_sort};
use super::stubs::StubKind;
use super::types::{POINTER_WIDTH, bool_sort, ptr_sort};
use super::{ChcCtx, CollectionCallResult, chc_fresh_name, declare_pending_var};

/// Parts returned by the collection-specific element extraction closure
/// in [`ChcCtx::translate_iter_next_skeleton`].
pub(in crate::codegen_ay::chc) struct IterNextParts {
    /// The raw element value (not wrapped in Option).
    /// Part of #3057: consumers use result_is_some for DT-free Option flattening.
    pub(in crate::codegen_ay::chc) element: Expr,
    /// Individual element fields for composite results (Part of #3057).
    /// For HashMap iterator next(): [key, value] — avoids constructing
    /// intermediate tuple Datatype that triggers ay#1766 (DT+BV).
    /// When present, flowed through to `CollectionCallResult.result_fields`.
    pub(in crate::codegen_ay::chc) element_fields: Option<Vec<Expr>>,
    /// The collection length expression.
    /// HashMap/HashSet: `iter.fld_len`. Vec: `vec.fld_len` (nested).
    pub(in crate::codegen_ay::chc) len: Expr,
    /// Iterator fields before the `fld_pos` slot (e.g., `[map, keys]` or `[vec]`).
    pub(in crate::codegen_ay::chc) fields_before_pos: Vec<Expr>,
    /// Iterator fields after the `fld_pos` slot (e.g., `[len]` or `[]`).
    pub(in crate::codegen_ay::chc) fields_after_pos: Vec<Expr>,
    /// Raw membership or soundness constraints (empty for Vec).
    /// The skeleton wraps each in `ITE(in_bounds, constraint, true)`.
    pub(in crate::codegen_ay::chc) constraints: Vec<Expr>,
}

/// Descriptor for constructing a collection iterator datatype expression.
///
/// Part of #2304 (FE4): shared into-iter constructor wiring for Vec/HashMap/HashSet.
pub(in crate::codegen_ay::chc) struct IterConstructConfig<'a> {
    /// Concrete iterator sort name (for example `VecIntoIter_bv32`).
    pub(in crate::codegen_ay::chc) iter_sort_name: &'a str,
    /// Datatype field layout for the iterator sort.
    pub(in crate::codegen_ay::chc) iter_fields: Vec<(&'static str, Sort)>,
    /// Constructor arguments in field order.
    pub(in crate::codegen_ay::chc) ctor_fields: Vec<Expr>,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translate collection Bool-predicate calls to SMT expressions.
    ///
    /// Phase 1 (is_empty): checks tracked collection length == 0.
    /// Phase 2 (contains/starts_with/ends_with/is_ascii): deterministic symbolic Bool.
    ///   This removes silent fallthrough for supported methods without requiring
    ///   full content semantics. Sound over-approximation — admits more behaviors.
    /// Part of #2125: CHC bool-method stub parity gap.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn translate_collection_predicate_call(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        let self_arg = args.first()?;

        if matches!(stub, StubKind::VecIsEmpty | StubKind::StringIsEmpty) {
            // Use tracked length if available, otherwise a conservative constant.
            if let Some((_, len_expr)) = self.get_collection_len_var(self_arg, modified_locals) {
                let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
                return Some(len_expr.eq(zero));
            }

            warn!(?stub, "collection is_empty: no tracked length, using sound fallback");
            // Return None so the caller leaves the predicate unconstrained
            // via record_sound_fallback(). A concrete `true` would only explore
            // the empty branch — an under-approximation.
            return None;
        }

        // Phase 2a: VecEq — element-wise forall comparison using fld_data arrays.
        // Part of #3348: replaces unconstrained symbolic Bool with precise constraint.
        if matches!(stub, StubKind::VecEq) {
            if let Some(eq_expr) = self.translate_vec_eq_elementwise(args, modified_locals) {
                debug!("VecEq -> element-wise forall constraint");
                return Some(eq_expr);
            }
            // Fall through to unconstrained symbolic Bool if extraction fails.
            debug!("VecEq -> element-wise failed, falling back to symbolic Bool");
        }

        // Phase 2b: content-based predicates — deterministic symbolic Bool
        // These methods depend on element/character content that is not tracked
        // in the current collection model (Vec = ptr+len+cap, String = ptr+len+cap).
        // Explicit symbolic assignment is sound and removes silent fallthrough.
        let prefix = match stub {
            StubKind::VecContains => "vec_contains",
            StubKind::VecEq => "vec_eq",
            StubKind::StringContains => "str_contains",
            StubKind::StringStartsWith => "str_starts_with",
            StubKind::StringEndsWith => "str_ends_with",
            StubKind::StringIsAscii => "str_is_ascii",
            _ => return None, // partial dispatch: StubKind
        };
        debug!("collection predicate {:?} -> symbolic Bool (no content model)", stub);
        // Part of #3447: no content model — result is fully unconstrained Bool.
        self.record_aggregate_gap("collection_predicate_no_content_model");
        let sym_name = chc_fresh_name(prefix);
        Some(declare_pending_var(sym_name, bool_sort()))
    }

    /// Translate VecEq to element-wise forall comparison.
    ///
    /// Returns `(len_a == len_b) && forall i: (i <u len_a) => select(data_a, i) == select(data_b, i)`.
    /// Falls back to None if either Vec argument can't be resolved to a Datatype with fld_data.
    ///
    /// Part of #3348: element-wise Vec equality for bv_bitblast proofs.
    ///
    /// Argument resolution uses a 3-tier cascade:
    /// 1. `resolve_ref_or_const_referent` — handles `&Vec<T>` references from PartialEq::eq
    /// 2. `get_collection_arg` — handles projected/flattened collection locals
    /// 3. `translate_operand_with_modified` — general operand translation
    fn translate_vec_eq_elementwise(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        use super::names::vec_layout::{FLD_DATA, FLD_LEN};
        use super::types::CtorFieldExt;

        let lhs_arg = args.first()?;
        let rhs_arg = args.get(1)?;

        let lhs = self.resolve_vec_eq_operand(lhs_arg, modified_locals)?;
        let rhs = self.resolve_vec_eq_operand(rhs_arg, modified_locals)?;

        // Clone sorts to avoid borrow conflicts with field_select (consumes self).
        let lhs_sort = lhs.sort().clone();
        let rhs_sort = rhs.sort().clone();

        // Both must be datatype sorts with Vec fields (fld_data).
        let lhs_dt = lhs_sort.datatype_sort()?;
        let rhs_dt = rhs_sort.datatype_sort()?;

        let lhs_ctor = lhs_dt.constructors.first()?;
        let rhs_ctor = rhs_dt.constructors.first()?;

        // Confirm both have fld_data (Vec DT marker).
        let data_sort = lhs_ctor.field_sort(FLD_DATA)?;
        let _ = rhs_ctor.field_sort(FLD_DATA)?;

        let lhs_dt_name = lhs_sort.datatype_name()?;
        let rhs_dt_name = rhs_sort.datatype_name()?;

        // Extract len and data from both Vecs.
        let lhs_len = lhs.clone().field_select(lhs_dt_name, FLD_LEN, ptr_sort());
        let lhs_data = lhs.field_select(lhs_dt_name, FLD_DATA, data_sort.clone());
        let rhs_len = rhs.clone().field_select(rhs_dt_name, FLD_LEN, ptr_sort());
        let rhs_data = rhs.field_select(rhs_dt_name, FLD_DATA, data_sort);

        // Build: (len_a == len_b) && forall i: (i <u len_a) => select(data_a, i) == select(data_b, i)
        let len_eq = lhs_len.clone().eq(rhs_len);

        let idx_name = chc_fresh_name("vec_eq_idx");
        let idx = Expr::var(&idx_name, ptr_sort());
        let in_range = idx.clone().bvult(lhs_len);
        let elem_eq = lhs_data.select(idx.clone()).eq(rhs_data.select(idx));
        let forall_body = Expr::implies(in_range, elem_eq);
        let forall = Expr::forall(vec![(idx_name, ptr_sort())], forall_body);

        Some(len_eq.and(forall))
    }

    /// Resolve a VecEq operand through a 3-tier cascade.
    ///
    /// Part of #3348: PartialEq::eq receives `&Vec<T>` references, not direct Vec values.
    /// Tier 1 (`resolve_ref_or_const_referent`) handles the reference dereference.
    /// Tier 2 (`get_collection_arg`) handles projected/flattened collection locals.
    /// Tier 3 (`translate_operand_with_modified`) is the general fallback.
    fn resolve_vec_eq_operand(
        &mut self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Tier 1: resolve through references (handles &Vec<T> from PartialEq::eq).
        if let Some(expr) = self.resolve_ref_or_const_referent(operand, modified_locals) {
            if expr.sort().is_datatype() {
                return Some(expr);
            }
            // If we got a BV64 pointer, try to load the Vec from typed memory.
            if *expr.sort() == ptr_sort() {
                if let Some(loaded) = self.try_load_vec_from_ptr(&expr, operand) {
                    return Some(loaded);
                }
            }
        }
        // Tier 2: projected/flattened collection resolution.
        if let Some(expr) = self.get_collection_arg(operand, modified_locals) {
            if expr.sort().is_datatype() {
                return Some(expr);
            }
        }
        // Tier 3: general operand translation.
        self.translate_operand_with_modified(operand, modified_locals)
    }

    /// Try to load a Vec Datatype from a pointer via typed memory.
    ///
    /// Part of #3348: when resolve_ref_or_const_referent returns a BV64 pointer
    /// (the address of the Vec), we need to load the Vec value from typed memory.
    fn try_load_vec_from_ptr(&mut self, ptr: &Expr, operand: &Operand) -> Option<Expr> {
        use rustc_public::ty::{RigidTy, TyKind};

        let local_idx = match operand {
            Operand::Copy(p) | Operand::Move(p) => p.local,
            _ => return None,
        };
        let arg_ty = self.body.locals().get(local_idx)?.ty;
        // Peel &Vec<T> to get Vec<T>.
        let inner_ty = match arg_ty.kind() {
            TyKind::RigidTy(RigidTy::Ref(_, inner, _)) => inner,
            _ => return None,
        };
        self.load_from_memory_untyped(ptr.clone(), inner_ty)
    }

    /// Gets the tracked length variable for a collection local, if available.
    /// Part of #1814: Returns (len_var_name, current_len_expr) for collections with tracked length.
    /// Part of #1739: Resolves through ref_targets so reference locals (e.g., `&mut HashMap`)
    /// read the underlying collection's length variable, not a disconnected shadow copy.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn get_collection_len_var(
        &self,
        operand: &Operand,
        modified_locals: &HashSet<usize>,
    ) -> Option<(String, Expr)> {
        let local_idx = self.extract_local_index(operand)?;
        // Resolve through ref_targets to find the underlying collection's length
        // variable. For `&mut HashMap` operands, the direct local is the reference;
        // ref_targets maps it to the actual HashMap local whose length we track.
        let resolved_idx =
            self.ref_resolution.ref_targets.get(&local_idx).map_or(local_idx, |rt| rt.local);
        // Part of #3284: Track whether the len var was found via the resolved
        // collection local (primary) or via the reference local itself (fallback).
        // This distinction matters for the modified_locals check below.
        let resolved_has_len = self.collections.len_state.get_len_var(resolved_idx).is_some();
        let len_var_name = self
            .collections
            .len_state
            .get_len_var(resolved_idx)
            .or_else(|| self.collections.len_state.get_len_var(local_idx))?
            .clone();
        let len_out_name = crate::codegen_ay::names::out_name(&len_var_name);

        // Use output var if the *collection* was modified in this block, input var otherwise.
        // In CHC, each basic block is a separate Horn clause rule. The length
        // input comes from the predecessor relation, so cross-block modifications
        // (tracked by is_len_modified) must NOT influence which variable we read.
        // Only modified_locals (scoped to this block's terminator) matters here.
        // Part of #1739: Removing is_len_modified check fixes circular constraints
        // where insert/remove read len__out instead of len (input).
        //
        // Part of #3148: When ref_targets resolves local_idx → resolved_idx,
        // local_idx is a reference (`&mut HashMap`), not the collection itself.
        // The reference local being in modified_locals means only that the MIR block
        // created a `&mut` borrow (e.g., `_8 = &mut _1`), NOT that the collection's
        // length was modified. Only check the resolved collection local.
        //
        // Part of #3284: When the len var was found via the fallback path
        // (local_idx, not resolved_idx), the ghost var belongs to a reference
        // that points through a struct field projection (e.g., `_23 = &((*_22).0)`).
        // In this case, ghost propagation in the same block already set
        // `len_23__out = _4_fld1`, so the stub should read `len__out`.
        // This is safe because the fallback path only fires when resolved_idx
        // (the struct) has NO ghost vars — for simple `_8 = &mut _1` patterns,
        // resolved_idx IS the Vec local and has ghost vars (primary path).
        let collection_modified = modified_locals.contains(&resolved_idx)
            || (resolved_idx == local_idx && modified_locals.contains(&local_idx))
            || (!resolved_has_len && modified_locals.contains(&local_idx));
        let len_expr = if collection_modified {
            Expr::var(len_out_name.as_str(), ptr_sort())
        } else {
            Expr::var(&*len_var_name, ptr_sort())
        };

        Some((len_out_name, len_expr))
    }

    /// Extracts the local index from an operand, if it's a simple local or reference to local.
    /// Part of #1814: Used to look up collection length state variables.
    pub(in crate::codegen_ay::chc) fn extract_local_index(
        &self,
        operand: &Operand,
    ) -> Option<usize> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                if place.projection.is_empty() {
                    Some(place.local)
                } else {
                    // Check if it's a deref of a ref_target
                    let has_deref =
                        place.projection.iter().any(|p| matches!(p, ProjectionElem::Deref));
                    if has_deref {
                        // Try to resolve through ref_targets
                        self.ref_resolution.ref_targets.get(&place.local).map(|t| t.local)
                    } else {
                        Some(place.local)
                    }
                }
            }
            Operand::Constant(_) => None,
        }
    }

    /// Shared zero position literal for collection iterators.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn iter_position_zero() -> Expr {
        Expr::bitvec_const(0u64, POINTER_WIDTH)
    }

    /// Reuse tracked iterator length when present, otherwise allocate a symbolic length.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn tracked_len_or_fresh(
        &self,
        tracked_len: Option<Expr>,
        fresh_len_prefix: &str,
    ) -> Expr {
        tracked_len.unwrap_or_else(|| {
            // Part of #3447: Record that iterator length is unconstrained
            // (no tracked length from collection ghost state).
            self.record_aggregate_gap("collection_iter_len_unconstrained");
            let len_name = chc_fresh_name(fresh_len_prefix);
            declare_pending_var(len_name, ptr_sort())
        })
    }

    /// Allocate a symbolic iterator key array `Array<usize, K>`.
    #[must_use]
    pub(in crate::codegen_ay::chc) fn make_symbolic_iter_keys(
        &self,
        fresh_keys_prefix: &str,
        key_sort: Sort,
    ) -> (Expr, Sort) {
        // Part of #3447: iterator key array is fully unconstrained.
        self.record_aggregate_gap("collection_iter_keys_unconstrained");
        let keys_name = chc_fresh_name(fresh_keys_prefix);
        let keys_sort = Sort::array(ptr_sort(), key_sort);
        let keys = declare_pending_var(keys_name, keys_sort.clone());
        (keys, keys_sort)
    }

    /// Build a collection iterator datatype constructor expression.
    ///
    /// Part of #2304 (FE4): deduplicates Vec/HashMap/HashSet iterator construction.
    /// Part of #2917: declares the iterator sort (and nested sorts) so the CHC
    /// preamble includes `declare-datatypes` for sorts not in state variables.
    pub(in crate::codegen_ay::chc) fn make_collection_iter(
        &mut self,
        config: IterConstructConfig<'_>,
    ) -> Expr {
        let iter_sort = struct_sort(config.iter_sort_name, config.iter_fields);
        self.declare_datatype_sort_if_needed(&iter_sort);
        let ctor_name = names::resolve_ctor_name(&iter_sort, config.iter_sort_name);
        Expr::datatype_constructor(config.iter_sort_name, ctor_name, config.ctor_fields, iter_sort)
    }

    /// Emit a fail-closed sort-mismatch guard failure.
    ///
    /// Increments `self.diagnostics.iterator_unsound_skip`, logs an `error!`, and
    /// returns a `CollectionCallResult` that `apply_collection_result` converts
    /// into an `error()` rule.
    ///
    /// Part of #2304 (FE2): Extracted from 3 identical guard blocks
    /// (iterator-next skeleton, VecIntoIter construction, HashMapIntoIter construction).
    pub(in crate::codegen_ay::chc) fn unsound_sort_mismatch_failure(
        &self,
        context: &str,
        actual_sort: &Sort,
    ) -> CollectionCallResult {
        let count = self.diagnostics.iterator_unsound_skip.inc_get();
        error!(
            "UNSOUND: {context} has non-datatype sort {actual_sort:?} (hit #{count}) \
             - forcing verification failure"
        );
        CollectionCallResult::forced_failure()
    }

    /// Shared skeleton for collection iterator `next()` implementations.
    ///
    /// All three iterator types (HashMap, HashSet, Vec) share the same structure:
    /// 1. Get iterator arg → guard non-datatype sort → extract `(dt_name, ctor_name)`
    /// 2. Call `extract_element` closure for collection-specific field/element extraction
    /// 3. Bounds check (`pos < len`) → position increment → iterator reconstruction
    /// 4. Wrap element in `Option<T>` → return `CollectionCallResult`
    ///
    /// The closure receives the iterator expression and its `(dt_name, ctor_name)`
    /// and returns [`IterNextParts`] with the element, sort, and reconstruction fields
    /// split around the position slot (`fields_before_pos`, `fields_after_pos`).
    ///
    /// Part of #2304: Extracted from 3 identical iterator `next()` implementations.
    pub(in crate::codegen_ay::chc) fn translate_iter_next_skeleton(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        iter_type_name: &str,
        extract_element: impl FnOnce(
            &mut Self,
            &Expr, // iter expression
            &str,  // dt_name
        ) -> Option<IterNextParts>,
    ) -> Option<CollectionCallResult> {
        let iter_arg = args.first()?;
        let iter = self.get_collection_arg(iter_arg, modified_locals)?;

        // Guard: must be a datatype (iterator struct).
        if !iter.sort().is_datatype() {
            return Some(self.unsound_sort_mismatch_failure(iter_type_name, iter.sort()));
        }

        // Extract (dt_name, ctor_name) from datatype sort.
        // Clone Sort (O(1) Arc bump) so dt borrows from sort_ref, not iter.
        let sort_ref = iter.sort().clone();
        let fallback_ctor = crate::codegen_ay::names::cons_name(iter_type_name);
        let (dt_name, ctor_name): (&str, &str) = sort_ref
            .datatype_sort()
            .and_then(|dt| {
                let ctor = dt.constructors.first()?;
                Some((&*dt.name, &*ctor.name))
            })
            .unwrap_or((iter_type_name, &fallback_ctor));

        // Collection-specific element extraction.
        let parts = extract_element(self, &iter, dt_name)?;

        // Extract position from iterator (all iterator types have fld_pos).
        // Length is provided by the closure (HashMap/HashSet: fld_len on iter;
        // Vec: fld_len on the nested vec struct).
        let pos = iter.clone().field_select(dt_name, "fld_pos", ptr_sort());

        // Bounds check: pos < len.
        let len = parts.len;
        let pos_in_range = pos.clone().bvule(len.clone());
        let in_bounds = pos.clone().bvult(len.clone());

        // Wrap raw membership constraints with in_bounds guard.
        let constraints: Vec<Expr> = parts
            .constraints
            .into_iter()
            .map(|c| Expr::ite(in_bounds.clone(), c, Expr::bool_const(true)))
            .collect();

        // Increment position only when in_bounds.
        let one = Expr::bitvec_const(1u64, POINTER_WIDTH);
        let new_pos = Expr::ite(in_bounds.clone(), pos.clone().bvadd(one), pos);
        let new_pos_in_range = new_pos.clone().bvule(len);

        // Reconstruct iterator: [fields_before_pos..., new_pos, fields_after_pos...].
        let mut ctor_fields = parts.fields_before_pos;
        ctor_fields.push(new_pos);
        ctor_fields.extend(parts.fields_after_pos);

        let new_iter =
            Expr::datatype_constructor(dt_name, ctor_name, ctor_fields, iter.sort().clone());

        // Part of #3057: DT-free — pass raw element + is_some flag instead of
        // wrapping in Option Datatype. Consumers decompose via result_is_some
        // for flattened destinations, avoiding DT+BV theory combination in CHC
        // constraints. This eliminates ay#1766 triggers from iterator next() paths.
        let mut constraints = constraints;
        constraints.push(pos_in_range);
        constraints.push(new_pos_in_range);

        Some(CollectionCallResult {
            map_update: Some(new_iter),
            map_update_fields: None,
            result: Some(parts.element),
            result_is_some: Some(in_bounds),
            len_update: None,
            present_update: None,
            result_fields: parts.element_fields,
            constraints,
            force_error: false,
            aux_targets_dest: false,
        })
    }
}
