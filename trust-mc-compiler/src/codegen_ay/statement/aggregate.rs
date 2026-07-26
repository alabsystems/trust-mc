// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>
//
//! Aggregate (tuple, closure, array) codegen for AY.
//!
//! This module handles construction of composite types in SMT encoding:
//! - Tuples: `(a, b, c)` → SMT datatypes with `fld_N` fields
//! - Closures: captured environment as SMT datatypes with `cap_N` fields
//! - Arrays: inline construction with element stores
//! - RawPtr: first operand or null
//! - Coroutine: state machine as struct with fld_state + cap_N fields (#1351)
//!
//! ADT (enum/struct) aggregate handling is in `aggregate_adt.rs` (#2246).

use std::borrow::Cow;

use crate::codegen_ay::coroutine_layout::build_coroutine_sort_info;
use ay_bindings::{Expr, Sort};
use rustc_public::mir::{AggregateKind, Operand};
use rustc_public::ty::{ClosureDef, CoroutineDef, GenericArgs};
use rustc_public_bridge::IndexedVal;
use tracing::{debug, trace};

use super::StatementCodegen;
use crate::codegen_ay::names::{self, struct_sort};
use crate::codegen_ay::types::{POINTER_WIDTH, ptr_sort};

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Codegen aggregate construction (tuples, arrays, ADTs, closures).
    ///
    /// Dispatches to specialized handlers based on aggregate kind:
    /// - Tuple → `codegen_tuple_aggregate`
    /// - Array → inline array construction with stores
    /// - ADT → `codegen_adt_aggregate` (in `aggregate_adt.rs`)
    /// - Closure → `codegen_closure_aggregate`
    /// - Coroutine → `codegen_coroutine_aggregate` (#1351)
    /// - CoroutineClosure → unsupported (kani#3783)
    /// - RawPtr → first operand or null
    ///
    /// Returns None if:
    /// - CoroutineClosure (unsupported, diagnostic recorded)
    /// - Tuple/Closure/ADT/Coroutine construction failure: see respective functions
    ///
    /// REQUIRES: operands are valid for the aggregate kind
    /// ENSURES: On Some, result is a composite expression (datatype/array)
    /// ENSURES: Other None returns may occur without diagnostic (delegated to inner functions)
    pub(super) fn codegen_aggregate(
        &mut self,
        kind: &AggregateKind,
        operands: &[Operand],
    ) -> Option<Expr> {
        match kind {
            AggregateKind::Tuple => self.codegen_tuple_aggregate(operands),
            AggregateKind::Array(elem_ty) => self.codegen_array_aggregate(*elem_ty, operands),
            AggregateKind::Adt(def, variant_idx, args, _user_ty_annot, _active_field) => {
                self.codegen_adt_aggregate(*def, *variant_idx, args.clone(), operands)
            }
            AggregateKind::Closure(def, args) => {
                self.codegen_closure_aggregate(*def, args.clone(), operands)
            }
            AggregateKind::Coroutine(def, args) => {
                self.codegen_coroutine_aggregate(*def, args.clone(), operands)
            }
            AggregateKind::CoroutineClosure(_, _) => {
                self.ctx.unsupported("Aggregate::CoroutineClosure", "coroutine_closure");
                None
            }
            AggregateKind::RawPtr(_, _) => {
                if !operands.is_empty() {
                    self.codegen_operand(&operands[0])
                } else {
                    Some(Expr::bitvec_const(0, POINTER_WIDTH))
                }
            }
        }
    }

    /// Codegen array aggregate construction with element stores.
    pub(super) fn codegen_array_aggregate(
        &mut self,
        elem_ty: rustc_public::ty::Ty,
        operands: &[Operand],
    ) -> Option<Expr> {
        let elem_sort = Self::infer_sort_from_ty(elem_ty).unwrap_or_else(|| Sort::bitvec(32));
        let array_sort = Sort::array(ptr_sort(), elem_sort.clone());
        let arr_name = self.ctx.fresh_name("array");
        let mut result = self.ctx.declare_var(&arr_name, array_sort);
        for (i, op) in operands.iter().enumerate() {
            if let Some(mut val) = self.codegen_operand(op) {
                trace!(
                    "Array aggregate elem {}: elem_sort={:?}, val_sort={:?}",
                    i,
                    elem_sort.datatype_name(),
                    val.sort()
                );
                // Part of #2894: Vec/String coercion via shared helper (was inline #1341, #1632).
                let arr_sort_for_coerce = Sort::array(ptr_sort(), elem_sort.clone());
                if let Some(coerced) =
                    crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
                        &arr_sort_for_coerce,
                        &val,
                    )
                {
                    trace!("Array aggregate: coerced BitVec to Vec/String for element {}", i);
                    val = coerced;
                }
                // Part of #2970: BMC sort coercion beyond Vec/String.
                // Part of #3034: derive signedness from MIR element type.
                let signed =
                    crate::codegen_ay::shared::ty_signedness_shallow(elem_ty).unwrap_or(false);
                if let Some(coerced) = crate::codegen_ay::store_coercion::coerce_store_value_bmc(
                    &arr_sort_for_coerce,
                    &val,
                    signed,
                ) {
                    debug!("Array aggregate: BMC-coerced element {} (Part of #2970)", i);
                    val = coerced;
                }
                let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                // Part of #2970: Last-resort fresh symbolic if sorts still mismatch.
                if *val.sort() != elem_sort {
                    let sym_name = crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                    debug!(
                        i,
                        store_sort = ?val.sort(),
                        elem_sort = ?elem_sort,
                        "Array aggregate: fresh symbolic for element sort mismatch (Part of #2970)"
                    );
                    val = self.ctx.declare_var(&sym_name, elem_sort.clone());
                }
                result = result.store(idx, val);
            }
        }
        Some(result)
    }

    /// Codegen tuple aggregate construction as SMT datatype.
    ///
    /// Generates an SMT datatype with:
    /// - Name: `Tuple_<sort1>_<sort2>_...` (e.g., `Tuple_bv32_bool`)
    /// - Constructor: `<datatype_name>_mk` (unique per datatype, #948)
    /// - Fields: `fld_0`, `fld_1`, ... with inferred sorts
    ///
    /// Empty tuples (unit `()`) produce a `Unit` datatype.
    ///
    /// REQUIRES: operands are valid operands from self.body
    /// ENSURES: On Some, result.sort().is_datatype()
    /// ENSURES: Empty operands produce Unit datatype
    fn codegen_tuple_aggregate(&mut self, operands: &[Operand]) -> Option<Expr> {
        if operands.is_empty() {
            let unit_sort = struct_sort("Unit", Vec::<(&str, Sort)>::new());
            // Constructor name is always "Unit_mk" per struct_type convention.
            return Some(Expr::datatype_constructor("Unit", "Unit_mk", vec![], unit_sort));
        }
        let mut field_exprs = Vec::with_capacity(operands.len());
        let mut fields: Vec<(Cow<'static, str>, Sort)> = Vec::with_capacity(operands.len());
        for (i, op) in operands.iter().enumerate() {
            let val = self.codegen_operand(op)?;
            fields.push((names::tuple_field_name(i), val.sort().clone()));
            field_exprs.push(val);
        }
        let name = Self::tuple_sort_name(&fields);
        let tuple_sort = struct_sort(&name, fields);
        let cons_name = names::resolve_ctor_name(&tuple_sort, &name);
        Some(Expr::datatype_constructor(name, cons_name, field_exprs, tuple_sort))
    }

    /// Codegen closure aggregate construction as SMT datatype.
    ///
    /// Closures in Rust MIR are represented as structs containing their captured
    /// environment. The operands are the captured values in memory layout order.
    ///
    /// Generates an SMT datatype with:
    /// Part of #1351: Coroutine aggregate — root state machine with direct-fields view.
    fn codegen_coroutine_aggregate(
        &mut self,
        def: CoroutineDef,
        args: GenericArgs,
        operands: &[Operand],
    ) -> Option<Expr> {
        let coro_name = names::coroutine_sort_name(def.0.to_index());
        let coroutine_ty =
            rustc_public::ty::Ty::from_rigid_kind(rustc_public::ty::RigidTy::Coroutine(def, args));
        let info = build_coroutine_sort_info(self.ctx.tcx, coroutine_ty, |field_ty| {
            Self::infer_sort_from_ty(field_ty).unwrap_or_else(ptr_sort)
        })?;

        debug!("codegen_coroutine_aggregate: {} with {} direct fields", coro_name, operands.len());

        // By-name operand mapping: view fields are offset-ordered while MIR
        // aggregate operands are indexed by MIR field index — pair them via
        // the index encoded in each field's name, never positionally.
        let operand_map = info.direct_fields.operand_map(operands.len())?;
        let mut direct_field_exprs = Vec::with_capacity(info.direct_fields.fields.len());
        for (field, mapped_idx) in info.direct_fields.fields.iter().zip(&operand_map) {
            let expr = match mapped_idx {
                None => match field.sort.bitvec_width() {
                    Some(width) => Expr::bitvec_const(0, width),
                    None => Expr::bool_const(false),
                },
                Some(mir_idx) => self.codegen_operand(operands.get(*mir_idx)?)?,
            };
            direct_field_exprs.push(expr);
        }

        let direct_sort_name = info.direct_fields.sort.datatype_name()?;
        let direct_cons_name =
            names::resolve_ctor_name(&info.direct_fields.sort, &direct_sort_name);
        let direct_expr = Expr::datatype_constructor(
            direct_sort_name,
            direct_cons_name,
            direct_field_exprs,
            info.direct_fields.sort.clone(),
        );

        let mut root_field_exprs = Vec::with_capacity(1 + info.variants.len());
        root_field_exprs.push(direct_expr);
        for variant in &info.variants {
            let fresh_name = self.ctx.fresh_name("coroutine_variant_view");
            root_field_exprs.push(self.ctx.declare_var(&fresh_name, variant.sort.clone()));
        }

        let cons_name = names::resolve_ctor_name(&info.root_sort, &coro_name);
        Some(Expr::datatype_constructor(coro_name, cons_name, root_field_exprs, info.root_sort))
    }

    /// - Name: `Closure_<id>` using the closure def id
    /// - Constructor: `<datatype_name>_mk` (unique per datatype, #948)
    /// - Fields: `cap_0`, `cap_1`, ... for captured values
    ///
    /// Empty closures (no captures) produce a unit-like datatype.
    ///
    /// REQUIRES: operands are valid operands from self.body
    /// ENSURES: On Some, result.sort().is_datatype()
    fn codegen_closure_aggregate(
        &mut self,
        def: ClosureDef,
        _args: GenericArgs,
        operands: &[Operand],
    ) -> Option<Expr> {
        let closure_id = def.0.to_index();
        let closure_name = names::closure_sort_name(closure_id);

        debug!("codegen_closure_aggregate: {} with {} captures", closure_name, operands.len());

        if operands.is_empty() {
            let sort = struct_sort(&closure_name, Vec::<(&str, Sort)>::new());
            let cons_name = names::resolve_ctor_name(&sort, &closure_name);
            return Some(Expr::datatype_constructor(closure_name, cons_name, vec![], sort));
        }

        let mut field_exprs = Vec::with_capacity(operands.len());
        let mut fields = Vec::with_capacity(operands.len());
        for (i, op) in operands.iter().enumerate() {
            let val = self.codegen_operand(op)?;
            fields.push((names::capture_field_name(i), val.sort().clone()));
            field_exprs.push(val);
        }

        let sort = struct_sort(&closure_name, fields);
        let cons_name = names::resolve_ctor_name(&sort, &closure_name);
        Some(Expr::datatype_constructor(closure_name, cons_name, field_exprs, sort))
    }
}
