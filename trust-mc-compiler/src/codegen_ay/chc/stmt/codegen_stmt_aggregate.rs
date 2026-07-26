// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Aggregate construction for CHC statement encoding.
//! Split from codegen_stmt.rs (#2036); ADT handling lives in `codegen_stmt_aggregate_adt.rs`.
//! Closure and coroutine aggregates live in `codegen_stmt_aggregate_closure.rs`.

use std::borrow::Cow;
use std::collections::HashSet;

use crate::codegen_ay::names::{self, struct_sort};
use rustc_public::CrateDef;
use rustc_public::mir::{AggregateKind, Operand};
use rustc_public::ty::{RigidTy, TyKind};
use tracing::{debug, warn};

use ay_bindings::{Expr, Sort};
use trust_mc_core::chc::VarDecl;

use crate::codegen_ay::shared::ty_signedness_shallow;
use crate::codegen_ay::types::{POINTER_WIDTH, SignExtension, coerce_bitvec_width_safe, ptr_sort};

use super::codegen_ctx::globals::declare_pending_var;
use super::codegen_types::CodegenTypes;
use super::{ChcCtx, chc_fresh_name};

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Translates an Aggregate rvalue to a AY datatype constructor expression.
    ///
    /// Handles ADT construction (structs, enums) and tuple construction.
    /// Tuples are encoded as datatypes with fields fld_0, fld_1, etc.
    pub(in crate::codegen_ay::chc) fn translate_aggregate(
        &mut self,
        kind: &AggregateKind,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        match kind {
            AggregateKind::Adt(def, variant_idx, args, _user_ty_annot, _active_field) => {
                self.translate_adt_aggregate(*def, *variant_idx, args, operands, modified_locals)
            }
            AggregateKind::Tuple => self.translate_tuple_aggregate(operands, modified_locals),
            AggregateKind::Array(elem_ty) => {
                self.translate_array_aggregate(*elem_ty, operands, modified_locals)
            }
            AggregateKind::Closure(def, args) => {
                self.translate_closure_aggregate(*def, args, operands, modified_locals)
            }
            AggregateKind::Coroutine(def, args) => {
                self.translate_coroutine_aggregate(*def, args, operands, modified_locals)
            }
            AggregateKind::CoroutineClosure(_, _) => {
                // CoroutineClosure unsupported in upstream Kani too (kani#3783).
                warn!(
                    ?kind,
                    "CHC: coroutine closure aggregate unsupported — sound over-approximation"
                );
                self.record_sound_fallback_reason("coroutine_closure_unsupported");
                let name = chc_fresh_name("__coroutine_closure_nondet");
                Some(declare_pending_var(name, ptr_sort()))
            }
            AggregateKind::RawPtr(_, _) => {
                // RawPtr aggregates lower to (data_ptr, metadata).
                // For fat pointers (usize metadata = slice/str length), encode as
                // BV128 = len.concat(data_ptr) so that metadata survives array
                // store/load round-trips. PtrMetadata extracts bits [127:64].
                // For thin pointers (unit metadata), return just the data_ptr as BV64.
                if !operands.is_empty() {
                    if let Some(addr_expr) =
                        self.translate_operand_with_modified(&operands[0], modified_locals)
                    {
                        let data_ptr = match addr_expr.sort().inner() {
                            ay_bindings::SortInner::BitVec(bv) if bv.width == POINTER_WIDTH => {
                                addr_expr
                            }
                            ay_bindings::SortInner::BitVec(_) => coerce_bitvec_width_safe(
                                addr_expr,
                                POINTER_WIDTH,
                                SignExtension::ZeroExtend,
                            ),
                            ay_bindings::SortInner::Int => addr_expr.int2bv(POINTER_WIDTH),
                            ay_bindings::SortInner::Bool => {
                                // Unit metadata for thin pointers — ignore
                                Expr::bitvec_const(0u64, POINTER_WIDTH)
                            }
                            _ => coerce_bitvec_width_safe(
                                Expr::bitvec_const(0u64, POINTER_WIDTH),
                                POINTER_WIDTH,
                                SignExtension::ZeroExtend,
                            ),
                        };
                        // Check if metadata operand is usize (fat pointer).
                        // If so, construct BV128 = len.concat(data_ptr) to preserve
                        // metadata through array stores and pointer casts.
                        if operands.len() > 1 {
                            if let Ok(meta_ty) = operands[1].ty(self.body.locals()) {
                                let is_usize = matches!(
                                    meta_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Uint(rustc_public::ty::UintTy::Usize))
                                );
                                // DynMetadata<dyn Trait> carries the resolved
                                // vtable-id as a pointer-width value — preserve
                                // it in the fat-pointer high half exactly like a
                                // slice length, instead of dropping it (the
                                // rawptr_fat_metadata_dropped demotion made
                                // NonNull::from_raw_parts dyn reconstruction
                                // lose its vtable: AggregateRvalue/dyn_ptr FP).
                                let is_dyn_metadata = matches!(
                                    meta_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Adt(ref def, _))
                                        if def.trimmed_name() == "DynMetadata"
                                );
                                if is_usize || is_dyn_metadata {
                                    if let Some(len_expr) = self.translate_operand_with_modified(
                                        &operands[1],
                                        modified_locals,
                                    ) {
                                        let len_bv = coerce_bitvec_width_safe(
                                            len_expr,
                                            POINTER_WIDTH,
                                            SignExtension::ZeroExtend,
                                        );
                                        debug!(
                                            operand_count = operands.len(),
                                            "CHC: RawPtr aggregate → BV128 fat pointer (meta ++ data_ptr)"
                                        );
                                        return Some(len_bv.concat(data_ptr));
                                    }
                                }
                                let is_unit = matches!(
                                    meta_ty.kind(),
                                    TyKind::RigidTy(RigidTy::Tuple(ref tys)) if tys.is_empty()
                                );
                                if !is_unit && !is_usize && !is_dyn_metadata {
                                    debug!(
                                        ?meta_ty,
                                        "CHC: RawPtr fat pointer metadata dropped — sound over-approximation"
                                    );
                                    self.record_sound_fallback_reason(
                                        "rawptr_fat_metadata_dropped",
                                    );
                                }
                            }
                        }
                        debug!(
                            operand_count = operands.len(),
                            "CHC: RawPtr aggregate → translated data pointer operand"
                        );
                        Some(data_ptr)
                    } else {
                        warn!(
                            "CHC: RawPtr aggregate operand translation failed — sound over-approximation"
                        );
                        self.record_sound_fallback_reason("rawptr_operand_translation_failed");
                        let name = chc_fresh_name("__rawptr_agg_nondet");
                        Some(declare_pending_var(name, ptr_sort()))
                    }
                } else {
                    debug!("CHC: RawPtr aggregate with no operands → null pointer");
                    Some(Expr::bitvec_const(0u64, POINTER_WIDTH))
                }
            }
        }
    }

    /// Translates a tuple aggregate into a tuple datatype constructor.
    fn translate_tuple_aggregate(
        &mut self,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Handle unit tuple () as a special case
        if operands.is_empty() {
            // Unit type - return a boolean constant (unit is ZST)
            debug!("translate_tuple_aggregate: unit tuple ()");
            return Some(Expr::bool_const(true));
        }

        // Translate all operands to expressions
        let mut field_exprs = Vec::with_capacity(operands.len());
        for (idx, operand) in operands.iter().enumerate() {
            let Some(expr) = self.translate_operand_with_modified(operand, modified_locals) else {
                warn!(idx, ?operand, "translate_tuple_aggregate: failed to translate operand");
                // Part of #3369: Reclassified SOUND_APPROXIMATION → DEMOTED.
                // Returning None triggers caller's self-loop (output = input),
                // which is identity — only one value explored, not all.
                self.record_fallback();
                return None;
            };
            field_exprs.push(expr);
        }

        // Fix #1979: Unwrap single-element tuples to avoid sort mismatch.
        //
        // MIR uses 1-element tuples `(T,)` as wrappers (e.g., for pointer casts
        // through `<*const T>::is_null()` inlining). The CHC state variable has
        // the inner sort (e.g., BitVec(64)), not a datatype sort, so returning a
        // Tuple_bv64 constructor here causes a sort mismatch that silently drops
        // the constraint. Unwrapping directly returns the inner expression.
        if field_exprs.len() == 1 {
            debug!("translate_tuple_aggregate: unwrapping single-element tuple");
            return field_exprs.into_iter().next();
        }

        // Build field list for sort construction: (fld_0, sort0), (fld_1, sort1), ...
        let fields: Vec<(Cow<'static, str>, Sort)> = field_exprs
            .iter()
            .enumerate()
            .map(|(idx, expr)| (names::tuple_field_name(idx), expr.sort().clone()))
            .collect();

        // Generate tuple sort name: Tuple_bv32_bv32, Tuple_int_bool, etc.
        let tuple_sort_name = Self::tuple_sort_name(&fields);

        // Build the datatype sort
        let tuple_sort = struct_sort(&tuple_sort_name, fields);

        // Part of #2980: Ensure the tuple Datatype sort is declared
        // in the CHC preamble when constructed via MIR Aggregate.
        self.declare_datatype_sort_if_needed(&tuple_sort);

        // Get constructor name (defaults to <sort_name>_mk)
        let cons_name = crate::codegen_ay::names::resolve_ctor_name(&tuple_sort, &tuple_sort_name);

        debug!(
            tuple_sort_name = %tuple_sort_name,
            num_fields = field_exprs.len(),
            "translate_tuple_aggregate: constructed tuple"
        );

        Some(Expr::datatype_constructor(tuple_sort_name, cons_name, field_exprs, tuple_sort))
    }

    /// Translates an array aggregate construction to a AY expression.
    ///
    /// Part of #795: CHC array aggregate construction support.
    ///
    /// Converts `[v0, v1, v2, ...]` into nested SMT store operations:
    /// ```smt
    /// (store (store (store arr 0 v0) 1 v1) 2 v2)
    /// ```
    ///
    /// This matches the BMC array aggregate codegen pattern in `statement/aggregate.rs`.
    ///
    /// REQUIRES: elem_ty is the array element type from AggregateKind::Array
    /// REQUIRES: operands are the array elements to initialize
    /// ENSURES: On Some, returns an array expression with all elements stored
    /// ENSURES: Returns None if element type cannot be translated
    /// ENSURES: Records aggregate gaps and skips stores for untranslatable operands
    fn translate_array_aggregate(
        &mut self,
        elem_ty: rustc_public::ty::Ty,
        operands: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Option<Expr> {
        // Get element sort from the element type
        // Part of #1739: Flatten DT array elements to BV for PDR compatibility.
        let Some(elem_sort) = Self::translate_ty(elem_ty) else {
            self.record_aggregate_gap("array_aggregate_element_type_translation_failed");
            debug!(?elem_ty, "translate_array_aggregate: cannot infer element sort");
            return None;
        };
        let elem_sort = if elem_sort.is_datatype() {
            if let Some(width) =
                crate::codegen_ay::types::flattenable_datatype_sort_width(&elem_sort)
            {
                if width > 0 {
                    // coerce_store_value will flatten DT→BV using DT operations;
                    // ensure the Datatype sort is declared for the ITE expressions.
                    self.declare_datatype_sort_if_needed(&elem_sort);
                    Sort::bitvec(width)
                } else {
                    elem_sort
                }
            } else {
                elem_sort
            }
        } else {
            elem_sort
        };

        // Create array sort: Array<usize, elem_sort>
        let array_sort = Sort::array(ptr_sort(), elem_sort);

        // Create a fresh undefined array variable as the base
        // Part of #1888: Declare the variable in the CHC VC so Z3 doesn't complain
        let arr_name = chc_fresh_name("__chc_array");

        // Declare the array variable in the VC
        self.vc.add_var(VarDecl::new(&*arr_name, array_sort.clone()));

        let mut result = Expr::var(&arr_name, array_sort);

        // Store each element at its index
        // Part of #2244, #3034: coerce value sort to match array element sort
        let signed = ty_signedness_shallow(elem_ty).unwrap_or(false);
        for (i, op) in operands.iter().enumerate() {
            if let Some(val) = self.translate_operand_with_modified(op, modified_locals) {
                let idx = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                let val = Self::coerce_store_value(result.sort(), val, signed, &self.diagnostics);
                result = result.store(idx, val);
            } else {
                self.record_aggregate_gap("array_aggregate_operand_translation_failed");
                debug!(index = i, "translate_array_aggregate: cannot translate operand");
                // Continue with other elements - partial initialization is allowed
            }
        }

        debug!(
            num_elements = operands.len(),
            arr_name = %arr_name,
            "translate_array_aggregate: constructed array"
        );
        Some(result)
    }
}
