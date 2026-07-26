// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! SliceIntoVec — `vec![...]` macro expansion handling (#2967).
//!
//! Extracted from `codegen_call_vec.rs` for 500-LOC compliance (Part of #3199, D4).
//! Models the conversion of `Box<[T; N]>` to `Vec<T>` by reading elements from
//! type-indexed memory and constructing a populated Vec Datatype.

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use ay_bindings::{Expr, ExprValue, Sort};
use rustc_public::mir::{AggregateKind, Operand, ProjectionElem, Rvalue, StatementKind};
use rustc_public::ty::{GenericArgKind, RigidTy, TyKind};

use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};

use super::ChcCtx;
use super::chc_call_context::ChcCallContext;
use super::codegen_call_coerce::CallCoerce;
use super::codegen_call_vec_ops::ProjectedVecState;
use super::codegen_ctx::globals::declare_pending_var;
use super::codegen_ctx::types::{AdapterSourceData, CollectionProjectionKind};
use super::codegen_expr_heap::{obj_size_in, obj_size_out, obj_valid_in, obj_valid_out};
use super::codegen_rules::CodegenRules;
use super::codegen_types::CodegenTypes;
use tracing::{debug, warn};

/// Type information extracted from `into_vec`'s function signature.
struct IntoVecTypeInfo {
    elem_ty: rustc_public::ty::Ty,
    elem_sort: Sort,
    elem_byte_width: u64,
    array_len: usize,
    type_key: String,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// Handle `<[T]>::into_vec` / `alloc::slice::hack::into_vec` — the `vec![...]` expansion.
    ///
    /// Models the conversion of `Box<[T; N]>` to `Vec<T>` by:
    /// 1. Extracting element type, sort, byte width, and array length from generics
    /// 2. Reading N elements from the type-indexed memory array (`mem_T`)
    /// 3. Constructing a Vec Datatype with populated `fld_data`
    ///
    /// This bridges the gap between concrete heap writes (Box::new) and the abstract
    /// Vec data model, preventing the dual-model mismatch that causes spurious CTREX.
    pub(in crate::codegen_ay::chc) fn codegen_call_slice_into_vec(
        &mut self,
        func: &Operand,
        cx: &ChcCallContext<'_>,
    ) {
        let args = cx.args;
        let destination = cx.destination;
        let target = cx.target;
        let from_app = cx.from_app;
        let stmt_constraints = cx.stmt_constraints;
        let modified_locals = cx.modified_locals;
        let dest_local: usize = destination.local;
        let dest_vec_idx = self.try_state_idx_for_local(dest_local);
        if dest_vec_idx.is_none() {
            debug!(dest_local, "CHC: slice_into_vec dest not in state map — sound over-approx");
            self.record_sound_fallback_reason("state_idx_missing_slice_into_vec_dest");
        }
        debug!("slice_into_vec dest={}", dest_local);
        let mut extra_constraints: Vec<Expr> = Vec::new();
        let mut extra_dests: Vec<usize> = Vec::new();

        // Extract type information from the function's generic args or the arg type.
        let Some(info) = self.extract_into_vec_type_info(func, args) else {
            // SOUND AUDIT (#3369): &[] extra_dests — dest retains identity
            // (under-approx). Reclassified from record_sound_fallback.
            warn!("slice_into_vec: could not extract type info, falling back to unconstrained");
            self.record_fallback();
            let new_output_args = self.build_output_args(modified_locals, &[]);
            self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
            return;
        };

        let len_expr = Expr::bitvec_const(info.array_len as u64, POINTER_WIDTH);
        let cap_expr = len_expr.clone(); // cap == len for vec![...]

        // Get the source pointer from the Box argument (args[0]).
        let src_ptr =
            args.first().and_then(|arg| self.translate_operand_with_modified(arg, modified_locals));

        // Build the populated data array by reading from type-indexed memory.
        let data_expr = if let Some(ref ptr) = src_ptr {
            self.build_into_vec_data_array(&info, ptr.clone(), args, modified_locals)
        } else {
            None
        };
        let concrete_elems = Self::concrete_vec_literal_elems(data_expr.as_ref(), info.array_len)
            .or_else(|| self.concrete_vec_literal_elems_from_mir(&info, args, modified_locals));
        self.seed_slice_into_vec_backing_metadata(src_ptr.as_ref(), &info, &mut extra_constraints);
        // Set length tracking variable.
        if let Some(len_var_name) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(
                &len_var_name,
                len_expr.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
        }
        // Set capacity tracking variable.
        if let Some(cap_var_name) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            self.collection_cap_set(
                &cap_var_name,
                cap_expr.clone(),
                &mut CallAccumulator::new(&mut extra_constraints, &mut extra_dests),
            );
            Self::emit_cap_ge_len(cap_expr.clone(), len_expr.clone(), &mut extra_constraints);
        }

        // Construct Vec fields: flattened path or Datatype path.
        // Part of #3095: projection Vecs reuse constrain_projected_vec_fields_for_call.
        if let Some(dest_vec_idx) = dest_vec_idx {
            if self.collections.projection_locals.get(&dest_local).copied()
                == Some(CollectionProjectionKind::Vec)
            {
                let Some((ptr_name, ptr_sort)) = self
                    .state_var_mgr
                    .output_state_vars
                    .get(dest_vec_idx + vec_layout::IDX_PTR)
                    .cloned()
                else {
                    // Projected Vec ptr state var missing (Part of #3123).
                    // SOUND AUDIT (#3369): &[] extra_dests — dest retains identity.
                    // Reclassified from record_sound_fallback.
                    self.record_fallback();
                    let new_output_args = self.build_output_args(modified_locals, &[]);
                    self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
                    return;
                };
                let Some((data_name, data_sort)) = self
                    .state_var_mgr
                    .output_state_vars
                    .get(dest_vec_idx + vec_layout::IDX_DATA)
                    .cloned()
                else {
                    // Projected Vec data state var missing (Part of #3123).
                    // SOUND AUDIT (#3369): &[] extra_dests — dest retains identity.
                    // Reclassified from record_sound_fallback.
                    self.record_fallback();
                    let new_output_args = self.build_output_args(modified_locals, &[]);
                    self.emit_goto_rule(from_app, target, &new_output_args, stmt_constraints);
                    return;
                };
                // Part of #2267: pre-allocate instead of format!().
                // Part of #3447: record encoding gap when ptr/data resolution failed.
                if src_ptr.is_none() {
                    self.record_aggregate_gap("vec_into_iter_ptr_resolution_failed");
                }
                if data_expr.is_none() {
                    self.record_aggregate_gap("vec_into_iter_data_resolution_failed");
                }
                let ptr = src_ptr.unwrap_or_else(|| {
                    let mut name = String::with_capacity(ptr_name.len() + 14);
                    name.push_str(&ptr_name);
                    name.push_str("_into_vec_ptr");
                    declare_pending_var(name, ptr_sort)
                });
                let data = data_expr.clone().unwrap_or_else(|| {
                    let mut name = String::with_capacity(data_name.len() + 15);
                    name.push_str(&data_name);
                    name.push_str("_into_vec_data");
                    declare_pending_var(name, data_sort)
                });
                Self::emit_cap_ge_len(cap_expr.clone(), len_expr.clone(), &mut extra_constraints);
                if self.constrain_projected_vec_fields_for_call(
                    dest_local,
                    ProjectedVecState { ptr, len: len_expr, cap: cap_expr, data },
                    &mut extra_constraints,
                    &mut extra_dests,
                ) {
                    self.record_concrete_vec_literal_data(
                        dest_local,
                        data_expr.as_ref(),
                        concrete_elems.as_ref(),
                    );
                } else {
                    self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
                }
            } else if let Some((out_name, out_sort)) =
                self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
                && let Some(dt) = out_sort.datatype_sort()
                && dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_CAP))
            {
                let dt_name = out_sort.datatype_name().expect("has datatype_sort");
                // Part of #2267: pre-allocate instead of format!().
                let ptr = declare_pending_var(
                    {
                        let mut n = String::with_capacity(out_name.len() + 14);
                        n.push_str(&out_name);
                        n.push_str("_into_vec_ptr");
                        n
                    },
                    ptr_sort(),
                );
                // Part of #3447: record encoding gap when DT data resolution failed.
                if data_expr.is_none() {
                    self.record_aggregate_gap("vec_into_iter_dt_data_resolution_failed");
                }
                let data = data_expr.unwrap_or_else(|| {
                    let data_sort = dt
                        .constructors
                        .first()
                        .and_then(|c| {
                            c.fields
                                .iter()
                                .find(|f| f.name == vec_layout::FLD_DATA)
                                .map(|f| f.sort.clone())
                        })
                        .unwrap_or_else(|| Sort::array(ptr_sort(), ptr_sort()));
                    // Part of #2267: pre-allocate instead of format!().
                    let mut n = String::with_capacity(out_name.len() + 15);
                    n.push_str(&out_name);
                    n.push_str("_into_vec_data");
                    declare_pending_var(n, data_sort)
                });
                Self::emit_cap_ge_len(cap_expr.clone(), len_expr.clone(), &mut extra_constraints);
                extra_constraints.push(Self::build_vec_datatype_eq(
                    dt_name,
                    vec![ptr, len_expr, cap_expr, data],
                    &out_name,
                    &out_sort,
                ));
                extra_dests.push(dest_local);
            }
        } else {
            debug!(
                dest_local,
                "CHC: slice_into_vec result dest not in state map — preserving len/cap only"
            );
        }

        let new_output_args = self.build_output_args(modified_locals, &extra_dests);
        self.emit_goto_rule_extra(
            from_app,
            target,
            &new_output_args,
            stmt_constraints,
            extra_constraints,
        );
    }

    fn concrete_vec_literal_elems(data_expr: Option<&Expr>, array_len: usize) -> Option<Vec<Expr>> {
        if array_len == 0 || array_len > 16 {
            return None;
        }
        let elems = Self::try_extract_store_chain_elements(data_expr?, array_len)?;
        if elems.iter().all(Self::is_concrete_scalar_expr) { Some(elems) } else { None }
    }

    fn seed_slice_into_vec_backing_metadata(
        &mut self,
        src_ptr: Option<&Expr>,
        info: &IntoVecTypeInfo,
        extra_constraints: &mut Vec<Expr>,
    ) {
        let Some(src_ptr) = src_ptr else {
            return;
        };
        let Some((obj_id_expr, _offset)) = self.split_pointer(src_ptr) else {
            return;
        };
        let Some(obj_id) = Self::const_obj_id_u32(&obj_id_expr) else {
            return;
        };
        let Some(size_bytes) = (info.array_len as u64).checked_mul(info.elem_byte_width) else {
            self.record_sound_fallback_reason("slice_into_vec_backing_size_overflow");
            return;
        };
        let Ok(size_u32) = u32::try_from(size_bytes) else {
            self.record_sound_fallback_reason("slice_into_vec_backing_size_exceeds_bv32");
            return;
        };

        self.heap_state.record_heap_alloc_size(obj_id, size_u32);

        if self.heap_state.are_metadata_arrays_modified() {
            debug!(
                obj_id,
                size_bytes,
                "slice_into_vec: recorded known backing size without duplicate metadata store"
            );
            return;
        }

        let obj_valid_in = obj_valid_in();
        let obj_valid_out = obj_valid_out();
        let obj_size_in = obj_size_in();
        let obj_size_out = obj_size_out();
        let size_expr = Expr::bitvec_const(size_u32 as i128, 32);
        extra_constraints.push(
            obj_valid_out.eq(obj_valid_in.store(obj_id_expr.clone(), Expr::bool_const(true))),
        );
        extra_constraints.push(obj_size_out.eq(obj_size_in.store(obj_id_expr, size_expr)));
        self.mark_heap_metadata_modified();

        debug!(obj_id, size_bytes, "slice_into_vec: seeded backing allocation metadata");
    }

    fn concrete_vec_literal_elems_from_mir(
        &mut self,
        info: &IntoVecTypeInfo,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Vec<Expr>> {
        let operands = self.find_vec_literal_array_operands(info, args)?;
        let mut elems = Vec::with_capacity(operands.len());
        for operand in &operands {
            let expr = self.translate_operand_with_modified(operand, modified_locals)?;
            if !Self::is_concrete_scalar_expr(&expr) {
                return None;
            }
            elems.push(expr);
        }
        debug!(
            elem_count = elems.len(),
            "slice_into_vec: recovered concrete Vec literal elements from MIR"
        );
        Some(elems)
    }

    fn find_vec_literal_array_operands(
        &self,
        info: &IntoVecTypeInfo,
        args: &[Operand],
    ) -> Option<Vec<Operand>> {
        let src_alloc_id = self
            .trace_into_vec_pre_unsize_local(args)
            .and_then(|local| self.trace_deref_store_alloc_id(local))?;

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                let Rvalue::Aggregate(AggregateKind::Array(elem_ty), operands) = rhs else {
                    continue;
                };
                if operands.len() != info.array_len {
                    continue;
                }
                if self.type_key_for_body_ty(*elem_ty) != info.type_key {
                    continue;
                }
                if *elem_ty != info.elem_ty {
                    continue;
                }

                if lhs.projection.as_slice() == [ProjectionElem::Deref]
                    && self.trace_deref_store_alloc_id(lhs.local) == Some(src_alloc_id)
                {
                    return Some(operands.clone());
                }
            }
        }

        None
    }

    fn is_concrete_scalar_expr(expr: &Expr) -> bool {
        matches!(
            expr.value(),
            ExprValue::BoolConst(_)
                | ExprValue::BitVecConst { .. }
                | ExprValue::IntConst(_)
                | ExprValue::RealConst(_)
        )
    }

    fn record_concrete_vec_literal_data(
        &mut self,
        dest_local: usize,
        data_expr: Option<&Expr>,
        concrete_elems: Option<&Vec<Expr>>,
    ) {
        let (Some(data), Some(elems)) = (data_expr, concrete_elems) else {
            return;
        };
        self.collections.adapter_source_data.insert(
            dest_local,
            AdapterSourceData {
                data_arrays: vec![data.clone()],
                has_transform: false,
                closure_template: None,
                concrete_elems: Some(elems.clone()),
            },
        );
        debug!(
            dest_local,
            elem_count = elems.len(),
            "slice_into_vec: recorded concrete Vec literal elements"
        );
    }

    /// Extract element type and array length from `into_vec`'s function and arg types.
    fn extract_into_vec_type_info(
        &self,
        func: &Operand,
        args: &[Operand],
    ) -> Option<IntoVecTypeInfo> {
        // Strategy 1: Extract [T; N] from the argument's type (Box<[T; N], A>).
        if let Some(arg) = args.first() {
            if let Ok(arg_ty) = arg.ty(self.body.locals()) {
                if let Some(info) = self.extract_array_from_box_ty(arg_ty) {
                    return Some(info);
                }
            }
        }

        // Strategy 2: Extract from the function's generic args.
        let func_ty = func.ty(self.body.locals()).ok()?;
        let TyKind::RigidTy(RigidTy::FnDef(_, fn_args)) = func_ty.kind() else {
            return None;
        };
        for arg in &fn_args.0 {
            if let GenericArgKind::Type(ty) = arg {
                if let TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) = ty.kind() {
                    let array_len = const_len.eval_target_usize().ok()? as usize;
                    let elem_sort = Self::translate_ty(elem_ty)?;
                    let elem_byte_width = self.get_type_size(elem_ty)? as u64;
                    // Part of #3661: resolve generic params for consistent type keys.
                    let type_key = self.type_key_for_body_ty(elem_ty).into_owned();
                    return Some(IntoVecTypeInfo {
                        elem_ty,
                        elem_sort,
                        elem_byte_width,
                        array_len,
                        type_key,
                    });
                }
            }
        }

        // Strategy 3: Trace the arg backward through Cast(Unsize) to recover
        // the pre-unsizing Box<[T; N]> type. vec![] creates Box<[T; N]> then
        // unsizes to Box<[T]> before calling into_vec, losing the array length.
        // Part of #3095.
        self.trace_into_vec_arg_through_unsize(args)
    }

    /// Trace the `into_vec` argument backward through a Cast(Unsize) statement
    /// to recover the pre-unsizing `Box<[T; N]>` type with known array length.
    fn trace_into_vec_pre_unsize_local(&self, args: &[Operand]) -> Option<usize> {
        let arg = args.first()?;
        let arg_local = match arg {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                if lhs.local != arg_local {
                    continue;
                }
                if let Rvalue::Cast(_, Operand::Copy(src) | Operand::Move(src), _) = rhs
                    && src.projection.is_empty()
                {
                    return Some(src.local);
                }
            }
        }
        None
    }

    fn trace_into_vec_arg_through_unsize(&self, args: &[Operand]) -> Option<IntoVecTypeInfo> {
        let src_local = self.trace_into_vec_pre_unsize_local(args)?;
        let src_ty = self.body.locals()[src_local].ty;
        let info = self.extract_array_from_box_ty(src_ty)?;
        debug!(
            src_local,
            array_len = info.array_len,
            "into_vec: recovered array type through Cast(Unsize)"
        );
        Some(info)
    }

    /// Try to extract `[T; N]` from a `Box<[T; N], A>` type.
    fn extract_array_from_box_ty(&self, ty: rustc_public::ty::Ty) -> Option<IntoVecTypeInfo> {
        let TyKind::RigidTy(RigidTy::Adt(_, box_args)) = ty.kind() else {
            return None;
        };
        let inner_ty = box_args.0.iter().find_map(|arg| match arg {
            GenericArgKind::Type(t) => Some(*t),
            _ => None,
        })?;
        let TyKind::RigidTy(RigidTy::Array(elem_ty, const_len)) = inner_ty.kind() else {
            return None;
        };
        let array_len = const_len.eval_target_usize().ok()? as usize;
        let elem_sort = Self::translate_ty(elem_ty)?;
        let elem_byte_width = self.get_type_size(elem_ty)? as u64;
        // Part of #3661: resolve generic params for consistent type keys.
        let type_key = self.type_key_for_body_ty(elem_ty).into_owned();
        Some(IntoVecTypeInfo { elem_ty, elem_sort, elem_byte_width, array_len, type_key })
    }

    /// Build a populated Vec data array by reading N elements from type-indexed memory.
    ///
    /// Constructs: `store(store(...base..., 0, mem[ptr+0*sz]), 1, mem[ptr+1*sz])`
    /// where `base` is either the existing mem store chain or a fresh symbolic array.
    fn build_into_vec_data_array(
        &mut self,
        info: &IntoVecTypeInfo,
        src_ptr: Expr,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        if info.array_len == 0 {
            return None; // Empty array, no data to populate
        }
        if info.array_len > 64 {
            debug!(len = info.array_len, "into_vec: array too large, leaving data unconstrained");
            return None;
        }

        if let Some(data) =
            self.build_into_vec_data_array_from_direct_store(info, args, modified_locals)
        {
            return Some(data);
        }

        // Get the type-indexed memory array for this element type.
        //
        // CRITICAL (#3095): This runs during TERMINATOR dispatch, AFTER
        // encode_block_statements has already drained store chains. So
        // get_store_chain() returns None even if stores happened in this block.
        //
        // Fix: when the store chain is empty but the array was modified in this
        // block (is_array_modified), read from the OUTPUT variable (arr_out)
        // instead of the INPUT variable (arr_in). The drain already emitted
        // `arr_out = store(store(arr_in, addr, val), ...)` so the solver can
        // propagate concrete values through the output variable.
        let (arr_name, arr_out_name, declared_elem_sort, is_new) = self
            .heap_state
            .get_or_create_type_array(&info.type_key, info.elem_sort.clone(), &self.fn_name);
        // Part of #3184: Mark this type array as read (Vec data read loads values).
        // Part of #3436: Per-block tracking for error-path-aware pruning.
        self.heap_state.mark_type_array_read(&arr_name, self.current_encode_bb);
        let arr_sort = Sort::array(ptr_sort(), declared_elem_sort.clone());
        if is_new {
            self.push_late_state_var_pair(
                std::sync::Arc::clone(&arr_name),
                &arr_out_name,
                arr_sort.clone(),
            );
        }
        let is_modified = self.heap_state.is_array_modified(&info.type_key);
        let mirror_addr = self.heap_state.get_mirror_base_addr(&info.type_key).cloned();
        let (mem_arr, read_base) =
            if let Some(accumulated) = self.heap_state.get_live_store_chain(&info.type_key) {
                // Store chain still live (pre-drain) — use accumulated expr directly.
                // Part of #3552: use get_live_store_chain to avoid drained seeds routing
                // here and bypassing the mirror_addr logic in the is_modified branch.
                (accumulated.clone(), src_ptr)
            } else if is_modified {
                // Array was modified this block but chains are drained.
                // Use the OUTPUT variable which carries the stores.
                let arr = Expr::var(&*arr_out_name, arr_sort);
                // Part of #3095: Use the mirror's base address for reads if available.
                // The mirror stored elements at `mirror_base + i*size` and the drain
                // emitted `arr_out = store(arr_in, mirror_base, val0, ...)`. Reading
                // with the same base address ensures select-over-store simplifies
                // within the same CHC rule, even when MIR aliases the pointer through
                // different locals (e.g., _4 vs _19 for the same allocation).
                let base = mirror_addr.unwrap_or_else(|| src_ptr.clone());
                (arr, base)
            } else {
                // No modifications this block — use the INPUT variable.
                (Expr::var(&*arr_name, arr_sort), src_ptr)
            };

        // Build the Vec data array: Store chain that maps abstract index -> memory value.
        // Vec data array is Array<bv64, T> indexed by logical position (0, 1, 2, ...).
        let data_sort = Sort::array(ptr_sort(), declared_elem_sort);
        // Part of #2267: pre-allocate instead of format!().
        let base_data =
            declare_pending_var(["into_vec_", &info.type_key, "_base"].concat(), data_sort);

        let mut result = base_data;
        for i in 0..info.array_len {
            // Part of #3095: Address computation must match mirror_array_elements_to_flat_memory
            // exactly. The mirror uses bare `base_addr` for i=0 (no bvadd) and
            // `base_addr + byte_offset` for i>0. If we unconditionally use `bvadd(0)`
            // for i=0, the SMT select-over-store axiom won't fire because
            // `base_addr` ≠ `base_addr + 0` in the expression tree — the first element
            // becomes unconstrained.
            let heap_addr = if i == 0 {
                read_base.clone()
            } else {
                let byte_offset = (i as u64) * info.elem_byte_width;
                read_base.clone().bvadd(Expr::bitvec_const(byte_offset, POINTER_WIDTH))
            };
            let elem_val = mem_arr.clone().select(heap_addr);
            let idx = Expr::bitvec_const(i as u64, POINTER_WIDTH);
            // Part of #4212: coerce element to match Vec data array sort.
            // Memory arrays may use a different element sort (e.g., BV64
            // from get_type_size with padding) than Vec fld_data (BV40 from
            // flatten_dt_array_element without padding). Without coercion,
            // ay-bindings .store() panics on sort mismatch.
            let elem_val =
                Self::coerce_store_value(result.sort(), elem_val, false, &self.diagnostics);
            result = result.store(idx, elem_val);
        }
        Some(result)
    }

    fn build_into_vec_data_array_from_direct_store(
        &mut self,
        info: &IntoVecTypeInfo,
        args: &[Operand],
        modified_locals: &std::collections::HashSet<usize>,
    ) -> Option<Expr> {
        let src_local = self.trace_into_vec_pre_unsize_local(args)?;
        let src_alloc_id = self.trace_deref_store_alloc_id(src_local)?;

        for bb_data in &self.body.blocks {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(lhs, rhs) = &stmt.kind else {
                    continue;
                };
                if lhs.projection.as_slice() != [ProjectionElem::Deref] {
                    continue;
                }
                if self.trace_deref_store_alloc_id(lhs.local) != Some(src_alloc_id) {
                    continue;
                }
                let Rvalue::Aggregate(AggregateKind::Array(elem_ty), operands) = rhs else {
                    continue;
                };
                if operands.len() != info.array_len {
                    continue;
                }
                if self.type_key_for_body_ty(*elem_ty) != info.type_key {
                    continue;
                }

                let signed =
                    crate::codegen_ay::shared::ty_signedness_shallow(*elem_ty).unwrap_or(false);
                let data_sort = Sort::array(ptr_sort(), info.elem_sort.clone());
                let base_data = declare_pending_var(
                    ["into_vec_", &info.type_key, "_direct_base"].concat(),
                    data_sort,
                );

                let mut result = base_data;
                for (i, operand) in operands.iter().enumerate() {
                    let value = self.translate_operand_with_modified(operand, modified_locals)?;
                    let coerced =
                        Self::coerce_store_value(result.sort(), value, signed, &self.diagnostics);
                    let index = Expr::bitvec_const(i as u128, POINTER_WIDTH);
                    result = result.store(index, coerced);
                }

                return Some(result);
            }
        }

        None
    }
}
