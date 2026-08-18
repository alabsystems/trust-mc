// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Vec constructor and conversion operations: VecNew, VecWithCapacity,
//! VecFromElem (vec![elem; n]). VecFromSlice lives in `from_slice.rs`.

use std::collections::HashSet;

use ay_bindings::{Expr, Sort};
use rustc_public::mir::Operand;

use crate::codegen_ay::chc::call::call_accumulator::CallAccumulator;
use crate::codegen_ay::names::vec_layout;
use crate::codegen_ay::provenance::{Loc, Val};
use crate::codegen_ay::stubs::StubKind;
use crate::codegen_ay::types::{CtorFieldExt, POINTER_WIDTH, ptr_sort};

use super::super::ChcCtx;
use super::super::codegen_ctx::globals::declare_pending_var;
use super::super::codegen_ctx::types::CollectionProjectionKind;
use super::shared::{ProjectedVecState, coerce_array_element};

pub(in crate::codegen_ay::chc) struct VecOpNewContext<'a> {
    pub(in crate::codegen_ay::chc) stub: StubKind,
    pub(in crate::codegen_ay::chc) args: &'a [Operand],
    pub(in crate::codegen_ay::chc) modified_locals: &'a HashSet<usize>,
    pub(in crate::codegen_ay::chc) dest_local: usize,
    pub(in crate::codegen_ay::chc) dest_vec_idx: usize,
}

impl<'tcx, 'body> ChcCtx<'tcx, 'body> {
    /// The capacity operand of `Vec::new` / `Vec::with_capacity`.
    ///
    /// A [`Val`] by the callee's signature: `Vec::with_capacity(capacity: usize)`
    /// takes a COUNT, and the `Vec::new` lane is the literal `0`. Neither is an
    /// address, which is the fact the consumer below used to re-derive from the
    /// width of the term.
    fn vec_new_cap_expr(
        &mut self,
        stub: StubKind,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
    ) -> Val {
        Val::of_value(if stub == StubKind::VecWithCapacity && !args.is_empty() {
            self.translate_operand_with_modified(&args[0], modified_locals)
                .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH))
        } else {
            Expr::bitvec_const(0u64, POINTER_WIDTH)
        })
    }

    /// Dangling-pointer + provenance-invalidation constraints for the CHC
    /// `Vec::new` / `Vec::with_capacity` lane.
    ///
    /// Address-vs-value: this is the CHC twin of
    /// `statement/collections/vec.rs::add_vec_dangling_provenance_constraints`,
    /// which wave 1 converted; both lanes are live and only one had been done.
    /// The two payload parameters were adjacent bare `Expr`s — `cap` is the
    /// CAPACITY (a `usize` count) and `ptr` is the buffer's allocation base (an
    /// address) — so transposing them type-checked. They are now different types
    /// and the swap is a compile error.
    ///
    /// The retired guard was `cap_expr.sort().bitvec_width() == Some(POINTER_WIDTH)`,
    /// which reads as "is the capacity a pointer?". It is not. The real
    /// precondition is that `cap` is comparable with the `zero` constant it is
    /// about to be equated to, so the test is written against `zero`'s own width;
    /// `zero` is built at `POINTER_WIDTH`, so exactly the same expressions are
    /// accepted as before.
    fn emit_vec_dangling_provenance_constraints(
        &mut self,
        stub: StubKind,
        cap: &Val,
        ptr: &Loc,
        extra_constraints: &mut Vec<Expr>,
    ) {
        if !self.extra_pointer_checks || self.int_lift {
            return;
        }

        let zero = Expr::bitvec_const(0u64, POINTER_WIDTH);
        let (dangling_cond, conditional) = if stub == StubKind::VecNew {
            (Expr::bool_const(true), false)
        } else if cap.as_expr().sort().bitvec_width() == zero.sort().bitvec_width() {
            (cap.as_expr().clone().eq(zero.clone()), true)
        } else {
            return;
        };

        let ptr = ptr.as_expr();
        let ptr_nonzero = ptr.clone().bvugt(zero);
        if conditional {
            extra_constraints.push(Expr::ite(
                dangling_cond.clone(),
                ptr_nonzero,
                Expr::bool_const(true),
            ));
        } else {
            extra_constraints.push(ptr_nonzero);
        }

        if let Some((obj_id, _offset)) = self.split_pointer(ptr) {
            let current_valid = self.current_obj_valid_array();
            let invalidated = current_valid.clone().store(obj_id, Expr::bool_const(false));
            let next_valid = if conditional {
                Expr::ite(dangling_cond, invalidated, current_valid)
            } else {
                invalidated
            };
            extra_constraints.push(super::super::codegen_expr_heap::obj_valid_out().eq(next_valid));
            self.mark_heap_metadata_modified();
        }
    }

    /// VecNew / VecWithCapacity: dest = Vec(ptr, len=0, cap=arg|0, data).
    pub(in crate::codegen_ay::chc) fn vec_op_new(
        &mut self,
        cx: VecOpNewContext<'_>,
        acc: &mut CallAccumulator<'_>,
    ) {
        let VecOpNewContext { stub, args, modified_locals, dest_local, dest_vec_idx } = cx;
        let cap_expr = self.vec_new_cap_expr(stub, args, modified_locals);
        // Length tracking: set to 0 on the destination local
        if let Some(len_var_name) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(&len_var_name, Expr::bitvec_const(0u64, POINTER_WIDTH), acc);
        }
        // Capacity tracking: set to 0 (VecNew) or arg (VecWithCapacity). Part of #2877.
        if let Some(cap_var_name) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            self.collection_cap_set(&cap_var_name, cap_expr.as_expr().clone(), acc);
            // Part of #1037 V2: cap >= len background invariant on sidecar path.
            Self::emit_cap_ge_len(
                cap_expr.as_expr().clone(),
                Expr::bitvec_const(0u64, POINTER_WIDTH),
                acc.constraints,
            );
        }
        if self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let Some((ptr_name, ptr_sort)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_PTR)
                .cloned()
            else {
                return;
            };
            let Some((_len_name, _len_sort)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_LEN)
                .cloned()
            else {
                return;
            };
            let Some((_cap_name, _cap_sort)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_CAP)
                .cloned()
            else {
                return;
            };
            let Some((data_name, data_sort)) = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .cloned()
            else {
                return;
            };

            let zero_len = Expr::bitvec_const(0u64, POINTER_WIDTH);
            // P3-uninit (MECH-2): a CONSTANT nonzero capacity is a REAL heap
            // allocation — bind the buffer pointer to a fresh registered heap
            // object at offset 0 and record its byte size, so downstream
            // wrap / span / alloc-bound checks resolve against real
            // provenance. An unconstrained symbolic buffer pointer let the
            // solver pick a wrapping/OOB offset lane and produce spurious
            // Genuine-looking CTREX (kani Uninit/vec-read-init FP). The
            // symbolic `_init_ptr` fallback remains for symbolic/zero caps
            // (Vec::new / with_capacity(0) keep dangling semantics).
            let elem_byte_width = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .and_then(|(_, s)| s.array_sort())
                .and_then(|arr| Self::sort_byte_width(&arr.element_sort));
            let concrete_ptr = Self::const_usize_from_expr(cap_expr.as_expr())
                .filter(|cap| *cap > 0)
                .zip(elem_byte_width)
                .and_then(|(cap, elem)| u32::try_from(cap.checked_mul(elem)?).ok())
                .and_then(|bytes| {
                    let obj_id = self.heap_state.next_heap_alloc_id()?;
                    self.heap_state.record_heap_alloc_size(obj_id, bytes);
                    tracing::debug!(
                        obj_id,
                        bytes,
                        "CHC: Vec::with_capacity buffer bound to fresh heap object (P3-uninit)"
                    );
                    Some(Expr::bitvec_const((obj_id as u64) << 32, POINTER_WIDTH))
                });
            // Part of #2267: pre-allocate instead of format!().
            // Both lanes MINT this Vec's buffer base here: either the offset-0
            // base of the heap object just registered above, or a freshly
            // declared pointer-sorted variable standing for the (dangling)
            // allocation. An ADDRESS by construction — nothing downstream has to
            // re-derive it.
            let ptr = Loc::of_address(concrete_ptr.unwrap_or_else(|| {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(ptr_name.len() + 10);
                        n.push_str(&ptr_name);
                        n.push_str("_init_ptr");
                        n
                    },
                    ptr_sort,
                )
            }));
            // Part of #4287: initialize `data` as a concrete const_array rather
            // than a fresh symbolic. The sidecar-length store in VecPush (at
            // old_len=0) must agree with the Index::index read of v[0]. A fresh
            // symbolic data array lets the solver pick arbitrary values at
            // every index, so `data.select(0)` after `store(0, val)` is still
            // equal to `val` by Array theory — but the projected fld1 vs
            // sidecar len_var mismatch at Vec::new() leaves
            // `old_data[sidecar_old_len=0]` and the reader's `data.select(0)`
            // only consistent when the initial data is deterministic. const_array
            // with a fresh default element mirrors vec_op_from_elem.
            let data = if let Some(arr) = data_sort.array_sort() {
                let elem_sort = arr.element_sort.clone();
                let default_elem = declare_pending_var(
                    {
                        let mut n = String::with_capacity(data_name.len() + 11);
                        n.push_str(&data_name);
                        n.push_str("_init_elem");
                        n
                    },
                    elem_sort,
                );
                Expr::const_array(crate::codegen_ay::types::ptr_sort(), default_elem)
            } else {
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(data_name.len() + 11);
                        n.push_str(&data_name);
                        n.push_str("_init_data");
                        n
                    },
                    data_sort,
                )
            };
            self.emit_vec_dangling_provenance_constraints(stub, &cap_expr, &ptr, acc.constraints);
            // Part of #1037 V2: cap >= len background invariant.
            Self::emit_cap_ge_len(cap_expr.as_expr().clone(), zero_len.clone(), acc.constraints);
            if !self.constrain_projected_vec_fields_for_call(
                dest_local,
                ProjectedVecState {
                    ptr: ptr.into_expr(),
                    len: zero_len,
                    cap: cap_expr.into_expr(),
                    data,
                },
                acc.constraints,
                acc.dests,
            ) {
                self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
            }
            return;
        }
        // Construct Vec Datatype with proper fld_cap.
        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
            && let Some(dt) = out_sort.datatype_sort()
            && dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_CAP))
        {
            // Borrow &str directly — avoids intermediate String allocation. Part of #2267.
            let dt_name = out_sort.datatype_name().expect("has datatype_sort");
            let zero_len = Expr::bitvec_const(0u64, POINTER_WIDTH);
            let mut ptr_name = String::with_capacity(out_name.len() + 9);
            ptr_name.push_str(&out_name);
            ptr_name.push_str("_init_ptr");
            // Minted here, same as the projected lane above: an ADDRESS.
            let ptr = Loc::of_address(declare_pending_var(ptr_name, ptr_sort()));
            let data_sort = dt
                .constructors
                .first()
                .and_then(|c| c.field_sort(vec_layout::FLD_DATA))
                .unwrap_or_else(|| Sort::array(ptr_sort(), ptr_sort()));
            let mut data_name = String::with_capacity(out_name.len() + 10);
            data_name.push_str(&out_name);
            data_name.push_str("_init_data");
            let data = declare_pending_var(data_name, data_sort);
            self.emit_vec_dangling_provenance_constraints(stub, &cap_expr, &ptr, acc.constraints);
            // Part of #1037 V2: cap >= len background invariant.
            Self::emit_cap_ge_len(cap_expr.as_expr().clone(), zero_len.clone(), acc.constraints);
            acc.constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr.into_expr(), zero_len, cap_expr.into_expr(), data],
                &out_name,
                &out_sort,
            ));
            acc.dests.push(dest_local);
        }
    }

    /// VecFromElem: `vec![elem; n]` → Vec with data = const_array(elem), len = n, cap = n.
    /// Part of #3348: models alloc::vec::from_elem(elem, n) as a populated Vec.
    pub(in crate::codegen_ay::chc) fn vec_op_from_elem(
        &mut self,
        args: &[Operand],
        modified_locals: &HashSet<usize>,
        dest_local: usize,
        dest_vec_idx: usize,
        acc: &mut CallAccumulator<'_>,
    ) {
        // args[0] = elem value, args[1] = count (usize)
        let elem_expr =
            args.first().and_then(|a| self.translate_operand_with_modified(a, modified_locals));
        let count_expr = args
            .get(1)
            .and_then(|a| self.translate_operand_with_modified(a, modified_locals))
            .unwrap_or_else(|| Expr::bitvec_const(0u64, POINTER_WIDTH));

        // Set sidecar len and cap to count
        if let Some(len_var) = self.collections.len_state.get_len_var(dest_local).cloned() {
            self.collection_len_set(&len_var, count_expr.clone(), acc);
        }
        if let Some(cap_var) = self.collections.len_state.get_cap_var(dest_local).cloned() {
            self.collection_cap_set(&cap_var, count_expr.clone(), acc);
            Self::emit_cap_ge_len(count_expr.clone(), count_expr.clone(), acc.constraints);
        }

        // Build data array: const_array where every index maps to elem_expr.
        // For projected path
        if self.collections.projection_locals.get(&dest_local).copied()
            == Some(CollectionProjectionKind::Vec)
        {
            let ptr = declare_pending_var(
                {
                    use std::fmt::Write;
                    let mut n = String::with_capacity(24);
                    n.push_str("from_elem_");
                    let _ = write!(n, "{dest_local}");
                    n.push_str("_ptr");
                    n
                },
                ptr_sort(),
            );
            let data_sort = self
                .state_var_mgr
                .output_state_vars
                .get(dest_vec_idx + vec_layout::IDX_DATA)
                .map(|(_, s)| s.clone())
                .unwrap_or_else(|| Sort::array(ptr_sort(), ptr_sort()));
            let data = if let Some(ref elem) = elem_expr {
                // Part of #3496 Bug D: coerce element to match declared data array
                // element sort. translate_operand may produce a different sort than
                // translate_ty used at declaration (e.g., Bool vs BV8 for Rust bool).
                let coerced_elem = coerce_array_element(elem.clone(), &data_sort);
                Expr::const_array(ptr_sort(), coerced_elem)
            } else {
                // Part of #3447: element translation failed — data array unconstrained.
                self.record_aggregate_gap("vec_from_elem_data_unconstrained");
                declare_pending_var(
                    {
                        use std::fmt::Write;
                        let mut n = String::with_capacity(24);
                        n.push_str("from_elem_");
                        let _ = write!(n, "{dest_local}");
                        n.push_str("_data");
                        n
                    },
                    data_sort,
                )
            };
            if !self.constrain_projected_vec_fields_for_call(
                dest_local,
                ProjectedVecState { ptr, len: count_expr.clone(), cap: count_expr, data },
                acc.constraints,
                acc.dests,
            ) {
                self.record_sound_fallback_reason("vec_field_constraint_not_emitted");
            }
            return;
        }
        // Datatype path
        if let Some((out_name, out_sort)) =
            self.state_var_mgr.output_state_vars.get(dest_vec_idx).cloned()
            && let Some(dt) = out_sort.datatype_sort()
            && dt.constructors.first().is_some_and(|c| c.has_field(vec_layout::FLD_CAP))
        {
            let dt_name = out_sort.datatype_name().expect("has datatype_sort");
            let ptr = declare_pending_var(
                {
                    let mut n = String::with_capacity(out_name.len() + 7);
                    n.push_str(&out_name);
                    n.push_str("_fe_ptr");
                    n
                },
                ptr_sort(),
            );
            let data_sort = dt
                .constructors
                .first()
                .and_then(|c| c.field_sort(vec_layout::FLD_DATA))
                .unwrap_or_else(|| Sort::array(ptr_sort(), ptr_sort()));
            let data = if let Some(ref elem) = elem_expr {
                // Part of #3496 Bug D: coerce element sort to match declared data sort.
                let coerced_elem = coerce_array_element(elem.clone(), &data_sort);
                Expr::const_array(ptr_sort(), coerced_elem)
            } else {
                // Part of #3447: element translation failed — DT data array unconstrained.
                self.record_aggregate_gap("vec_from_elem_dt_data_unconstrained");
                declare_pending_var(
                    {
                        let mut n = String::with_capacity(out_name.len() + 8);
                        n.push_str(&out_name);
                        n.push_str("_fe_data");
                        n
                    },
                    data_sort,
                )
            };
            acc.constraints.push(Self::build_vec_datatype_eq(
                dt_name,
                vec![ptr, count_expr.clone(), count_expr, data],
                &out_name,
                &out_sort,
            ));
            acc.dests.push(dest_local);
        }
    }
}
