// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Author: Andrew Yates <andrewyates.name@gmail.com>

//! Reference deref assignment and indexed write propagation.
//!
//! Extracted from `codegen_assign_ref.rs` — Part of #4206.

use super::{IntoOption, StatementCodegen};
use ay_bindings::Expr;
use rustc_public::mir::{Mutability, Operand, Place, ProjectionElem, Rvalue};
use rustc_public::ty::{RigidTy, TyKind};
use std::sync::Arc;
use tracing::{debug, trace};

use crate::codegen_ay::types::POINTER_WIDTH;
use crate::kani_middle::abi::LayoutOf;

impl<'a, 'tcx, 't> StatementCodegen<'a, 'tcx, 't> {
    /// Handle reference deref assignment: `*ref = value` for mutable references (#484).
    ///
    /// When LHS is `*r` where `r: &mut T`, assign to the pointee tracked in `ref_pointees`.
    /// Returns `true` if handled.
    pub(super) fn try_codegen_assign_ref_deref(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        let Some(ProjectionElem::Deref) = lhs.projection.first() else {
            return false;
        };
        // Part of #2267: construct Place directly instead of clone + clear.
        let ref_place = Place { local: lhs.local, projection: vec![] };
        let Some(ref_ty) = ref_place.ty(self.body.locals()).into_option() else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, _, Mutability::Mut)) = ref_ty.kind() else {
            return false;
        };
        // Only handle whole-struct assignment (no further projections after Deref)
        if lhs.projection.len() != 1 {
            return false;
        }

        let ref_base =
            crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), ref_place.local);

        let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() else {
            return false;
        };
        debug!(
            "codegen_assign: reference deref whole struct, ref={}, pointee={}",
            ref_base, pointee_base
        );
        let Some(rhs_expr) = self.codegen_rvalue(rhs) else {
            return false;
        };

        // A synthetic raw-deref alias (`X_deref`, `X_deref_field_N`) names bytes that
        // every raw-pointer read loads from `memory`. Updating only the alias left
        // those bytes stale: `let pb = &mut s.b; *pb = 9; assert!(s.b == 2)` on a
        // `Box` payload verified SUCCESSFUL. Mirror the store at the reference's
        // address as well.
        if pointee_base.contains("_deref") {
            self.mirror_ref_store_to_memory(&ref_base, &rhs_expr, lhs);
        }

        // Create new SSA version of the pointee
        let pointee_ssa = self.ssa_name_from_base(&pointee_base, true);
        let pointee_var = self.ctx.declare_var(&pointee_ssa, rhs_expr.sort().clone());

        // Assert SSA definition with ite semantics (#2081)
        self.assert_ssa_def(pointee_var.clone(), rhs_expr, &pointee_base);

        // Update environment
        let bindings_before = self.ref_pointees.generation();
        self.env_update(Arc::clone(&pointee_base), pointee_var.clone());
        // `pointee_base` now holds a value stored THROUGH the reference, so a
        // pointee binding recorded for it (or for a field of it) still names what
        // its PREVIOUS value pointed to: `let r = &mut p; *r = q; *p` read `p`'s
        // old target and certified the counterexample Genuine. Poison them, as a
        // direct reassignment does, so a later read through them fails closed.
        self.ref_pointees.poison_stale_since(&pointee_base, bindings_before);
        debug!("codegen_assign: reference deref assigned {} = rhs", pointee_ssa);

        // The stored value's flattened components travel with it.
        self.store_flattened_components_through_ref(&pointee_base, rhs);

        // A pointee whose address was taken was mirrored into byte memory
        // (#1246), and a read through a pointer made before this store (one
        // joined from two borrows, which has no tracked pointee) loads that
        // image. Keep it in step with the environment.
        if let Some(addr) = self.addr_symbols.get(pointee_base.as_ref()).cloned() {
            debug!("codegen_assign: reference deref store mirrored to memory image of {}", pointee_base);
            match ref_ty.kind() {
                TyKind::RigidTy(RigidTy::Ref(_, pointee, _)) => {
                    self.store_typed_value_to_memory(addr, pointee_var.clone(), pointee)
                }
                _ => self.ctx.store_memory_bytes(addr, pointee_var.clone()),
            }
        }

        // #1210: Propagate writes to array elements back to the array.
        // Part of #2267: .to_owned() is required here because try_propagate takes
        // &mut self while fn_name borrows from self.ctx.
        let fn_name = self.ctx.current_fn_name().to_owned();
        self.try_propagate_indexed_ref_write_to_array(&fn_name, &pointee_base, pointee_var.clone());

        // Part of #3041: Propagate writes to enum variant payloads back to the parent enum.
        self.try_propagate_deref_write_to_parent_datatype(&pointee_base, &pointee_var, lhs);

        true
    }

    /// `*r = v` through a `&mut T` with no tracked pointee binds only the
    /// `{r}_deref` environment entry, and the bytes at the address `r` holds
    /// kept their old value. A later read of that object through another
    /// pointer loads bytes: `static mut FOO: &mut i32 = &mut 12; static mut
    /// BAR: *mut i32 = FOO as *mut _;` then `*FOO = 13; assert_eq!(*BAR, 13)`
    /// read the initializer 12 and failed certified Genuine
    /// (kani/Static/anon_static.rs). Store the value's bytes at the pointer too,
    /// guarded by the path condition so an untaken branch leaves them unchanged.
    /// A value whose bytes cannot be laid out, or an address already holding a
    /// symbolic whole-value store, is left to the environment binding alone.
    pub(in crate::codegen_ay::statement) fn mirror_untracked_ref_deref_store(
        &mut self,
        lhs: &Place,
        value: &Expr,
    ) {
        if lhs.projection.len() != 1 || !matches!(lhs.projection[0], ProjectionElem::Deref) {
            return;
        }
        let ref_place = Place { local: lhs.local, projection: vec![] };
        let Some(ref_ty) = ref_place.ty(self.body.locals()).into_option() else {
            return;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, Mutability::Mut)) = ref_ty.kind() else {
            return;
        };
        let ref_base =
            crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), ref_place.local);
        if self.ref_pointees.contains_key(ref_base.as_str()) {
            return;
        }
        let Some(size) = crate::kani_middle::abi::LayoutOf::new(pointee_ty).size_of() else {
            return;
        };
        let Some(width) = value.sort().bitvec_width() else {
            return;
        };
        if size == 0 || width as usize != size * 8 {
            return;
        }
        let Some(addr) = self.codegen_place(&ref_place) else {
            return;
        };
        if addr.sort().bitvec_width() != Some(crate::codegen_ay::types::POINTER_WIDTH)
            || self.ctx.load_symbolic_memory_value(addr.clone()).is_some()
        {
            return;
        }
        let stored = match self.current_path_condition.clone() {
            Some(pc) => {
                let old = self.ctx.load_memory_bytes(addr.clone(), size as u32);
                Expr::ite(pc, value.clone(), old)
            }
            None => value.clone(),
        };
        debug!(%ref_base, size, "untracked &mut deref store mirrored to byte memory");
        self.ctx.store_memory_bytes(addr, stored);
    }

    /// After a whole-value store into `pointee_base`, give it the flattened
    /// components (`{base}.0` discriminant, `{base}_variant_V_field_N`,
    /// `{base}_field_N`) of the stored value.
    ///
    /// A flattened `Option` keeps its variant under `{base}.0`; the store wrote
    /// only the payload word, so after `let p = &mut o; *p = None;` the variant
    /// still read `Some` and `assert!(!(o == None))` was proved
    /// (tools/soundness-duals/negative/review_r18_mutate_then_compare.rs). A
    /// component the destination records and the stored value does not supply
    /// has no exact value: it is left unconstrained and the harness is marked.
    pub(in crate::codegen_ay::statement) fn store_flattened_components_through_ref(
        &mut self,
        pointee_base: &str,
        rhs: &Rvalue,
    ) {
        let source = match rhs {
            Rvalue::Use(Operand::Copy(src) | Operand::Move(src), ..) => Some(src),
            _ => None,
        };
        let source_components = source
            .map(|src| {
                let src_base = self.ssa_base_name(src);
                Self::collect_flattened_value_entries(&self.current_env, &src_base)
            })
            .unwrap_or_default();
        self.store_flattened_components(pointee_base, source_components);
    }

    /// Replace the flattened components recorded under `dest_base` with
    /// `components`; a destination component without a counterpart is left
    /// unconstrained and the harness is marked (see
    /// [`Self::store_flattened_components_through_ref`]).
    pub(in crate::codegen_ay::statement) fn store_flattened_components(
        &mut self,
        dest_base: &str,
        components: Vec<(String, Expr)>,
    ) {
        let existing = Self::collect_flattened_value_entries(&self.current_env, dest_base);
        let unmatched: Vec<(String, ay_bindings::Sort)> = existing
            .iter()
            .filter(|(suffix, _)| !components.iter().any(|(s, _)| s == suffix))
            .map(|(suffix, expr)| (suffix.clone(), expr.sort().clone()))
            .collect();
        self.apply_flattened_value_entries(dest_base, components);
        if unmatched.is_empty() {
            return;
        }
        self.ctx.unsupported_with_fallback(
            "store_flattened_components",
            format!("{dest_base}: components without a stored counterpart {unmatched:?}"),
        );
        for (suffix, sort) in unmatched {
            let key = format!("{dest_base}{suffix}");
            let name = self.ssa_name_from_base(&key, true);
            let fresh = self.ctx.declare_var(&name, sort);
            self.env_update(key, fresh);
        }
    }

    /// `(*r)[i] = v` and `(*r)[K] = v` through `r: &mut [T; N]` / `r: &mut [T]`:
    /// store into the referent's element array.
    ///
    /// Neither `try_codegen_assign_ref_deref` (whole-value stores only) nor
    /// `try_codegen_assign_array_index` (index on a local) covered this place,
    /// so the generic path bound a register named `r_deref_idx_by_i` and the
    /// referent never changed: `let r: &mut [u8; 2] = &mut lhs; r[0] = 9;
    /// assert!(lhs[0] == 1)` verified SUCCESSFUL, `assert!(r[0] == 1)` right
    /// after the store did too, the safe twins FAILED with a Genuine
    /// counterexample, and the same held through an unsized `&mut [u8]` and
    /// inside a `fn set(r: &mut [u8; 2])` callee (main 31793ccc3).
    ///
    /// The referent's value (an SMT array, or a slice/Vec datatype carrying its
    /// elements in `fld_data`) gets a new SSA version with `store(data, i, v)`,
    /// bindings nested under the referent are poisoned as a whole-value store
    /// poisons them, a parent datatype is rebuilt, and a materialized byte image
    /// of the referent is written at `addr + i * size_of::<T>()` on the current
    /// path. Any part that cannot be modelled exactly records
    /// `unsupported_with_fallback`, so no proof rests on a dropped store.
    /// Returns `true` when the store reached the referent.
    pub(super) fn try_codegen_assign_ref_deref_index(&mut self, lhs: &Place, rhs: &Rvalue) -> bool {
        if lhs.projection.len() < 2 || lhs.projection.first() != Some(&ProjectionElem::Deref) {
            return false;
        }
        // `(*r)[i][j] = v` (a nested element) is handled here too; `(*r)[i].x = v`
        // (fields after the element) stays with `try_codegen_datatype_field_assign`,
        // which selects the element and rebuilds it.
        let nested = &lhs.projection[2..];
        if !nested.is_empty()
            && !nested
                .iter()
                .any(|p| matches!(p, ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. }))
        {
            return false;
        }
        let ref_place = Place { local: lhs.local, projection: vec![] };
        let Some(ref_ty) = ref_place.ty(self.body.locals()).into_option() else {
            return false;
        };
        let TyKind::RigidTy(RigidTy::Ref(_, pointee_ty, Mutability::Mut)) = ref_ty.kind() else {
            return false;
        };
        let elem_ty = match pointee_ty.kind() {
            TyKind::RigidTy(RigidTy::Array(elem, _)) | TyKind::RigidTy(RigidTy::Slice(elem)) => {
                elem
            }
            _ => return false, // external enum: TyKind
        };
        let location = || format!("{lhs:?}");
        let idx_expr = match &lhs.projection[1] {
            ProjectionElem::Index(idx_local) => {
                let idx_name =
                    crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), *idx_local);
                let Some(idx) = self.env_lookup(&idx_name).cloned().or_else(|| {
                    let idx_ssa = self.ssa_name_from_base(&idx_name, false);
                    self.ctx.lookup_var(&idx_ssa).cloned()
                }) else {
                    self.ctx.unsupported_with_fallback(
                        "ref deref index store: index has no value",
                        location(),
                    );
                    return false;
                };
                idx
            }
            ProjectionElem::ConstantIndex { offset, from_end: false, .. } => {
                Expr::bitvec_const(*offset as u128, POINTER_WIDTH)
            }
            ProjectionElem::ConstantIndex { from_end: true, .. } => {
                self.ctx.unsupported_with_fallback(
                    "ref deref index store: index from the end",
                    location(),
                );
                return false;
            }
            _ => return false, // external enum: ProjectionElem
        };
        let ref_base =
            crate::codegen_ay::names::local_name(self.ctx.current_fn_name(), ref_place.local);
        let Some(pointee_base) = self.ref_pointees.get(ref_base.as_str()).cloned() else {
            self.ctx
                .unsupported_with_fallback("ref deref index store: untracked referent", location());
            return false;
        };
        // The referent's value as a read of `*r` sees it: the env, a derived
        // pointee recovered into the env, or the read path's own resolution (an
        // argument's pointee after a block-entry env rebuild).
        let pointee_val = self
            .env_lookup(pointee_base.as_ref())
            .cloned()
            .or_else(|| self.ensure_derived_pointee_in_env(pointee_base.as_ref()))
            .or_else(|| {
                self.codegen_place(&Place {
                    local: lhs.local,
                    projection: vec![ProjectionElem::Deref],
                })
            });
        let Some(pointee_val) = pointee_val else {
            self.ctx.unsupported_with_fallback(
                "ref deref index store: referent has no value",
                location(),
            );
            return false;
        };
        // The element storage: the referent itself, or the element array of a
        // slice/Vec datatype it is modelled as.
        let data_field = if pointee_val.sort().is_array() {
            None
        } else if let Some(dt) = pointee_val.sort().datatype_sort()
            && dt.constructors.len() == 1
            && let Some((field_idx, field)) = dt.constructors[0]
                .fields
                .iter()
                .enumerate()
                .find(|(_, f)| matches!(&*f.name, "fld_data" | "fld_buf") && f.sort.is_array())
        {
            Some((dt.name.to_string(), field_idx, field.name.to_string(), field.sort.clone()))
        } else {
            self.ctx.unsupported_with_fallback(
                "ref deref index store: referent is not an element array",
                location(),
            );
            return false;
        };
        let data_array = match &data_field {
            None => pointee_val.clone(),
            Some((dt_name, _, field_name, field_sort)) => {
                pointee_val.clone().field_select(dt_name, field_name, field_sort.clone())
            }
        };
        let Some(arr_sort) = data_array.sort().array_sort() else {
            return false;
        };
        let elem_sort = arr_sort.element_sort.clone();
        let index_width = arr_sort.index_sort.bitvec_width().unwrap_or(POINTER_WIDTH);
        let idx = match idx_expr.sort().bitvec_width() {
            Some(w) if w == index_width => idx_expr,
            Some(w) if w < index_width => idx_expr.zero_extend(index_width - w),
            Some(_) => idx_expr.extract(index_width - 1, 0),
            None => {
                self.ctx.unsupported_with_fallback(
                    "ref deref index store: non-bitvector index",
                    location(),
                );
                return false;
            }
        };
        let Some(rhs_expr) = self.codegen_rvalue(rhs) else {
            self.ctx.unsupported_with_fallback(
                "ref deref index store: value did not codegen",
                location(),
            );
            return false;
        };
        let signed = lhs
            .ty(self.body.locals())
            .into_option()
            .and_then(crate::codegen_ay::shared::ty_signedness_shallow)
            .unwrap_or(false);
        // The new element: the coerced value for `(*r)[i] = v`, or the old
        // element rebuilt from the leaf for `(*r)[i][j] = v`.
        let val = if nested.is_empty() {
            let val = crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
                data_array.sort(),
                &rhs_expr,
            )
            .or_else(|| {
                crate::codegen_ay::store_coercion::coerce_store_value_bmc(
                    data_array.sort(),
                    &rhs_expr,
                    signed,
                )
            })
            .unwrap_or(rhs_expr);
            if *val.sort() != elem_sort {
                self.ctx.unsupported_with_fallback(
                    "ref deref index store: element sort mismatch",
                    location(),
                );
                return false;
            }
            val
        } else {
            let elem = data_array.clone().select(idx.clone());
            let Some(new_elem) =
                self.update_projected_value(&elem, nested, &rhs_expr, lhs, signed)
            else {
                self.ctx.unsupported_with_fallback(
                    "ref deref index store: nested place not rebuilt",
                    location(),
                );
                return false;
            };
            new_elem
        };

        let new_data = data_array.store(idx.clone(), val.clone());
        let new_val = match &data_field {
            None => new_data,
            Some((_, field_idx, _, _)) => {
                let Some(rebuilt) = Self::datatype_field_update(
                    &pointee_val,
                    *field_idx,
                    None,
                    new_data,
                    lhs,
                    self.ctx,
                ) else {
                    self.ctx.unsupported_with_fallback(
                        "ref deref index store: element array not rebuilt",
                        location(),
                    );
                    return false;
                };
                rebuilt
            }
        };
        let pointee_ssa = self.ssa_name_from_base(&pointee_base, true);
        let pointee_var = self.ctx.declare_var(&pointee_ssa, new_val.sort().clone());
        self.assert_ssa_def(pointee_var.clone(), new_val, &pointee_base);
        let bindings_before = self.ref_pointees.generation();
        self.env_update(Arc::clone(&pointee_base), pointee_var.clone());
        self.ref_pointees.poison_stale_since(&pointee_base, bindings_before);
        self.repeat_array_values.remove(pointee_base.as_ref());
        if self.heap_pointees.contains_key(pointee_base.as_ref()) {
            self.heap_pointees.insert(Arc::clone(&pointee_base), pointee_var.clone());
        }
        debug!(
            "codegen_assign: reference deref index store {} = store(referent, idx, val)",
            pointee_ssa
        );
        self.try_propagate_deref_write_to_parent_datatype(&pointee_base, &pointee_var, lhs);

        // A materialized byte image of the referent (its address was taken) and
        // the bytes a raw-deref alias names must see the element too.
        let addr = self.addr_symbols.get(pointee_base.as_ref()).cloned();
        if addr.is_some() || pointee_base.contains("_deref") {
            let mirrored = addr.is_some_and(|addr| {
                self.mirror_ref_element_store_to_memory(addr, &idx, &val, elem_ty)
            });
            if !mirrored {
                self.ctx.unsupported_with_fallback("ref_deref_index_store_unmirrored", location());
            }
        }
        true
    }

    /// Write element `val` at `addr + idx * size_of(elem_ty)` on the current
    /// path. `false` when the element has no whole-byte bitvector image or the
    /// element size is unknown (the caller then fails closed).
    fn mirror_ref_element_store_to_memory(
        &mut self,
        addr: Expr,
        idx: &Expr,
        val: &Expr,
        elem_ty: rustc_public::ty::Ty,
    ) -> bool {
        if addr.sort().bitvec_width() != Some(POINTER_WIDTH) {
            return false;
        }
        let Some(elem_size) = LayoutOf::new(elem_ty).size_of() else {
            return false;
        };
        let bytes = if val.sort().is_bool() {
            Expr::ite(val.clone(), Expr::bitvec_const(1u64, 8), Expr::bitvec_const(0u64, 8))
        } else {
            val.clone()
        };
        let Some(width) = bytes.sort().bitvec_width().filter(|w| *w > 0 && w % 8 == 0) else {
            return false;
        };
        if width / 8 != elem_size as u32 {
            return false;
        }
        let idx = match idx.sort().bitvec_width() {
            Some(w) if w == POINTER_WIDTH => idx.clone(),
            Some(w) if w < POINTER_WIDTH => idx.clone().zero_extend(POINTER_WIDTH - w),
            Some(_) => idx.clone().extract(POINTER_WIDTH - 1, 0),
            None => return false,
        };
        let elem_addr = addr.bvadd(idx.bvmul(Expr::bitvec_const(elem_size as u128, POINTER_WIDTH)));
        self.store_memory_bytes_on_path(elem_addr, bytes, "ref_deref_index_store_unmirrored");
        true
    }

    /// Write `value` into byte memory at the address a `&mut` reference holds,
    /// under the current path condition. Anything that cannot be written exactly
    /// fails closed: the alias store above still stands, but raw reads of those
    /// bytes may be stale, so no verdict may rest on them.
    fn mirror_ref_store_to_memory(&mut self, ref_base: &str, value: &Expr, lhs: &Place) {
        let location = || format!("{lhs:?}");
        let Some(addr) = self.env_lookup(ref_base).cloned() else {
            self.ctx.unsupported_with_fallback("ref_deref_alias_store_unmirrored", location());
            return;
        };
        if addr.sort().bitvec_width() != Some(crate::codegen_ay::types::POINTER_WIDTH)
            || self.ctx.load_symbolic_memory_value(addr.clone()).is_some()
        {
            self.ctx.unsupported_with_fallback("ref_deref_alias_store_unmirrored", location());
            return;
        }
        let bytes = if value.sort().is_bool() {
            Expr::ite(value.clone(), Expr::bitvec_const(1u64, 8), Expr::bitvec_const(0u64, 8))
        } else {
            value.clone()
        };
        let Some(width) = bytes.sort().bitvec_width().filter(|w| *w > 0 && w % 8 == 0) else {
            self.ctx.unsupported_with_fallback("ref_deref_alias_store_unmirrored", location());
            return;
        };
        if self.memory_bytes_hold_symbolic_store(&addr, width / 8) {
            self.ctx.unsupported_with_fallback("ref_deref_alias_store_unmirrored", location());
            return;
        }
        trace!(ref_base, width, "ref deref store mirrored into byte memory");
        self.store_memory_bytes_on_path(addr, bytes, "ref_deref_alias_store_unmirrored");
    }

    /// Propagate indexed reference writes back to the parent array.
    ///
    /// When pointee is an indexed element (e.g., `fn::local_1_idx_by_3`),
    /// update the array itself using store operation so subsequent reads
    /// via `arr[i]` see the updated value (#1210).
    pub(in crate::codegen_ay::statement) fn try_propagate_indexed_ref_write_to_array(
        &mut self,
        fn_name: &str,
        pointee_base: &str,
        pointee_var: Expr,
    ) {
        // A name that records a projection is the walk's business
        // (`try_propagate_deref_write_to_parent_datatype`), which undoes the
        // projections RIGHT TO LEFT — the only order that is correct for a
        // chain such as `..._field_1_idx_by_L`. Doing it here as well would
        // store the same element twice, and doing it here INSTEAD would store
        // a field's value as if it were a whole element.
        if super::datatype_deref_write::last_derived_slot(pointee_base).is_some() {
            return;
        }
        let Some(idx_pos) = pointee_base.find("_idx_by_") else {
            // Part of #3392: fallback for stub-created pointees that don't use
            // the `_idx_by_` naming convention (e.g., `slice_index_pointee_N`).
            self.try_propagate_stub_indexed_ref_write(pointee_base, pointee_var);
            return;
        };
        let array_base = &pointee_base[..idx_pos];
        let Some(idx_local_str) = pointee_base[idx_pos + 8..].split('_').next() else {
            return;
        };
        let Ok(idx_local) = idx_local_str.parse::<usize>() else {
            return;
        };

        let Some(arr_expr) = self.env_lookup(array_base).cloned() else {
            return;
        };
        if !arr_expr.sort().is_array() {
            return;
        }

        let idx_base = crate::codegen_ay::names::local_name(fn_name, idx_local);
        let Some(idx_expr) = self.env_lookup(&idx_base).cloned() else {
            return;
        };

        // Part of #2894: Vec/String coercion via shared helper (was inline #1341).
        let store_val = if let Some(coerced) =
            crate::codegen_ay::store_coercion::coerce_vec_string_store_value(
                arr_expr.sort(),
                &pointee_var,
            ) {
            trace!("codegen_assign: coerced value for Vec/String indexed ref write");
            coerced
        } else {
            pointee_var
        };

        // Part of #2970: BMC sort coercion beyond Vec/String (BV width, Bool↔BV, etc.).
        // Part of #3034: derive signedness from array element MIR type.
        // Part of #2267: eliminate format! allocation — use chained strip_prefix.
        let signed = {
            array_base
                .strip_prefix(fn_name)
                .and_then(|s| s.strip_prefix("::local_"))
                .and_then(|idx_str| idx_str.parse::<usize>().ok())
                .and_then(|local_idx| {
                    let local_ty = self.body.locals()[local_idx].ty;
                    match local_ty.kind() {
                        TyKind::RigidTy(RigidTy::Array(elem_ty, _))
                        | TyKind::RigidTy(RigidTy::Slice(elem_ty)) => {
                            crate::codegen_ay::shared::ty_signedness_shallow(elem_ty)
                        }
                        _ => crate::codegen_ay::shared::ty_signedness_shallow(local_ty),
                    }
                })
                .unwrap_or(false)
        };
        let store_val = if let Some(coerced) =
            crate::codegen_ay::store_coercion::coerce_store_value_bmc(
                arr_expr.sort(),
                &store_val,
                signed,
            ) {
            debug!("codegen_assign: BMC-coerced value for indexed ref write (Part of #2970)");
            coerced
        } else {
            store_val
        };

        // Part of #2970: Last-resort fresh symbolic if sorts still mismatch.
        let store_val = if let Some(arr) = arr_expr.sort().array_sort() {
            if *store_val.sort() != arr.element_sort {
                let sym_name = crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                debug!(
                    array_base = %array_base,
                    store_sort = ?store_val.sort(),
                    elem_sort = ?arr.element_sort,
                    "codegen_assign: fresh symbolic for indexed ref write sort mismatch (Part of #2970)"
                );
                self.ctx.declare_var(&sym_name, arr.element_sort.clone())
            } else {
                store_val
            }
        } else {
            store_val
        };

        let new_arr = arr_expr.store(idx_expr, store_val);
        let new_arr_ssa = self.ssa_name_from_base(array_base, true);
        let new_arr_var = self.ctx.declare_var(&new_arr_ssa, new_arr.sort().clone());
        self.assert_ssa_def(new_arr_var.clone(), new_arr, array_base);
        self.env_update(array_base, new_arr_var);
        debug!("codegen_assign: propagated indexed ref write to array {}", new_arr_ssa);
    }

    /// Fallback propagation for stub-created indexed references. Part of #3392.
    ///
    /// When `try_propagate_indexed_ref_write_to_array` can't find `_idx_by_` in
    /// the pointee name, check `stub_indexed_refs` for a mapping from the stub
    /// path. Handles both bare arrays and Vec/datatype `fld_data` containers.
    fn try_propagate_stub_indexed_ref_write(&mut self, pointee_base: &str, pointee_var: Expr) {
        let Some((container_base, idx_expr)) = self.stub_indexed_refs.get(pointee_base).cloned()
        else {
            return;
        };
        let Some(container_expr) = self.env_lookup(&container_base).cloned() else {
            return;
        };

        if container_expr.sort().is_array() {
            // Case 1: bare array — store directly.
            let store_val = self.coerce_store_value_for_array(&container_expr, pointee_var);
            let new_arr = container_expr.store(idx_expr, store_val);
            let new_arr_ssa = self.ssa_name_from_base(&container_base, true);
            let new_arr_var = self.ctx.declare_var(&new_arr_ssa, new_arr.sort().clone());
            self.assert_ssa_def(new_arr_var.clone(), new_arr, &container_base);
            self.env_update(std::sync::Arc::clone(&container_base), new_arr_var);
            debug!(
                "codegen_assign: propagated stub indexed ref write to bare array {} (Part of #3392)",
                new_arr_ssa
            );
        } else if let Some(dt) = container_expr.sort().datatype_sort() {
            // Case 2: Vec/datatype with a backing array field. Vec/Slice use
            // "fld_data"; ArrayVec/inline buffers use "fld_buf" (the fld_-prefixed
            // Rust field name). Part of the PROVED-green ArrayVec store modelling.
            let dt_name = &*dt.name;
            let Some(cons) = dt.constructors.first() else {
                return;
            };
            let data_field_idx =
                cons.fields.iter().position(|f| matches!(&*f.name, "fld_data" | "fld_buf"));
            let Some(data_field_idx) = data_field_idx else {
                return;
            };
            let data_field_name = &*cons.fields[data_field_idx].name;
            let data_sort = cons.fields[data_field_idx].sort.clone();
            if !data_sort.is_array() {
                return;
            }
            let data_expr =
                container_expr.clone().field_select(dt_name, data_field_name, data_sort);
            let store_val = self.coerce_store_value_for_array(&data_expr, pointee_var);
            let new_data = data_expr.store(idx_expr, store_val);

            // Reconstruct the datatype with updated fld_data.
            let cons_name = &*cons.name;
            let mut args = Vec::with_capacity(cons.fields.len());
            for (idx, field) in cons.fields.iter().enumerate() {
                if idx == data_field_idx {
                    args.push(new_data.clone());
                } else {
                    args.push(container_expr.clone().field_select(
                        dt_name,
                        &*field.name,
                        field.sort.clone(),
                    ));
                }
            }
            let new_container =
                Expr::datatype_constructor(dt_name, cons_name, args, container_expr.sort().clone());
            let new_ssa = self.ssa_name_from_base(&container_base, true);
            let new_var = self.ctx.declare_var(&new_ssa, new_container.sort().clone());
            self.assert_ssa_def(new_var.clone(), new_container, &container_base);
            self.env_update(std::sync::Arc::clone(&container_base), new_var);
            debug!(
                "codegen_assign: propagated stub indexed ref write to datatype {} {} (Part of #3392)",
                data_field_name, new_ssa
            );
        }
    }

    /// Coerce a store value for array element sort compatibility. Part of #3392.
    pub(in crate::codegen_ay::statement) fn coerce_store_value_for_array(
        &mut self,
        arr_expr: &Expr,
        val: Expr,
    ) -> Expr {
        // Try Vec/String coercion first.
        if let Some(coerced) =
            crate::codegen_ay::store_coercion::coerce_vec_string_store_value(arr_expr.sort(), &val)
        {
            return coerced;
        }
        // BMC sort coercion (BV width, Bool↔BV, etc.).
        let coerced = crate::codegen_ay::store_coercion::coerce_store_value_bmc(
            arr_expr.sort(),
            &val,
            false, // default unsigned for stub path
        );
        let val = coerced.unwrap_or(val);
        // Last-resort fresh symbolic for sort mismatch.
        if let Some(arr) = arr_expr.sort().array_sort() {
            if *val.sort() != arr.element_sort {
                let sym_name = crate::codegen_ay::store_coercion::bmc_store_fallback_name();
                return self.ctx.declare_var(&sym_name, arr.element_sort.clone());
            }
        }
        val
    }
}
